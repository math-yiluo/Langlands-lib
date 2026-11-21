import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartFiniteTypeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartRepresentabilityReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertClassifying
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeProof

/-! # Finite type of frame charts from the locally closed Hilbert locus -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry

/-- The fixed-polynomial ambient family produces a universal frame datum on a base
locally of finite type and quasi-compact over `Spec ℤ[1/n]`. -/
theorem exists_isUniversalFrameDatum_finiteType
    (HL : FrameHilbertLocusStatement) (HP : CubicBundlePolarizationDeterminationStatement.{0})
    (Hiso : FrameLocusIsoInvarianceStatement.{0}) (HE : FrameEmbeddingExistenceStatement.{0})
    (HU : FrameEmbeddingUniquenessStatement.{0})
    (P : Prerequisites.{0}) (g d n : ℕ) (hd : 0 < d) (hn : 3 ≤ n)
    (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n) :
    ∃ (X : LevelBase n) (U : Datum P X.obj g d n),
      IsUniversalFrameDatum ρ X U ∧ LocallyOfFiniteType X.toLocalizationSpec ∧
        QuasiCompact X.toLocalizationSpec := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨S⟩ := nonempty_cubicFrameClassifyingFamily.{0} g d n (cubicProjectiveDimension g d)
  have := S.noetherian
  obtain ⟨X, j, hj, ⟨U, ψU, hUframe, hψU, hUreal⟩, hfac⟩ :=
    HL P g d n hd hn ρ S.base S.ideal S.points S.flat S.locallyOfFinitePresentation
  have : Mono j := inferInstance
  have hft : LocallyOfFiniteType X.toLocalizationSpec := by
    let a := specULiftZIsTerminal.from (Spec (CommRingCat.of (Localization.Away (n : ℤ))))
    have := S.locallyOfFiniteType
    have : LocallyOfFiniteType (X.toLocalizationSpec ≫ a) := by
      rw [specULiftZIsTerminal.hom_ext (X.toLocalizationSpec ≫ a)
        (j ≫ specULiftZIsTerminal.from S.base)]
      infer_instance
    exact locallyOfFiniteType_of_comp X.toLocalizationSpec a
  have : TopologicalSpace.NoetherianSpace X.obj := j.isEmbedding.isInducing.noetherianSpace
  have hqc : QuasiCompact X.toLocalizationSpec := inferInstance
  have hUf : ∀ (T : LevelBase n) (f : T ⟶ X), (U.pullback f.hom).frameLocus ρ = ⊤ := by
    intro T f
    rw [frameLocusBaseChange P X.obj T.obj g d n hd U f.hom ρ, hUframe]
    rfl
  refine ⟨X, U, ⟨?_, ?_, ?_⟩, hft, hqc⟩
  · intro T f f' ⟨e⟩
    have hψ₁ := hψU.pullback (f := f.hom)
    have hψ₂ := hψU.pullback (f := f'.hom)
    have hr₁ := hUreal.pullback (f := f.hom) hψU
    have hr₂ := hUreal.pullback (f := f'.hom) hψU
    obtain ⟨hI, hσ⟩ := Datum.Realizes.eq_of_polarizedIso HU e (hUf T f) hψ₁ hψ₂ hr₁ hr₂
    obtain ⟨t, -, ht⟩ := S.classifies (U.pullback f.hom) ρ _ hψ₁
    have h₁ : f.hom ≫ j = t := ht _ ⟨by
      rw [RelativeProjectiveSpace.map_comp, Scheme.IdealSheafData.comap_comp]
      exact hr₁.1.symm,
      fun r => by simpa only [Category.assoc] using (hr₁.2 r).symm⟩
    have h₂ : f'.hom ≫ j = t := ht _ ⟨by
      rw [RelativeProjectiveSpace.map_comp, Scheme.IdealSheafData.comap_comp, ← hI]
      exact hr₁.1.symm,
      fun r => by
        rw [Category.assoc, ← congrFun hσ r]
        exact (hr₁.2 r).symm⟩
    apply ObjectProperty.hom_ext
    exact (cancel_mono j).mp (h₁.trans h₂.symm)
  · intro T b hb
    obtain ⟨ψ, hψ⟩ := HE P T.obj g d n hd b ρ hb
    obtain ⟨t, ⟨htI, htσ⟩, -⟩ := S.classifies b ρ ψ hψ
    have hreal : b.Realizes ψ (S.ideal.comap (RelativeProjectiveSpace.map _ t))
        (fun r => t ≫ S.points r) := ⟨htI.symm, fun r => (htσ r).symm⟩
    obtain ⟨t', ht'⟩ := hfac T t b ψ hb hψ hreal
    refine ⟨LevelBase.homMk t', ?_⟩
    have hr := hUreal.pullback (f := t') hψU
    apply Datum.nonempty_polarizedIso_of_realizes HP hψ (hψU.pullback (f := t')) hreal
    refine ⟨?_, fun r => ?_⟩
    · rw [hr.1, ← Scheme.IdealSheafData.comap_comp, ← RelativeProjectiveSpace.map_comp, ht']
    · rw [hr.2 r, ← ht']
      simp only [Category.assoc]
  · intro T f b ⟨e⟩
    rw [Hiso P T.obj g d n _ b (U.pullback f.hom) ρ ⟨e⟩]
    exact hUf T f

set_option linter.defProp false in
/-- The locally closed frame Hilbert locus and the frame-embedding inputs imply
`FrameChartFiniteTypeStatement`. The resulting chart theorem holds for all `n ≥ 3`. -/
def frameChartFiniteType_of_frameHilbertLocus
    (HL : FrameHilbertLocusStatement) (HP : CubicBundlePolarizationDeterminationStatement.{0})
    (Hiso : FrameLocusIsoInvarianceStatement.{0}) (HE : FrameEmbeddingExistenceStatement.{0})
    (HU : FrameEmbeddingUniquenessStatement.{0}) : FrameChartFiniteTypeStatement := by
  intro P g d _ hd
  refine ⟨3, ?_⟩
  intro n _ hn ρ
  obtain ⟨X, U, hU, hft, hqc⟩ := exists_isUniversalFrameDatum_finiteType
    HL HP Hiso HE HU P g d n hd hn ρ
  obtain ⟨a, ha, ha'⟩ := frameChart_of_isUniversalFrameDatum hd hn ρ X U hU
  exact ⟨X, a, ha, ha', hft, hqc⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
