import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartUniversalDatum
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertLocusStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusIsoInvarianceStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingExistenceStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingUniquenessStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingBaseChange
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingFaithful
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.HilbertClassifying

/-! # Frame charts from the frame-normalized Hilbert locus -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry

/-- Isomorphic data with frame locus `⊤` realize the same embedded family by any of their
frame-normalized embeddings. -/
theorem Datum.Realizes.eq_of_polarizedIso (HU : FrameEmbeddingUniquenessStatement.{0})
    {T : Scheme.{0}} {g d n m : ℕ} {P : Prerequisites.{0}} {b b' : Datum P T g d n}
    (e : PolarizedIso b b') {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n}
    (hb : b.frameLocus ρ = ⊤)
    {ψ : b.abelian.X.left ⟶ RelativeProjectiveSpace T m}
    {ψ' : b'.abelian.X.left ⟶ RelativeProjectiveSpace T m}
    {I I' : (RelativeProjectiveSpace T m).IdealSheafData}
    {σ σ' : (Fin (2 * g) → ZMod n) → (T ⟶ ProjectiveSpace (ULift.{0} ℤ) m)}
    (h : b.IsFrameEmbedding ρ ψ) (h' : b'.IsFrameEmbedding ρ ψ')
    (hr : b.Realizes ψ I σ) (hr' : b'.Realizes ψ' I' σ') : I = I' ∧ σ = σ' := by
  have heq := HU P T g d n m b ρ ψ _ hb h (h'.ofPolarizedIso e)
  have hr'' := hr'.ofPolarizedIso e
  rw [← heq] at hr''
  exact ⟨hr.1.symm.trans hr''.1, funext fun r => (hr.2 r).symm.trans (hr''.2 r)⟩

/-- From the frame-normalized Hilbert locus and the auxiliary statements, the frame chart of
`ρ` has a universal frame datum. -/
theorem exists_isUniversalFrameDatum
    (HL : FrameHilbertLocusStatement) (HP : CubicBundlePolarizationDeterminationStatement.{0})
    (Hbc : FrameLocusBaseChangeStatement.{0}) (Hiso : FrameLocusIsoInvarianceStatement.{0})
    (HE : FrameEmbeddingExistenceStatement.{0}) (HU : FrameEmbeddingUniquenessStatement.{0})
    (P : Prerequisites.{0}) (g d n : ℕ) (hd : 0 < d) (hn : 3 ≤ n)
    (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n) :
    ∃ (X : LevelBase n) (U : Datum P X.obj g d n), IsUniversalFrameDatum ρ X U := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨S, IS, σS, hS, hflat, hlfp, hclass⟩ :=
    exists_relativeProjectiveFamily_classifying.{0} (cubicProjectiveDimension g d)
      (Fin (2 * g) → ZMod n)
  obtain ⟨S', j, hj, ⟨U, ψU, hUframe, hψU, hUreal⟩, hfac⟩ :=
    HL P g d n hd hn ρ S IS σS hflat hlfp
  have : Mono j := inferInstance
  have hUf : ∀ (T : LevelBase n) (f : T ⟶ S'), (U.pullback f.hom).frameLocus ρ = ⊤ := by
    intro T f
    rw [Hbc P S'.obj T.obj g d n hd U f.hom ρ, hUframe]
    rfl
  refine ⟨S', U, ⟨?_, ?_, ?_⟩⟩
  · -- pullbacks along different morphisms are not isomorphic
    intro T f f' ⟨e⟩
    have hψ₁ := hψU.pullback (f := f.hom)
    have hψ₂ := hψU.pullback (f := f'.hom)
    have hr₁ := hUreal.pullback (f := f.hom) hψU
    have hr₂ := hUreal.pullback (f := f'.hom) hψU
    obtain ⟨hI, hσ⟩ := Datum.Realizes.eq_of_polarizedIso HU e (hUf T f) hψ₁ hψ₂ hr₁ hr₂
    have hfl := hψ₁.flat
    have hlp := hψ₁.locallyOfFinitePresentation
    rw [hr₁.1] at hfl hlp
    obtain ⟨t, -, ht⟩ := hclass T.obj _ (fun r => f.hom ≫ j ≫ σS r) hfl hlp
    have h₁ : f.hom ≫ j = t := ht _ ⟨by
      rw [RelativeProjectiveSpace.map_comp, Scheme.IdealSheafData.comap_comp],
      fun r => by simp only [Category.assoc]⟩
    have h₂ : f'.hom ≫ j = t := ht _ ⟨by
      rw [RelativeProjectiveSpace.map_comp, Scheme.IdealSheafData.comap_comp, hI],
      fun r => by
        have := (congrFun hσ r).symm
        simp only [Category.assoc] at this ⊢
        exact this⟩
    apply ObjectProperty.hom_ext
    exact (cancel_mono j).mp (h₁.trans h₂.symm)
  · -- every datum with frame locus `⊤` is a pullback
    intro T b hb
    obtain ⟨ψ, hψ⟩ := HE P T.obj g d n hd b ρ hb
    obtain ⟨t, ⟨htI, htσ⟩, -⟩ := hclass T.obj ψ.ker
      (fun r => b.torsionPoint r ≫ ψ ≫ RelativeProjectiveSpace.toIntegral _ _)
      hψ.flat hψ.locallyOfFinitePresentation
    have hreal : b.Realizes ψ (IS.comap (RelativeProjectiveSpace.map _ t))
        (fun r => t ≫ σS r) := ⟨htI.symm, fun r => (htσ r).symm⟩
    obtain ⟨t', ht'⟩ := hfac T t b ψ hb hψ hreal
    refine ⟨LevelBase.homMk t', ?_⟩
    have hr₁ := hUreal.pullback (f := t') hψU
    apply Datum.nonempty_polarizedIso_of_realizes HP hψ (hψU.pullback (f := t')) hreal
    refine ⟨?_, fun r => ?_⟩
    · rw [hr₁.1, ← Scheme.IdealSheafData.comap_comp, ← RelativeProjectiveSpace.map_comp, ht']
    · rw [hr₁.2 r, ← ht']
      simp only [Category.assoc]
  · -- data isomorphic to pullbacks have frame locus `⊤`
    intro T f b ⟨e⟩
    rw [Hiso P T.obj g d n _ b (U.pullback f.hom) ρ ⟨e⟩]
    exact hUf T f

set_option linter.defProp false in
/-- Proved definition: the frame-normalized Hilbert locus (relative GIT Proposition 7.3),
determination of the polarization by the cubic bundle, base change and isomorphism
invariance of the frame locus, and existence and uniqueness of frame-normalized cubic
embeddings imply `FrameChartRepresentabilityStatement`. -/
def frameChartRepresentability_of_frameHilbertLocus
    (HL : FrameHilbertLocusStatement) (HP : CubicBundlePolarizationDeterminationStatement.{0})
    (Hbc : FrameLocusBaseChangeStatement.{0}) (Hiso : FrameLocusIsoInvarianceStatement.{0})
    (HE : FrameEmbeddingExistenceStatement.{0}) (HU : FrameEmbeddingUniquenessStatement.{0}) :
    FrameChartRepresentabilityStatement := by
  intro P g d n hd hn ρ
  obtain ⟨X, U, hU⟩ := exists_isUniversalFrameDatum HL HP Hbc Hiso HE HU P g d n hd hn ρ
  obtain ⟨a, ha⟩ := frameChart_of_isUniversalFrameDatum hd hn ρ X U hU
  exact ⟨X, a, ha⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
