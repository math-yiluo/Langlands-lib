import Langlands.Geometry.Analytic.SaturatedRecognitionCospans
import Langlands.Geometry.Analytic.FibreProductChartSystem
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Statement

/-! # Smallness of the actual recognized fibre-product quotient -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace FibreProduct

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  (p : PairIndex f g) (k : C.atlas.Index) (hk : IsCommonBase f g p.1.1 p.1.2 k)

/-- The whole pair algebra is independent of the chosen common base chart,
by the two full bounded pushout universal properties. -/
def commonBaseAlgebraEquiv : BoundedAlgEquiv K (algebra f g p)
    (AffinoidPushout.algebra (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2)) := by
  let a := f.pullback p.1.1 k hk.1
  let b := g.pullback p.1.2 k hk.2
  let S := AffinoidPushout.algebra a b
  let α : BoundedAlgHom K (algebra f g p) S :=
    AffinoidPushout.lift (leftBase f g p) (rightBase f g p) S
      (AffinoidPushout.leftMap a b) (AffinoidPushout.rightMap a b)
      (condition_of_isCommonBase hk (isCommonBase_base f g p) _ _
        (AffinoidPushout.condition a b))
  let β : BoundedAlgHom K S (algebra f g p) :=
    AffinoidPushout.lift a b (algebra f g p)
      (leftMap f g p) (rightMap f g p) (condition f g p hk)
  have hβα : β.comp α = BoundedAlgHom.id K (algebra f g p) := by
    apply AffinoidPushout.hom_ext
    · rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.id_comp]
      dsimp only [α, β]
      rw [AffinoidPushout.lift_comp_leftMap, AffinoidPushout.lift_comp_leftMap]
    · rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.id_comp]
      dsimp only [α, β]
      rw [AffinoidPushout.lift_comp_rightMap, AffinoidPushout.lift_comp_rightMap]
  have hαβ : α.comp β = BoundedAlgHom.id K S := by
    apply AffinoidPushout.hom_ext a b
    · rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.id_comp]
      dsimp only [α, β]
      rw [AffinoidPushout.lift_comp_leftMap, AffinoidPushout.lift_comp_leftMap]
    · rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.id_comp]
      dsimp only [α, β]
      rw [AffinoidPushout.lift_comp_rightMap, AffinoidPushout.lift_comp_rightMap]
  exact BoundedAlgEquiv.ofHomInv α β
    (fun x => congrArg (fun q : BoundedAlgHom K (algebra f g p) (algebra f g p) => q x) hβα)
    (fun x => congrArg (fun q : BoundedAlgHom K S S => q x) hαβ)

/-- A finite first map over any common base makes the actual pair spectrum
small whenever the second factor chart is small. -/
theorem small_pairSpectrum_of_finite_commonBase
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (hf : (f.pullback p.1.1 k hk.1).IsFiniteBanach)
    [Small.{v} (BanachSpectrum (B.atlas.algebra p.1.2))] :
    Small.{v} (BanachSpectrum (algebra f g p)) := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout
    (f.pullback p.1.1 k hk.1) (g.pullback p.1.2 k hk.2) hpush hf
  exact small_of_injective (f := (commonBaseAlgebraEquiv f g p k hk).spectrumHomeomorph.symm)
    (commonBaseAlgebraEquiv f g p k hk).spectrumHomeomorph.symm.injective

end FibreProduct

namespace SaturatedAtlasPresentation

variable {A B C : SaturatedAtlasPresentation.{u, v, v} K}
  (f : A ⟶ C) (g : B ⟶ C)

/-- Literal finite chart pairs through every compatible ambient pair cover
every point of the actual quotient by small pair spectra. -/
theorem small_fibreProductSpace_of_pointedFiniteEtalePairs
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (hfinite : HasPointedFiniteEtalePairs f g) :
    Small.{v} (FibreProduct.chartSystem
      (CompatibleStrongHom.ofSaturated f A.hasAllLocalDomains)
      (CompatibleStrongHom.ofSaturated g B.hasAllLocalDomains)).Space := by
  let F := CompatibleStrongHom.ofSaturated f A.hasAllLocalDomains
  let G := CompatibleStrongHom.ofSaturated g B.hasAllLocalDomains
  let D := FibreProduct.chartSystem F G
  let S : Set (FibreProduct.PairIndex F G) :=
    {p | Small.{v} (BanachSpectrum (FibreProduct.algebra F G p))}
  let : ∀ p : S, Small.{v} (BanachSpectrum (FibreProduct.algebra F G p.val)) :=
    fun p => p.property
  apply small_of_surjective (f := fun t : Σ p : S,
    BanachSpectrum (FibreProduct.algebra F G p.val) => D.chart t.1.val t.2)
  intro z
  obtain ⟨i, j, k, hi, hj, s, r, hs, hr, hf, -, -⟩ :=
    hfinite (FibreProduct.fst F G z) (FibreProduct.snd F G z)
      (FibreProduct.baseMap_fst F G z)
  let p : FibreProduct.PairIndex F G := ⟨(i, j), k, hi, hj⟩
  have hk : FibreProduct.IsCommonBase F G p.1.1 p.1.2 k := ⟨hi, hj⟩
  let : Small.{v} (BanachSpectrum (B.presentation.atlas.algebra j)) :=
    small_of_injective (B.presentation.atlas.isEmbedding_chart j).injective
  have hp : Small.{v} (BanachSpectrum (FibreProduct.algebra F G p)) :=
    FibreProduct.small_pairSpectrum_of_finite_commonBase F G p k hk hpush hf
  have hz : z ∈ range (D.chart p) :=
    (FibreProduct.mem_range_chart_iff F G p z).2 ⟨⟨s, hs⟩, ⟨r, hr⟩⟩
  obtain ⟨t, ht⟩ := hz
  exact ⟨⟨⟨p, hp⟩, t⟩, ht⟩

/-- The quotient of the canonical recognition-selected cospan is small in
the unchanged ambient space universe, from the original strong etale input. -/
theorem recognition_fibreProductSpace_small
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) (hf : strongEtale f) :
    Small.{v} (FibreProduct.chartSystem
      (CompatibleStrongHom.ofSaturated (recognitionMap f) (recognitionSource f).hasAllLocalDomains)
      (CompatibleStrongHom.ofSaturated (recognitionMap g) (recognitionSource g).hasAllLocalDomains)).Space :=
  small_fibreProductSpace_of_pointedFiniteEtalePairs (recognitionMap f) (recognitionMap g)
    hpush (recognitionMaps_hasPointedFiniteEtalePairs f g hf)

end SaturatedAtlasPresentation

end Langlands.Analytic
