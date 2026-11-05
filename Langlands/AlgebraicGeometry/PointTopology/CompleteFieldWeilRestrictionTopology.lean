import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionLocalTopology
import Langlands.Global.AdelicFunctoriality.Extension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Weil-restriction topology over complete fields and actual completions -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section CompleteField

variable (K L : Type u) [NontriviallyNormedField K] [CompleteSpace K]
  [Field L] [TopologicalSpace L] [IsTopologicalDivisionRing L] [T2Space L]
  [Algebra K L] [ContinuousSMul K L] [Module.Finite K L]
  (Y : Over (Spec (CommRingCat.of L))) [LocallyOfFiniteType Y.hom]

/-- Finite-dimensional topology over a complete nontrivially normed field
supplies the module-topology premise of the actual point homeomorphism. -/
def completeFieldWeilRestrictionPointHomeomorph
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace L n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec L n = Y.hom) :
    letI : TopologicalSpace (RingPoint K (affineChartWeilRestriction K L Y) K) :=
      schemePointTopology K (affineChartWeilRestriction K L Y) K
    letI : TopologicalSpace (RingPoint L Y L) := schemePointTopology L Y L
    RingPoint K (affineChartWeilRestriction K L Y) K ≃ₜ RingPoint L Y L := by
  letI : IsModuleTopology K L := isModuleTopologyOfFiniteDimensional
  exact projectiveImmersionWeilRestrictionPointHomeomorph K L Y n i hi

@[simp]
theorem completeFieldWeilRestrictionPointHomeomorph_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace L n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec L n = Y.hom)
    (p : RingPoint K (affineChartWeilRestriction K L Y) K) :
    completeFieldWeilRestrictionPointHomeomorph K L Y n i hi p =
      affineChartWeilRestrictionBasePointComparison K L Y p := rfl

end CompleteField

section FiniteCompletion

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
  (Y : Over (Spec (CommRingCat.of (w.adicCompletion L)))) [LocallyOfFiniteType Y.hom]

/-- The comparison for an actual extension of finite completed number fields,
with the actual continuous completion embedding as scalar action. -/
def finiteCompletionWeilRestrictionPointHomeomorph
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace (w.adicCompletion L) n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec (w.adicCompletion L) n = Y.hom) :
    letI : TopologicalSpace (RingPoint (v.adicCompletion K)
        (affineChartWeilRestriction (v.adicCompletion K) (w.adicCompletion L) Y)
        (v.adicCompletion K)) :=
      schemePointTopology (v.adicCompletion K)
        (affineChartWeilRestriction (v.adicCompletion K) (w.adicCompletion L) Y)
        (v.adicCompletion K)
    letI : TopologicalSpace (RingPoint (w.adicCompletion L) Y (w.adicCompletion L)) :=
      schemePointTopology (w.adicCompletion L) Y (w.adicCompletion L)
    RingPoint (v.adicCompletion K)
        (affineChartWeilRestriction (v.adicCompletion K) (w.adicCompletion L) Y)
        (v.adicCompletion K) ≃ₜ
      RingPoint (w.adicCompletion L) Y (w.adicCompletion L) := by
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact completeFieldWeilRestrictionPointHomeomorph
    (v.adicCompletion K) (w.adicCompletion L) Y n i hi

@[simp]
theorem finiteCompletionWeilRestrictionPointHomeomorph_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace (w.adicCompletion L) n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec (w.adicCompletion L) n = Y.hom)
    (p : RingPoint (v.adicCompletion K)
      (affineChartWeilRestriction (v.adicCompletion K) (w.adicCompletion L) Y)
      (v.adicCompletion K)) :
    finiteCompletionWeilRestrictionPointHomeomorph K L v w Y n i hi p =
      affineChartWeilRestrictionBasePointComparison
        (v.adicCompletion K) (w.adicCompletion L) Y p := rfl

end FiniteCompletion

section InfiniteCompletion

open NumberField
open scoped NumberField.LiesOver Langlands.Global.AdelicFunctoriality.InfiniteExtension

/-- The original norm topology on an actual infinite completion is nontrivial. -/
@[instance_reducible]
def infiniteCompletionNontriviallyNormedField
    {K : Type u} [Field K] (v : InfinitePlace K) :
    NontriviallyNormedField v.Completion :=
  { (inferInstance : NormedField v.Completion) with
    non_trivial := by
      refine ⟨2, ?_⟩
      have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.extensionEmbedding v)) (2 : v.Completion)
      rw [← h]
      norm_num only [map_ofNat, Complex.norm_ofNat] }

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
  (Y : Over (Spec (CommRingCat.of w.Completion))) [LocallyOfFiniteType Y.hom]

/-- The actual infinite-completion comparison, including both real and complex
places, uses the existing completed scalar action and its proved finite degree. -/
def infiniteCompletionWeilRestrictionPointHomeomorph
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace w.Completion n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec w.Completion n = Y.hom) :
    letI : TopologicalSpace (RingPoint v.Completion
        (affineChartWeilRestriction v.Completion w.Completion Y) v.Completion) :=
      schemePointTopology v.Completion
        (affineChartWeilRestriction v.Completion w.Completion Y) v.Completion
    letI : TopologicalSpace (RingPoint w.Completion Y w.Completion) :=
      schemePointTopology w.Completion Y w.Completion
    RingPoint v.Completion (affineChartWeilRestriction v.Completion w.Completion Y)
        v.Completion ≃ₜ RingPoint w.Completion Y w.Completion := by
  letI := infiniteCompletionNontriviallyNormedField v
  exact completeFieldWeilRestrictionPointHomeomorph v.Completion w.Completion Y n i hi

@[simp]
theorem infiniteCompletionWeilRestrictionPointHomeomorph_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace w.Completion n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec w.Completion n = Y.hom)
    (p : RingPoint v.Completion (affineChartWeilRestriction v.Completion w.Completion Y)
      v.Completion) :
    infiniteCompletionWeilRestrictionPointHomeomorph K L v w Y n i hi p =
      affineChartWeilRestrictionBasePointComparison v.Completion w.Completion Y p := rfl

end InfiniteCompletion

end Langlands.AlgebraicGeometry.PointTopology
