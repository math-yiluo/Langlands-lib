import Langlands.Geometry.Building.KPSplitNorm
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormProof

/-! # Bounded split-torus norms over finite extensions of the unramified closure -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) E]
  (L : IntermediateField E (SeparableClosure F)) [FiniteDimensional E L]

/-- The prescribed spectral valuation on a second intermediate extension. -/
def nestedIntermediateValuation : Valuation L ℝ≥0 :=
  (sepClosureValuation F).comap (algebraMap L (SeparableClosure F))

/-- The two restrictions of the ambient spectral valuation are compatible. -/
instance nestedIntermediateValuation_extends :
    (intermediateValuation F E).HasExtension (nestedIntermediateValuation F E L) where
  val_isEquiv_comap x y := by
    change sepClosureValuation F (algebraMap E (SeparableClosure F) x) ≤
      sepClosureValuation F (algebraMap E (SeparableClosure F) y) ↔
      sepClosureValuation F (algebraMap L (SeparableClosure F) (algebraMap E L x)) ≤
      sepClosureValuation F (algebraMap L (SeparableClosure F) (algebraMap E L y))
    rw [IsScalarTower.algebraMap_apply E L (SeparableClosure F),
      IsScalarTower.algebraMap_apply E L (SeparableClosure F)]

/-- The nested spectral valuation is invariant under every relative automorphism. -/
theorem nestedIntermediateValuation_conjugate (σ : L ≃ₐ[E] L) (x : L) :
    nestedIntermediateValuation F E L (σ x) =
      nestedIntermediateValuation F E L x := by
  let : NontriviallyNormedField F := Langlands.LocalGalois.localNormedField F
  let : IsScalarTower F E (SeparableClosure F) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra F L := ((algebraMap E L).comp (algebraMap F E)).toAlgebra
  let : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F L (SeparableClosure F) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap F (SeparableClosure F) x =
      algebraMap L (SeparableClosure F) (algebraMap E L (algebraMap F E x))
    rw [← IsScalarTower.algebraMap_apply E L (SeparableClosure F),
      ← IsScalarTower.algebraMap_apply F E (SeparableClosure F)]
  apply NNReal.eq
  change spectralNorm F (SeparableClosure F) (algebraMap L (SeparableClosure F) (σ x)) =
    spectralNorm F (SeparableClosure F) (algebraMap L (SeparableClosure F) x)
  rw [← spectralNorm.eq_of_tower, ← spectralNorm.eq_of_tower]
  exact (spectralNorm_eq_of_equiv (σ.restrictScalars F) x).symm

/-- The published inertia-fixed-field theorem supplies scalar bounded norm lifts. -/
theorem nestedIntermediate_unit_norm_surjective (a : Eˣ)
    (ha : intermediateValuation F E (a : E) = 1) :
    ∃ b : Lˣ, nestedIntermediateValuation F E L (b : L) = 1 ∧
      Units.map (Algebra.norm E) b = a :=
  Langlands.ClassFieldTheory.Local.separableInertiaUnitNormSurjectivity F E L a ha

variable [IsGalois E L]

/-- The actual bounded rational norm for the prescribed local intermediate fields. -/
def inertiaBoundedNorm (T : CommGroupScheme (Spec (CommRingCat.of E)))
    [IsAffine T.X.left] :
    characterValuationKernel (nestedIntermediateValuation F E L)
        ((CommGroupScheme.baseChange (baseMap E L)).obj T).toGrp →*
      characterValuationKernel (intermediateValuation F E) T.toGrp :=
  boundedRationalNorm E L (intermediateValuation F E) (nestedIntermediateValuation F E L)
    (nestedIntermediateValuation_conjugate F E L) T

/-- On split tori the local bounded norm is surjective with no scalar norm premise. -/
theorem inertiaBoundedNorm_surjective_of_split
    (T : CommGroupScheme (Spec (CommRingCat.of E))) [IsAffine T.X.left]
    (hT : IsSplitTorus T.toGrp) :
    Function.Surjective (inertiaBoundedNorm F E L T) :=
  boundedRationalNorm_surjective_of_split E L (intermediateValuation F E)
    (nestedIntermediateValuation F E L) (nestedIntermediateValuation_conjugate F E L)
    (nestedIntermediate_unit_norm_surjective F E L) T hT

end Langlands.Geometry.Building
