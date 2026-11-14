import Langlands.GroupScheme.Rational.SpectralTorusNormKernelBoundedness
import Langlands.Geometry.Building.UnramifiedOneStabilizerBoundedness
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-! # Norm-one tori over the actual maximal unramified field -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The norm-one subgroup of every actual affine torus over the maximal
unramified field is algebraically bounded for the prescribed valuative relation. -/
def TorusNormOneBoundedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left], IsTorus T →
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    IsAlgebraicallyBounded (inertiaFixedField F) T.X
      (characterValuationKernel (valuation F) T : Set (rationalPoints T))

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F

/-- Integer normalization and the spectral valuation have exactly the same
character-unit locus on the actual fixed field. -/
theorem characterValuationKernel_eq_spectralCharacterUnitLocus
    (T : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) :
    (characterValuationKernel (valuation F) T : Set (rationalPoints T)) =
      spectralCharacterUnitLocus F (inertiaFixedField F) T := by
  ext p
  simp only [SetLike.mem_coe, mem_characterValuationKernel,
    spectralCharacterUnitLocus, Set.mem_ofPred_eq]
  apply forall_congr'
  intro χ
  rw [← fixedFieldValuation_eq_spectralValuation F]
  exact (valuation_isEquiv F).eq_one_iff_eq_one

/-- Torus norm-one boundedness uses completeness only on the original local
field and retains the prescribed fixed-field valuative relation. -/
theorem isAlgebraicallyBounded_characterValuationKernel
    (T : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T) :
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    IsAlgebraicallyBounded (inertiaFixedField F) T.X
      (characterValuationKernel (valuation F) T : Set (rationalPoints T)) := by
  rw [characterValuationKernel_eq_spectralCharacterUnitLocus F T]
  have h := isAlgebraicallyBounded_spectralCharacterUnitLocus (F := F) T hT
  rw [← fixedFieldValuation_eq_spectralValuation F] at h
  exact h

/-- The exact torus statement over the actual maximal unramified field. -/
theorem torusNormOneBounded : TorusNormOneBoundedStatement.{u} := by
  intro F _ _ _ _ T _ hT
  exact isAlgebraicallyBounded_characterValuationKernel F T hT

/-- Every morphism of affine group schemes carries this norm-one torus
subgroup to an algebraically bounded subset. -/
theorem isAlgebraicallyBounded_image_characterValuationKernel
    {T G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffine T.X.left] [IsAffine G.X.left] (j : T ⟶ G) (hT : IsTorus T) :
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    IsAlgebraicallyBounded (inertiaFixedField F) G.X
      (rationalPoints.map j ''
        (characterValuationKernel (valuation F) T : Set (rationalPoints T))) := by
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  exact (isAlgebraicallyBounded_characterValuationKernel F T hT).image_rationalPointsMap j

/-- For supplied building data, the only additional input needed by this
torus route is the actual centralizer's torus structure. -/
theorem centralizerNormOneBounded_of_isTorus
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : BuildingData F G) (hZ : IsTorus C.centralizer.Z) :
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    IsAlgebraicallyBounded (inertiaFixedField F) G.X
      (rationalPoints.map C.centralizer.j ''
        (characterValuationKernel (valuation F) C.centralizer.Z :
          Set (rationalPoints C.centralizer.Z))) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion C.centralizer.j.hom.hom.left := C.centralizer.isClosedSubgroup
  let : IsAffine C.centralizer.Z.X.left :=
    isAffine_of_isAffineHom C.centralizer.j.hom.hom.left
  exact isAlgebraicallyBounded_image_characterValuationKernel F C.centralizer.j hZ

end Langlands.Geometry.Building.MaximalUnramified
