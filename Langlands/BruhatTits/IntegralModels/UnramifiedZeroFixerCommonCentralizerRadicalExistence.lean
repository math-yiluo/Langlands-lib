import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCommonCentralizerRadical
import Langlands.GroupScheme.Absolute.TorusCentralizerUnipotentRadicalProof

/-! # Unconditional common centralizer radical for maximal-unramified models -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

/-- A single subgroup is the centralizer intersection of every actual upstairs
radical preimage on the nonempty single-facet domain. -/
def UnramifiedZeroFixerCommonCentralizerRadicalExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G),
    ∃ H : Subgroup (rationalPoints G),
      H ≤ (rationalPoints.map C.centralizer.j).range ∧
      H ≤ E.zeroPoints ⊓ C.pointwiseFixer (Set.range C.apartmentMap) ∧
      ∀ (Ω : Set C.Apartment), Ω.Nonempty →
        (∃ x : C.Apartment, Ω ⊆ AffineRootSystem.facet C.affineRoots x) →
      ∀ (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
        N.IsSmooth →
        N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
      ∀ (U : GroupScheme
          (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
        (i : U ⟶ N.specialFibre), IsUnipotentRadical i →
        (((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap) ⊓
          (rationalPoints.map C.centralizer.j).range = H

/-- The torus-centralizer radical-intersection proof discharges the sole
geometric premise of the published common-subgroup construction. -/
theorem unramifiedZeroFixerCommonCentralizerRadicalExistence :
    UnramifiedZeroFixerCommonCentralizerRadicalExistenceStatement.{u} :=
  unramifiedZeroFixerCommonCentralizerRadical torusCentralizerUnipotentRadical

end Langlands.BruhatTits.IntegralModels
