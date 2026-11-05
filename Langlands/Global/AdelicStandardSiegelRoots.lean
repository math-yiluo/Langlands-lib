import Langlands.Global.AdelicStandardSiegelFactors
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.SubgroupRelativeRootComparison

/-! # Actual Lie roots of the canonical standard Siegel parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme

variable (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)

local instance : IsAffineHom (Standard.parabolicScheme i ν ∅).X.hom :=
  (Standard.isClosedSubgroup_parabolicHom i ν ∅).isAffineHom

include hG hi hν

/-- The nonzero weights on the actual canonical standard parabolic Lie
algebra are exactly the positive ambient relative roots. -/
theorem relativeRoots_torusToStandardParabolic :
    relativeRoots (torusToStandardParabolic k G T i ν) = positiveRelativeRoots i ν := by
  have hp : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (Standard.parabolicHom i ν ∅) := by
    rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact Standard.isRepresentedBy_parabolicHom i ν ∅
  exact RelativeRoot.relativeRoots_parabolicRepresentative_of_generic
    (torusToStandardParabolic k G T i ν) (Standard.parabolicHom i ν ∅)
    hi.1.1 i ν hp (torusToStandardParabolic_comp k G T i ν) hν

/-- The identity on characters identifies the actual canonical parabolic
roots with the positive ambient roots used in the Siegel chamber. -/
def standardParabolicPositiveRootsEquiv :
    relativeRoots (torusToStandardParabolic k G T i ν) ≃ positiveRelativeRoots i ν where
  toFun α := ⟨α.val, (relativeRoots_torusToStandardParabolic k G T i ν hG hi hν) ▸
    α.property⟩
  invFun α := ⟨α.val, (relativeRoots_torusToStandardParabolic k G T i ν hG hi hν).symm ▸
    α.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem standardParabolicPositiveRootsEquiv_apply
    (α : relativeRoots (torusToStandardParabolic k G T i ν)) :
    (standardParabolicPositiveRootsEquiv k G T i ν hG hi hν α : characterLattice T) = α :=
  rfl

end Langlands.Global.AdelicSiegelFactors
