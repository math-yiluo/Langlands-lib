/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-! # The residue root map is an isomorphism

## References

* Stacks Project, Tags 0152, 06YY and 0GLZ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
private theorem cachedModSheafify (Z : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify Z.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance
attribute [local instance] cachedModSheafify

/-- For a scheme `Z`, `n ≥ 0` and `R = ULift (ZMod n)`, the ordinary finite root tensor map
`μ_n → forget(R_Z(1))` is an isomorphism. -/
theorem residueFiniteRootMap_isIso (Z : Scheme.{u}) (n : ℕ)
    (hR : (n : ULift.{u + 1} (ZMod n)) = 0) :
    IsIso (ordinaryFiniteRootMap (ULift.{u + 1} (ZMod n)) n hR Z) := by
  let R := ULift.{u + 1} (ZMod n)
  let φ := Scheme.finiteEtaleTwistScalar n R hR
  have hφ : φ = ULift.ringEquiv.symm.toRingHom := Subsingleton.elim _ _
  have : (ModuleCat.restrictScalars.{u + 1} φ).IsEquivalence := by
    rw [hφ]
    infer_instance
  let ad := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} φ
  have : (ModuleCat.extendScalars.{0, u + 1, u + 1} φ).IsEquivalence :=
    ad.isEquivalence_left_of_isEquivalence_right
  let P := Scheme.finiteEtaleMuModulePresheaf Z n
  have hP : Presheaf.IsSheaf Z.smallEtaleTopology P := by
    apply Presheaf.isSheaf_of_isSheaf_comp Z.smallEtaleTopology P
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})
    exact (Z.rootsOfUnitySheaf n).property
  have hQ := Presheaf.isSheaf_comp_of_isSheaf Z.smallEtaleTopology P
    (ModuleCat.extendScalars φ) hP
  have : IsIso (toSheafify Z.smallEtaleTopology (P ⋙ ModuleCat.extendScalars φ)) :=
    isIso_toSheafify Z.smallEtaleTopology hQ
  have hW (W : Z.Etaleᵒᵖ) : IsIso
      ((ordinaryFiniteRootMap R n hR Z).hom.app W) := by
    change IsIso ((forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}).map
        (((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} φ).unit.app (P.obj W))) ≫
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
        ((toSheafify Z.smallEtaleTopology (P ⋙ ModuleCat.extendScalars φ)).app W))
    infer_instance
  have : IsIso (ordinaryFiniteRootMap R n hR Z).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (ordinaryFiniteRootMap R n hR Z)) := ‹IsIso (ordinaryFiniteRootMap R n hR Z).hom›
  exact isIso_of_reflects_iso (ordinaryFiniteRootMap R n hR Z)
    (sheafToPresheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
end AlgebraicGeometry.Etale
