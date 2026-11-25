/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Explicit standard basis germs on an affine open

Source: Stacks Project, Tags 01HV, 01IB, 01C6 and 0098.
(blueprint: def-sc-affine-free-basis-germs).
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Sheafification, ordinary open direct image, and the ambient stalk. -/
noncomputable def affineFreeStalkFunctor (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hU : IsAffineOpen U) : ModuleCat.{u} Γ(X, U) ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  affinePerfectSheafification X U hU ⋙
    SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U) ⋙
    RingedSpace.moduleStalkFunctor X.toRingedSpace x

private theorem stalk_additive (X : Scheme.{u}) (x : X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).Additive := by
  constructor
  intro M N f g
  ext v
  obtain ⟨V, hxV, v, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf v
  change RingedSpace.stalkAddMap X.toRingedSpace x (f + g) _ =
    RingedSpace.stalkAddMap X.toRingedSpace x f _ +
      RingedSpace.stalkAddMap X.toRingedSpace x g _
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ N.val.presheaf V x hxV
    ((f.val.app (.op V)) v + (g.val.app (.op V)) v) = _
  exact map_add _ _ _

/-- The affine stalk functor preserves sums of module maps. -/
instance affineFreeStalkFunctor_additive (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hU : IsAffineOpen U) : (affineFreeStalkFunctor X x U hU).Additive := by
  let F := affinePerfectSheafification X U hU
  let T := Modules.restrictFunctor hU.isoSpec.hom
  have : T.Additive := Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
  have : CategoryTheory.Limits.HasBinaryBiproducts
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts
  have : CategoryTheory.Limits.PreservesBinaryBiproducts (Modules.overEquiv U).inverse :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : (Modules.overEquiv U).inverse.Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : CategoryTheory.Limits.PreservesBinaryBiproducts (tilde.functor Γ(X, U)) :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tilde.functor Γ(X, U)).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : F.Additive := by unfold F affinePerfectSheafification; infer_instance
  let P := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  have : P.Additive := by
    constructor
    intro M N f g
    ext V v
    rfl
  have := stalk_additive X x
  change (F ⋙ P ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x).Additive
  infer_instance

/-- The regular coordinate module sheafifies to the structure sheaf on the slice site. -/
noncomputable def affineRegularSheafIso (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) :
    (affinePerfectSheafification X U hU).obj (ModuleCat.of Γ(X, U) Γ(X, U)) ≅
      SheafOfModules.unit ((moduleRings X.toRingedSpace).over U) :=
  (Modules.overEquiv U).inverse.mapIso
    ((Modules.restrictFunctor hU.isoSpec.hom).mapIso tildeSelf ≪≫
      Modules.restrictUnitIso hU.isoSpec.hom ≪≫ Modules.overEquivFunctorObjUnitIso U) ≪≫
    ((Modules.overEquiv U).unitIso.app
      (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U))).symm

/-- Inclusion of a standard coordinate, as a map from the regular module. -/
noncomputable def affineCoordinateInclusion (X : Scheme.{u}) (U : X.Opens)
    (n : ℕ) (p : Fin n) :
    ModuleCat.of Γ(X, U) Γ(X, U) ⟶
      ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U))) :=
  ModuleCat.ofHom
    { toFun := fun r ↦ ULift.up (Pi.single p r)
      map_add' := by
        intro r s
        apply ULift.ext
        change (Pi.single p (r + s) : Fin n → Γ(X, U)) = _
        ext q
        by_cases h : q = p <;> simp [h]
      map_smul' := by
        intro r s
        apply ULift.ext
        ext q
        by_cases h : q = p <;> simp [h] }

/-- Projection onto one coordinate. -/
def affineCoordinateProjection (X : Scheme.{u}) (U : X.Opens) (n : ℕ) (p : Fin n) :
    ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U))) ⟶
      ModuleCat.of Γ(X, U) Γ(X, U) :=
  ModuleCat.ofHom
    { toFun := fun v ↦ v.down p
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The germ of the unit section under the explicit regular-module sheaf isomorphism. -/
noncomputable def affineRegularStalkGerm (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (hU : IsAffineOpen U) :
    (affineFreeStalkFunctor X x U hU).obj (ModuleCat.of Γ(X, U) Γ(X, U)) := by
  let P := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  let a := P.map (affineRegularSheafIso X U hU).inv
  exact TopCat.Presheaf.germ
    (P.obj ((affinePerfectSheafification X U hU).obj
      (ModuleCat.of Γ(X, U) Γ(X, U)))).val.presheaf
    U x hxU ((a.val.app (.op U))
      (1 : ((moduleRings X.toRingedSpace).over U).obj.obj
        (.op ((Over.star U).obj U))))

/-- The explicit comparison on the regular module, given by its unit germ. -/
noncomputable def affineRegularStalkComparison (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (hU : IsAffineOpen U) :
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶
      (affineFreeStalkFunctor X x U hU).obj (ModuleCat.of Γ(X, U) Γ(X, U)) :=
  ModuleCat.ofHom
    { toFun := fun r ↦ r • affineRegularStalkGerm X x U hxU hU
      map_add' := fun r s ↦ add_smul r s _
      map_smul' := fun r s ↦ mul_smul r s _ }

/-- The standard basis germ is the image of the unit germ under its coordinate inclusion.
This is constructed from actual maps, without choosing data from an existence theorem. -/
noncomputable def affineFreeBasisGerm (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (hU : IsAffineOpen U) (n : ℕ) (p : Fin n) :
    (affineFreeStalkFunctor X x U hU).obj
      (ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U)))) :=
  (affineFreeStalkFunctor X x U hU).map (affineCoordinateInclusion X U n p)
    (affineRegularStalkGerm X x U hxU hU)

/-- Multiplication by a coordinate-ring element on the regular module. -/
def affineScalarEnd (X : Scheme.{u}) (U : X.Opens) (a : Γ(X, U)) :
    ModuleCat.of Γ(X, U) Γ(X, U) ⟶ ModuleCat.of Γ(X, U) Γ(X, U) :=
  ModuleCat.ofHom
    { toFun := fun r ↦ a * r
      map_add' := mul_add a
      map_smul' := by intro r s; simp [mul_left_comm] }

/-- The linear combination of the standard basis germs with stalk coefficients.
(blueprint: def-sc-affine-free-basis-germs)
-/
noncomputable def affineFreeStalkComparison (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (hU : IsAffineOpen U) (n : ℕ) :
    ModuleCat.of (X.presheaf.stalk x) (ULift.{0} (Fin n → X.presheaf.stalk x)) ⟶
      (affineFreeStalkFunctor X x U hU).obj
        (ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U)))) :=
  ModuleCat.ofHom
    { toFun := fun v ↦ ∑ p, v.down p • affineFreeBasisGerm X x U hxU hU n p
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }

@[simp] theorem affineFreeStalkComparison_basis (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (hU : IsAffineOpen U) (n : ℕ) (p : Fin n) :
    affineFreeStalkComparison X x U hxU hU n (ULift.up (Pi.single p 1)) =
      affineFreeBasisGerm X x U hxU hU n p := by
  classical
  change (∑ q, (Pi.single p 1 : Fin n → X.presheaf.stalk x) q •
    affineFreeBasisGerm X x U hxU hU n q) = _
  simp [Pi.single_apply]

end AlgebraicGeometry.Scheme
