/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule

/-! # Scalars in the underived affine associated-sheaf functor

Source: Stacks Project, Tags 01I6 and 06Z0, associated-sheaf construction.
(blueprint: lem-sc-affine-sheafification-scalar).
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Scalar calculation for the associated-sheaf construction.
Source: Stacks Project, Tag 01I6.
(blueprint: lem-sc-affine-sheafification-scalar). -/
private theorem tilde_scalar_sections (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (r : R)
    (V : (Spec R).Opens) (x : Γ(tilde M, V)) :
    (tilde.map (r • 𝟙 M)).app V x =
      (Spec R).presheaf.map V.leTop.op ((Scheme.ΓSpecIso R).inv r) • x := by
  change (tilde.map (r • 𝟙 M)).app V x = r • x
  change ((modulesSpecToSheaf.map (tilde.map (r • 𝟙 M))).hom.app (op V)).hom x = r • x
  unfold tilde.map
  rw [Functor.FullyFaithful.map_preimage]
  have hx : r • x = ((tilde.modulesSpecToSheafIso M).app (op V)).inv.hom
      (r • ((tilde.modulesSpecToSheafIso M).app (op V)).hom x) := by
    simp
  rw [hx]
  change _ = @SMul.smul R ((structureSheafInType R M).obj.obj (op V)) inferInstance r x
  apply Subtype.ext
  funext y
  dsimp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  dsimp [StructureSheaf.comapₗ, StructureSheaf.comapFun,
    tilde.modulesSpecToSheafIso, LinearEquiv.toModuleIso]
  change StructureSheaf.Localizations.comapFun (r • LinearMap.id : M →ₗ[R] M)
    y.1 (x.1 y) = r • x.1 y
  induction x.1 y using LocalizedModule.induction_on with
  | _ m s =>
    simp only [StructureSheaf.Localizations.comapFun_mk,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [LocalizedModule.smul'_mk]
    rfl



set_option backward.isDefEq.respectTransparency false in
/-- Scalar calculation for the associated-sheaf construction.
Source: Stacks Project, Tag 01I6.
(blueprint: lem-sc-affine-sheafification-scalar). -/
private theorem affine_scalar_coefficient (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (r : X.presheaf.obj (op U)) (W : Over U) :
    let V : (U : Scheme.{u}).Opens := U.overEquivalence.functor.obj W
    (hU.isoSpec.hom.appIso V).inv
      ((((U.sheafRestrictSheafEquivOver (A := RingCat.{u})).app X.ringCatSheaf).inv.hom.app
        (op W)) (X.presheaf.map W.hom.op r)) =
      (Spec (X.presheaf.obj (op U))).presheaf.map
        (hU.isoSpec.hom.opensFunctor.obj V).leTop.op ((ΓSpecIso _).inv r) := by
  let V : (U : Scheme.{u}).Opens := U.overEquivalence.functor.obj W
  change (hU.isoSpec.hom.appIso V).inv _ = _
  apply (ConcreteCategory.bijective_of_isIso (hU.isoSpec.hom.appIso V).hom).injective
  simp only [Iso.inv_hom_id_apply]
  rw [Hom.appIso_hom']
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Hom.map_appLE]
  rw [← hU.isoSpec.hom.appLE_map (U := ⊤) (V := ⊤) (by simp) V.leTop.op]
  have htop : hU.isoSpec.hom.appLE ⊤ ⊤ (by simp) =
      (ΓSpecIso (X.presheaf.obj (op U))).hom ≫ U.topIso.inv := by
    change hU.isoSpec.hom.appTop ≫ U.toScheme.presheaf.map (𝟙 (op ⊤)) = _
    rw [U.toScheme.presheaf.map_id, Category.comp_id]
    exact hU.isoSpec_hom_appTop
  rw [htop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (X.presheaf.map W.hom.op ≫
    X.presheaf.map ((U.overEquivalence.unitIso.inv.app W).left.op)) r =
    (X.presheaf.map (eqToHom U.ι_image_top).op ≫
      X.presheaf.map (U.ι.opensFunctor.map V.leTop).op) r
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Affine sheafification takes multiplication by an affine section to multiplication
by its restrictions on the localized site. This is an underived statement about one module.
Source: Stacks Project, Tag 01I6, the associated-sheaf construction and its linearity;
Tag 06Z0, its termwise use in the derived affine equivalence.
(blueprint: lem-sc-affine-sheafification-scalar).

Proof: Write the affine sheafification as tilde followed by restriction along the affine
spectrum isomorphism and the inverse over-site equivalence. On tilde, multiplication by r
on a module sends a local fraction m/s to rm/s; this is multiplication by the image of r
in the local structure ring. Restriction along the spectrum isomorphism transports this
image by the structure-sheaf ring map. The defining affine spectrum isomorphism identifies
this transported section on each open V contained in U with the restriction of r from U
to V. The inverse over-site equivalence only reindexes V as an object of Over U and
transports the coefficient ring through the canonical restriction identification. Thus
every component of the mapped scalar identity is multiplication by the corresponding
component of overSections U r. The homModule action has precisely these components.
Extensionality of module-sheaf morphisms proves the equality. This fraction calculation
also holds for r = 0 and for the empty open, with the unique maps of zero rings. -/
theorem affine_perfect_sheafification_scalar (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) (M : ModuleCat.{u} (X.presheaf.obj (op U)))
    (r : X.presheaf.obj (op U)) :
    let B := (Over.forget U).op ⋙ X.sheaf.obj
    letI : Linear (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
      SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
    (affinePerfectSheafification X U hU).map (r • 𝟙 M) =
      PresheafOfModules.overSections (R := X.sheaf.obj) U r •
        𝟙 ((affinePerfectSheafification X U hU).obj M) := by
  dsimp only
  ext W x
  let V : (U : Scheme.{u}).Opens := U.overEquivalence.functor.obj W.unop
  let x' : Γ(tilde M, hU.isoSpec.hom.opensFunctor.obj V) := x
  change (tilde.map (r • 𝟙 M)).app (hU.isoSpec.hom.opensFunctor.obj V) x' =
    (hU.isoSpec.hom.appIso V).inv
      ((((U.sheafRestrictSheafEquivOver (A := RingCat.{u})).app X.ringCatSheaf).inv.hom.app
        W) (X.presheaf.map W.unop.hom.op r)) • x'
  rw [affine_scalar_coefficient X U hU r W.unop]
  exact tilde_scalar_sections (X.presheaf.obj (op U)) M r _ x'


end AlgebraicGeometry.Scheme
