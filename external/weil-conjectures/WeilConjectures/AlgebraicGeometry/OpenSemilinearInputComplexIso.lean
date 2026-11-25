/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Semilinear input stalk coordinates for an open subscheme

Source: Stacks Project, Tag 0098; Mathlib restrictStalkNatIso and its germ formulas.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open TopologicalSpace Opposite
namespace AlgebraicGeometry

/-- The inverse stalk ring map acts on germs through the inverse section-ring map. -/
private theorem inverse_stalkMap_germ
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    (inv (j.stalkMap x)) (X.presheaf.germ U x hx r) =
      Y.presheaf.germ (j ''ᵁ U) (j x) (by simpa) ((j.appIso U).inv r) := by
  apply (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1
  simp only [IsIso.inv_hom_id_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ U x hx r =
    ((j.appIso U).inv ≫ j.app _ ≫ X.presheaf.germ _ x _) r
  rw [Scheme.Hom.appIso_inv_app_assoc]
  exact (X.presheaf.germ_res_apply (eqToHom (j.preimage_image_eq U)) x
    (by simpa) r).symm

/-- The additive restriction-stalk comparison is semilinear over the inverse stalk map. -/
private theorem restriction_stalk_smul
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules)
    (r : X.presheaf.stalk x)
    (m : ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x) :
    (Scheme.Modules.restrictStalkNatIso j x).hom.app M (r • m) =
      (inv (j.stalkMap x)) r •
        (show M.presheaf.stalk (j x) from
          (Scheme.Modules.restrictStalkNatIso j x).hom.app M m) := by
  let N := (Scheme.Modules.restrictFunctor j).obj M
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := N.presheaf.exists_germ_eq m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← N.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) N.val]
  rw [inverse_stalkMap_germ]
  have hg (s : Γ(N, U ⊓ V)) :
      (Scheme.Modules.restrictStalkNatIso j x).hom.app M
        (N.presheaf.germ (U ⊓ V) x hx s) =
        M.presheaf.germ (j ''ᵁ (U ⊓ V)) (j x) (by simpa) s :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x M hx) s
  erw [hg, hg]
  exact PresheafOfModules.germ_smul (R := Y.presheaf) M.val _ _ _ _ _

/-- The canonical additive open restriction comparison is a semilinear chain iso,
with the same-germ component formula, including transport of the ambient point.

Proof: transport the point equality by equality induction, reducing to y=x.val.
Whisker overFunctorEquiv by the restricted additive stalk functor and compose
with restrictStalkNatIso. Map this natural isomorphism to complexes to get alpha;
naturality with respect to the differentials is built into this construction.
The overFunctorEquiv component is linear on stalks. For restrictStalkNatIso,
represent the scalar and the module element by section germs on a common open.
The inverse inclusion stalk map sends the ring germ to the inverse section-ring
map's germ. germ_smul and germ_restrictStalkNatIso_hom_app therefore prove
semilinearity. Finally stalkIso_inv identifies this inverse ring map with the
specified ring equivalence. The component formula follows by unfolding the
mapped natural isomorphism, and equality induction gives the stated transport.
No resolution, flatness, boundedness or nonzero-ring hypothesis is used.
Source: Stacks Project, Tag 0098, and Mathlib restrictStalkNatIso;
the proved inverse_stalkMap_germ and restriction_stalk_smul argument in
Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso.
(blueprint: lem-pc-open-semilinear-input-complex-iso). -/
theorem exists_openSemilinearInputComplexIso (X : Scheme.{u}) (U : X.Opens) (x : U.toScheme) (y : X)
    (hxy : x.val = y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    letI : (schemeOpenRestriction X U).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let L₀ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x
    let L₁ := RingedSpace.moduleStalkFunctor X.toRingedSpace y
    let F₀ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk x)) AddCommGrpCat.{u}
    let F₁ := forget₂ (ModuleCat.{u} (X.presheaf.stalk y)) AddCommGrpCat.{u}
    let K₀ := (L₀.mapHomologicalComplex (.up ℤ)).obj
      (((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P)
    let K₁ := (L₁.mapHomologicalComplex (.up ℤ)).obj P
    let eA := (U.stalkIso x ≪≫ X.presheaf.stalkCongr (.of_eq hxy)).commRingCatIsoToRingEquiv
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (L₀ ⋙ F₀) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι x
    ∃ α : (F₀.mapHomologicalComplex (.up ℤ)).obj K₀ ≅
        (F₁.mapHomologicalComplex (.up ℤ)).obj K₁,
      (∀ (n : ℤ) (a : U.toScheme.presheaf.stalk x) (q : K₀.X n),
        α.hom.f n (a • q) = eA a • (show K₁.X n from α.hom.f n q)) ∧
      ∀ n : ℤ, α.hom.f n = γ.hom.app (P.X n) ≫
        ((show X.Modules from P.X n).presheaf.stalkCongr (.of_eq hxy)).hom := by
  subst y
  let := schemeOpenRestriction_additive X U
  let L₀ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x
  let F₀ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk x)) AddCommGrpCat.{u}
  let L₁ := RingedSpace.moduleStalkFunctor X.toRingedSpace x.val
  let F₁ := forget₂ (ModuleCat.{u} (X.presheaf.stalk x.val)) AddCommGrpCat.{u}
  let γ : schemeOpenRestriction X U ⋙ L₀ ⋙ F₀ ≅ L₁ ⋙ F₁ :=
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (L₀ ⋙ F₀) ≪≫
    Scheme.Modules.restrictStalkNatIso U.ι x
  have : (schemeOpenRestriction X U ⋙ L₀ ⋙ F₀).PreservesZeroMorphisms := by
    infer_instance
  have : (L₁ ⋙ F₁).PreservesZeroMorphisms := by infer_instance
  refine ⟨(NatIso.mapHomologicalComplex γ (.up ℤ)).app P, ?_, ?_⟩
  · intro n a q
    change γ.hom.app (P.X n) (a • q) = _
    dsimp only [γ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.comp_map, AddCommGrpCat.comp_apply]
    change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app (P.X n)
        ((L₀.map ((Scheme.Modules.overFunctorEquiv U).hom.app (P.X n))) (a • q)) = _
    rw [(L₀.map ((Scheme.Modules.overFunctorEquiv U).hom.app (P.X n))).hom.map_smul]
    let e := (U.stalkIso x ≪≫ X.presheaf.stalkCongr
      (.of_eq (Eq.refl x.val))).commRingCatIsoToRingEquiv
    have he : e.toRingHom = (inv (U.ι.stalkMap x)).hom := by
      change ((U.stalkIso x).hom ≫
        (X.presheaf.stalkCongr (.of_eq (Eq.refl x.val))).hom).hom = _
      simp only [TopCat.Presheaf.stalkCongr_hom,
        TopCat.Presheaf.stalkSpecializes_refl, Category.comp_id]
      apply congrArg
        (fun f : U.toScheme.presheaf.stalk x ⟶ X.presheaf.stalk x.val => f.hom)
      apply (cancel_mono (U.ι.stalkMap x)).1
      simp only [IsIso.inv_hom_id]
      simpa only [Scheme.Opens.stalkIso_inv] using (U.stalkIso x).hom_inv_id
    change _ = (e.toRingHom a) • _
    rw [he]
    exact restriction_stalk_smul U.ι x (P.X n) a _
  · intro n
    simp [TopCat.Presheaf.stalkCongr, γ]
    rfl

end AlgebraicGeometry
