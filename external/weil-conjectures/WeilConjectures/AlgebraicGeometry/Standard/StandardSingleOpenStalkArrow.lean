/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleOpenDerivedArrow
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local comparison factors

Source: Stacks Project, perfect.tex, Tags 0DJ7 and 0DJ9;
cohomology.tex, Tags 06YB and 0D5S.
(blueprint: lem-pc-standard-single-open-stalk-arrow).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Expose the existing presheaf-module stalk instance through `Scheme.Modules.presheaf`. -/
private local instance schemeModuleStalkModule {X : Scheme.{u}} (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  inferInstanceAs (Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
      (M.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ _ _)).presheaf x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The additive stalk comparison, viewed as a linear map after restriction of scalars. -/
private noncomputable def restrictionStalkLinearMap
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ⟶
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        ((Scheme.Modules.restrictFunctor j).obj M)))
    (Y := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M)
    { toFun := (Scheme.Modules.restrictStalkNatIso j x).hom.app M
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change (Scheme.Modules.restrictStalkNatIso j x).hom.app M
            ((j.stalkMap x) r •
              (show ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x from m)) =
          r • (show M.presheaf.stalk (j x) from
            (Scheme.Modules.restrictStalkNatIso j x).hom.app M m)
        rw [restriction_stalk_smul]
        simp }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The linear stalk comparison is invertible because its underlying additive map is. -/
private noncomputable def restrictionStalkLinearIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ≅
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M := by
  let a := restrictionStalkLinearMap j x M
  have : IsIso a :=
    (ConcreteCategory.isIso_iff_bijective a).mpr
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.Modules.restrictStalkNatIso j x).hom.app M))
  exact asIso a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The linear stalk comparisons are natural in the module sheaf. -/
private noncomputable def restrictionStalkLinearNatIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    (Scheme.Modules.restrictFunctor j ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x) ⋙
        ModuleCat.restrictScalars (j.stalkMap x).hom ≅
      RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x) :=
  NatIso.ofComponents (restrictionStalkLinearIso j x) (by
    intro M N f
    ext m
    exact ConcreteCategory.congr_hom
      ((Scheme.Modules.restrictStalkNatIso j x).hom.naturality f) m)

private theorem transportArrow
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (G : D ⥤ E) (T : C ⥤ E) (c : R ⋙ G ≅ T)
    {X Y : C} {X0 Y0 : D} (f : X ⟶ Y) (f0 : X0 ⟶ Y0)
    (s : R.obj X ≅ X0) (t : R.obj Y ≅ Y0)
    (h : R.map f ≫ t.hom = s.hom ≫ f0) :
    T.map f = ((c.app X).symm ≪≫ G.mapIso s).hom ≫ G.map f0 ≫
      ((G.mapIso t).symm ≪≫ c.app Y).hom := by
  apply (cancel_epi (c.app X).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc]
  have hn : G.map (R.map f) ≫ (c.app Y).hom =
      (c.app X).hom ≫ T.map f := c.hom.naturality f
  rw [← hn]
  rw [← G.map_comp_assoc, ← h]
  simp only [G.map_comp, Category.assoc, ← G.map_comp_assoc, Iso.hom_inv_id,
    G.map_id, Category.id_comp]

/-- Restriction of the canonical single-module base-change arrow to target opens,
then transport of its stalk back to the original local ring.

Proof: restrict the base direct image to S and the base-changed direct image to V.
Direct image commutes with restriction to a full inverse-image open: identify the
underived section functors, and derive that identification using exact restriction.
The pullback square over V identifies the restricted source with the pullback over
S. The tensor-pullback composition isomorphism identifies the restricted coefficient
module with the pullback of MS. Derived pullback commutes with these restrictions,
by the exact open pullback and its composition comparison. The base-change arrow
is the unit followed by direct image of the coefficient map followed by the counit.
The existing restricted_base_change_compatibility theorem applies to the pinned
single-module comparisons: the adjunction comparison and its inverse cancel,
identifying these comparisons with picardTermwiseSingleMap. It gives conjugacy
of the two derived arrows, before applying homology. Apply degree-n homology and
use exactness of open restriction to pass to restricted cohomology sheaves. Taking
the stalk at xV, the open-immersion stalk isomorphism and restriction of scalars
along its inverse identify these stalks with the original stalk at a. Composing
these identifications gives s, t and the displayed equality. This does not use
flatness, quasi-coherence, affineness, or a representative complex. Empty V admits
no a with hV; for top opens the same comparisons reduce to the identity.
Source: Stacks Project, perfect.tex, equation-bc (Tag 0DJ7), and
Lemma lemma-single-complex-base-change (Tag 0DJ9), locality paragraph.
(blueprint: lem-pc-standard-single-open-stalk-arrow). -/
theorem standardSingle_open_stalk_arrow
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hV : a ∈ V) (hVS : V ≤ g ⁻¹ᵁ S) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let xV : V.toScheme := ⟨a, hV⟩
    let F := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace xV ⋙
      ModuleCat.restrictScalars (V.stalkIso xV).inv.hom
    let pS := p ∣_ S
    let MS := M.restrict (p ⁻¹ᵁ S).ι
    let j := g.resLE S V hVS
    ∀ n : ℤ,
      ∃ (s : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
          ((DerivedCategory.homologyFunctor _ n).obj
            ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
              ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
          F.obj ((DerivedCategory.homologyFunctor _ n).obj
            ((derivedPullback j).obj ((schemeDerivedDirectImage pS).obj
              ((DerivedCategory.singleFunctor _ 0).obj MS)))))
        (t : F.obj ((DerivedCategory.homologyFunctor _ n).obj
            ((schemeDerivedDirectImage (pullback.snd pS j)).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (Scheme.Modules.tensorPullbackObj (pullback.fst pS j) MS)))) ≅
          (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
            ((DerivedCategory.homologyFunctor _ n).obj
              ((schemeDerivedDirectImage (pullback.snd p g)).obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
        (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
            ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
          s.hom ≫ F.map ((DerivedCategory.homologyFunctor _ n).map
            (standardSingleBaseChangeMap pS MS j)) ≫ t.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  intro xV F pS MS j n
  let R := (schemeOpenRestriction A V).mapDerivedCategory
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings A.toRingedSpace)) n
  let HV := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) n
  let T := RingedSpace.moduleStalkFunctor A.toRingedSpace a
  let e : schemeOpenRestriction A V ⋙ F ≅ T := by
    have hρ : (V.stalkIso xV).inv.hom = (V.ι.stalkMap xV).hom := by
      rw [Scheme.Opens.stalkIso_inv]
    dsimp only [F]
    rw [hρ]
    exact Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv V)
      (RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace xV ⋙
        ModuleCat.restrictScalars (V.ι.stalkMap xV).hom) ≪≫
      restrictionStalkLinearNatIso V.ι xV
  let c : R ⋙ HV ⋙ F ≅ H ⋙ T :=
    Functor.isoWhiskerRight
      ((schemeOpenRestriction A V).mapDerivedCategoryHomologyFunctorIso n).symm F ≪≫
      Functor.isoWhiskerLeft H e
  obtain ⟨s, t, h⟩ := standardSingle_open_derived_arrow p M g S V hVS
  let G := HV ⋙ F
  refine ⟨(c.app _).symm ≪≫ G.mapIso s,
    (G.mapIso t).symm ≪≫ c.app _, ?_⟩
  exact transportArrow R G (H ⋙ T) c (standardSingleBaseChangeMap p M g)
    (standardSingleBaseChangeMap pS MS j) s t h

end
end AlgebraicGeometry
