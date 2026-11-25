/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-! Component data for exterior presheaf pullback. -/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The old wedge is alternating for the scalar action transported through `e.inv`. -/
private noncomputable def ringTransportWedge (R S : CommRingCat.{v}) (e : R ≅ S)
    (A : ModuleCat.{v} R) (n : ℕ) :
    ((ModuleCat.restrictScalars e.inv.hom).obj A) [⋀^Fin n]→ₗ[S]
      (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)) where
  toFun a := exteriorPower.ιMulti R n a
  map_update_add' := by
    intro _ a i x y
    exact (exteriorPower.ιMulti R n (M := A)).map_update_add a i x y
  map_update_smul' := by
    intro _ a i r x
    exact (exteriorPower.ιMulti R n (M := A)).map_update_smul a i (e.inv r) x
  map_eq_zero_of_eq' := by
    intro a i j hij hne
    exact (exteriorPower.ιMulti R n (M := A)).map_eq_zero_of_eq a hij hne

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Extend the old wedge by the universal property over the new coefficient ring. -/
private noncomputable def ringTransportMap (R S : CommRingCat.{v}) (e : R ≅ S)
    (A : ModuleCat.{v} R) (n : ℕ) :
    ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A)) ⟶
      (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A)))
    (Y := (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)))
    (exteriorPower.alternatingMapLinearEquiv
      (N := (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)))
      (ringTransportWedge R S e A n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The transported linear map has its defining value on pure wedges. -/
private theorem ringTransportMap_wedge (R S : CommRingCat.{v}) (e : R ≅ S)
    (A : ModuleCat.{v} R) (n : ℕ)
    (a : Fin n → (ModuleCat.restrictScalars e.inv.hom).obj A) :
    ringTransportMap R S e A n (exteriorPower.ιMulti S n a) =
      exteriorPower.ιMulti R n a :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (N := (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)))
    (ringTransportWedge R S e A n) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pure wedges still detect equality after scalar transport by a ring isomorphism. -/
private theorem ringTransport_ext (R S : CommRingCat.{v}) (e : R ≅ S)
    (A : ModuleCat.{v} R) (n : ℕ) (B : ModuleCat.{v} S)
    (f g : (ModuleCat.restrictScalars e.inv.hom).obj
      (ModuleCat.of R (⋀[R]^n A)) ⟶ B)
    (h : ∀ a : Fin n → A, f (exteriorPower.ιMulti R n a) =
      g (exteriorPower.ιMulti R n a)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := A))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h a
  | zero => exact (map_zero f.hom).trans (map_zero g.hom).symm
  | add x y _ _ hx hy =>
    exact (map_add f.hom x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add g.hom x y).symm)
  | smul r x _ hx =>
    have he : e.inv (e.hom r) = r := CategoryTheory.congr_fun e.hom_inv_id r
    have hs : r • x = (e.hom r) •
        (x : (ModuleCat.restrictScalars e.inv.hom).obj
          (ModuleCat.of R (⋀[R]^n A))) := by
      change r • x = e.inv (e.hom r) • x
      rw [he]
    rw [hs, f.hom.map_smul, g.hom.map_smul, hx]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The new wedge is alternating over the old ring via `e.hom`. -/
private noncomputable def ringTransportInverseWedge
    (R S : CommRingCat.{v}) (e : R ≅ S) (A : ModuleCat.{v} R) (n : ℕ) :
    A [⋀^Fin n]→ₗ[R] (ModuleCat.restrictScalars e.hom.hom).obj
      (ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A))) where
  toFun a := exteriorPower.ιMulti S n
    (M := (ModuleCat.restrictScalars e.inv.hom).obj A) a
  map_update_add' := by
    intro _ a i x y
    exact (exteriorPower.ιMulti S n
      (M := (ModuleCat.restrictScalars e.inv.hom).obj A)).map_update_add a i x y
  map_update_smul' := by
    intro _ a i r x
    have he : e.inv (e.hom r) = r := CategoryTheory.congr_fun e.hom_inv_id r
    change exteriorPower.ιMulti S n
        (M := (ModuleCat.restrictScalars e.inv.hom).obj A)
        (Function.update a i (r • x)) =
      e.hom r • exteriorPower.ιMulti S n
        (M := (ModuleCat.restrictScalars e.inv.hom).obj A) (Function.update a i x)
    simpa only [ModuleCat.restrictScalars.smul_def, he] using
      (exteriorPower.ιMulti S n
        (M := (ModuleCat.restrictScalars e.inv.hom).obj A)).map_update_smul a i (e.hom r) x
  map_eq_zero_of_eq' := by
    intro a i j hij hne
    exact (exteriorPower.ιMulti S n
      (M := (ModuleCat.restrictScalars e.inv.hom).obj A)).map_eq_zero_of_eq a hij hne

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The `S`-linear map from the old exterior power to the new one extending the new wedge. -/
private noncomputable def ringTransportInverse
    (R S : CommRingCat.{v}) (e : R ≅ S) (A : ModuleCat.{v} R) (n : ℕ) :
    (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)) ⟶
      ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A)) := by
  let l := exteriorPower.alternatingMapLinearEquiv
    (N := (ModuleCat.restrictScalars e.hom.hom).obj
      (ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A))))
    (ringTransportInverseWedge R S e A n)
  exact ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)))
    (Y := ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A)))
    { toFun := l
      map_add' := l.map_add
      map_smul' := by
        intro r x
        have he : e.hom (e.inv r) = r := CategoryTheory.congr_fun e.inv_hom_id r
        exact (l.map_smul (e.inv r) x).trans (by
          change e.hom (e.inv r) • l x = r • l x
          rw [he]) }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse transport sends an old pure wedge to its new pure wedge. -/
private theorem ringTransportInverse_wedge
    (R S : CommRingCat.{v}) (e : R ≅ S) (A : ModuleCat.{v} R) (n : ℕ)
    (a : Fin n → A) :
    ringTransportInverse R S e A n (exteriorPower.ιMulti R n a) =
      exteriorPower.ιMulti S n (M := (ModuleCat.restrictScalars e.inv.hom).obj A) a :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (N := (ModuleCat.restrictScalars e.hom.hom).obj
      (ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A))))
    (ringTransportInverseWedge R S e A n) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism of `S`-modules between the old and the new exterior power. -/
private noncomputable def ringTransportIso
    (R S : CommRingCat.{v}) (e : R ≅ S) (A : ModuleCat.{v} R) (n : ℕ) :
    (ModuleCat.restrictScalars e.inv.hom).obj (ModuleCat.of R (⋀[R]^n A)) ≅
      ModuleCat.of S (⋀[S]^n ((ModuleCat.restrictScalars e.inv.hom).obj A)) where
  hom := ringTransportInverse R S e A n
  inv := ringTransportMap R S e A n
  hom_inv_id := by
    apply ringTransport_ext R S e A n
    intro a
    change ringTransportMap R S e A n
      (ringTransportInverse R S e A n (exteriorPower.ιMulti R n a)) = _
    rw [ringTransportInverse_wedge, ringTransportMap_wedge]
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext (R := S)
    apply DFunLike.ext
    intro a
    change ringTransportInverse R S e A n
      (ringTransportMap R S e A n (exteriorPower.ιMulti S n a)) = _
    rw [ringTransportMap_wedge]
    exact ringTransportInverse_wedge R S e A n a

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The sectionwise inverse ring isomorphisms of an open immersion. -/
private noncomputable def openRingRestriction {X Y : Scheme.{v}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    X.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ Y.ringCatSheaf.obj :=
  Functor.whiskerRight
    (show X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf from
      { app V := (f.appIso V.unop).inv }) (forget₂ CommRingCat RingCat)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restrict to image opens and transport scalars along the inverse section isomorphism. -/
private noncomputable def openPresheafRestriction {X Y : Scheme.{v}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    _root_.PresheafOfModules.{v} Y.ringCatSheaf.obj ⥤
      _root_.PresheafOfModules.{v} X.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (openRingRestriction f)

private local instance restrictedSectionModule {X : Scheme.{v}}
    (M : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj)
    {V W : X.Opens} (i : W ⟶ V) :
    Module Γ(X, W)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i.op).hom).obj
        (M.obj (Opposite.op W))) :=
  inferInstanceAs (Module Γ(X, W) (M.obj (Opposite.op W)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The presheaf analogue of Mathlib's `restrictAdjunction`: its unit is restriction to
`f ᵁ (f ⁻¹ᵁ V)`, and its counit restricts along `f ⁻¹ᵁ (f ᵁ V) = V`. -/
private noncomputable def openPresheafRestrictionAdjunction {X Y : Scheme.{v}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    openPresheafRestriction f ⊣ PresheafOfModules.pushforward.{v} f.toRingCatSheafHom.hom where
  unit :=
    { app M :=
        { app V := ModuleCat.ofHom
            (X := M.obj V)
            (Y := ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
              ((openPresheafRestriction f).obj M)).obj V)
            { toFun := M.map (homOfLE (f.image_preimage_le V.unop)).op
              map_add' := (M.map _).hom.map_add
              map_smul' := by
                intro r x
                change M.map (homOfLE (f.image_preimage_le V.unop)).op (r • x) =
                  (f.appIso (f ⁻¹ᵁ V.unop)).inv (f.app V.unop r) •
                    (M.map (homOfLE (f.image_preimage_le V.unop)).op x :
                      M.obj (Opposite.op (f ''ᵁ f ⁻¹ᵁ V.unop)))
                rw [M.map_smul]
                rw [← ConcreteCategory.comp_apply, f.app_appIso_inv]
                rfl }
          naturality := by
            intro V W g
            ext x
            change M.map (homOfLE (f.image_preimage_le W.unop)).op (M.map g x) =
              M.map (f.opensFunctor.op.map ((TopologicalSpace.Opens.map f.base).op.map g))
                (M.map (homOfLE (f.image_preimage_le V.unop)).op x)
            erw [← M.map_comp_apply, ← M.map_comp_apply]
            exact M.congr_map_apply (Subsingleton.elim _ _) x }
      naturality := by
        intro M N g
        ext V x
        exact (PresheafOfModules.naturality_apply g
          (homOfLE (f.image_preimage_le V.unop)).op x).symm }
  counit :=
    { app M :=
        { app V := ModuleCat.ofHom
            (X := ((openPresheafRestriction f).obj
              ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj M)).obj V)
            (Y := M.obj V)
            { toFun := M.map (eqToHom (f.preimage_image_eq V.unop).symm).op
              map_add' := by
                intro x y
                change ↑(M.obj (Opposite.op (f ⁻¹ᵁ f ''ᵁ V.unop))) at x y
                exact (M.map (eqToHom (f.preimage_image_eq V.unop).symm).op).hom.map_add x y
              map_smul' := by
                intro r x
                change ↑(M.obj (Opposite.op (f ⁻¹ᵁ f ''ᵁ V.unop))) at x
                change M.map (eqToHom (f.preimage_image_eq V.unop).symm).op
                    ((f.app _ ((f.appIso V.unop).inv r)) •
                      (x : M.obj (Opposite.op (f ⁻¹ᵁ f ''ᵁ V.unop)))) =
                  r • (M.map (eqToHom (f.preimage_image_eq V.unop).symm).op x : M.obj V)
                rw [M.map_smul]
                change X.presheaf.map (eqToHom (f.preimage_image_eq V.unop).symm).op
                    (f.app _ ((f.appIso V.unop).inv r)) • _ = r • _
                rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
                  f.appIso_inv_app_presheafMap]
                rfl }
          naturality := by
            intro V W g
            ext x
            change ↑(M.obj (Opposite.op (f ⁻¹ᵁ f ''ᵁ V.unop))) at x
            change M.map (eqToHom (f.preimage_image_eq W.unop).symm).op
                (M.map ((TopologicalSpace.Opens.map f.base).op.map
                  (f.opensFunctor.op.map g)) x) =
              M.map g (M.map (eqToHom (f.preimage_image_eq V.unop).symm).op x)
            erw [← M.map_comp_apply, ← M.map_comp_apply]
            exact M.congr_map_apply (Subsingleton.elim _ _) x }
      naturality := by
        intro M N g
        ext V x
        change ↑(M.obj (Opposite.op (f ⁻¹ᵁ f ''ᵁ V.unop))) at x
        exact (PresheafOfModules.naturality_apply g
          (eqToHom (f.preimage_image_eq V.unop).symm).op x).symm }
  left_triangle_components M := by
    ext V x
    change ↑(M.obj (f.opensFunctor.op.obj V)) at x
    change M.map (f.opensFunctor.op.map
        (eqToHom (f.preimage_image_eq V.unop).symm).op)
        (M.map (homOfLE (f.image_preimage_le (f ''ᵁ V.unop))).op x) = x
    erw [← M.map_comp_apply]
    exact (M.congr_map_apply (Subsingleton.elim _ _) x).trans
      (CategoryTheory.congr_fun (M.map_id (f.opensFunctor.op.obj V)) x)
  right_triangle_components M := by
    ext V x
    change ↑(M.obj ((TopologicalSpace.Opens.map f.base).op.obj V)) at x
    change M.map (eqToHom (f.preimage_image_eq (f ⁻¹ᵁ V.unop)).symm).op
        (M.map ((TopologicalSpace.Opens.map f.base).op.map
          (homOfLE (f.image_preimage_le V.unop)).op) x) = x
    erw [← M.map_comp_apply]
    exact (M.congr_map_apply (Subsingleton.elim _ _) x).trans
      (CategoryTheory.congr_fun (M.map_id ((TopologicalSpace.Opens.map f.base).op.obj V)) x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Expose the defining wedge formula of the exterior-power restriction. -/
private theorem restriction_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {V W : X.Opensᵒᵖ} (f : V ⟶ W) (a : Fin n → M.val.obj V) :
    ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n).map f)
      (exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V) a) =
        exteriorPower.ιMulti (X.presheaf.obj W) n (M := M.val.obj W)
          (fun i ↦ M.val.map f (a i)) :=
  (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val n f) a

/-- Identify restricted sections before applying the exterior-power functor. -/
private noncomputable def openSectionTransportIso {X : Scheme.{v}} (M : X.Modules)
    (U : X.Opens) (V : U.toScheme.Opensᵒᵖ) :
    (ModuleCat.restrictScalars (U.ι.appIso V.unop).inv.hom).obj
      (M.val.obj (U.ι.opensFunctor.op.obj V)) ≅ (M.restrict U.ι).val.obj V :=
  Iso.refl _

/-- Scalar transport on exterior powers, expressed in the actual section modules. -/
private noncomputable def openExteriorComponent {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (U : X.Opens) (V : U.toScheme.Opensᵒᵖ) :
    ((openPresheafRestriction U.ι).obj
      (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).obj V ≅
      (_root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n).obj V :=
  ringTransportIso
    (X.presheaf.obj (U.ι.opensFunctor.op.obj V)) (U.toScheme.presheaf.obj V)
    (U.ι.appIso V.unop) (M.val.obj (U.ι.opensFunctor.op.obj V)) n ≪≫
      (ModuleCat.exteriorPower.functor (U.toScheme.presheaf.obj V) n).mapIso
        (openSectionTransportIso M U V)

/-- The section comparison takes a pure wedge to the same sections after restriction. -/
private theorem openExteriorComponent_wedge {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (U : X.Opens) (V : U.toScheme.Opensᵒᵖ)
    (a : Fin n → M.val.obj (U.ι.opensFunctor.op.obj V)) :
    (openExteriorComponent M n U V).hom
      (exteriorPower.ιMulti (X.presheaf.obj (U.ι.opensFunctor.op.obj V)) n a) =
      exteriorPower.ιMulti (U.toScheme.presheaf.obj V) n
        (M := (M.restrict U.ι).val.obj V) a := by
  change ModuleCat.exteriorPower.map (openSectionTransportIso M U V).hom n
      (ringTransportInverse
        (X.presheaf.obj (U.ι.opensFunctor.op.obj V)) (U.toScheme.presheaf.obj V)
        (U.ι.appIso V.unop) (M.val.obj (U.ι.opensFunctor.op.obj V)) n
        (exteriorPower.ιMulti (X.presheaf.obj (U.ι.opensFunctor.op.obj V)) n a)) = _
  rw [ringTransportInverse_wedge]
  exact ModuleCat.exteriorPower.map_mk (openSectionTransportIso M U V).hom a

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For an open `U ⊆ X`, the presheaf pullback of `⋀ⁿ M` along `U.ι` and `⋀ⁿ (M|_U)` have
isomorphic sections over every open, compatibly with restriction. -/
theorem exteriorPresheaf_open_pullback_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    ∃ (app : ∀ V : U.toScheme.Opensᵒᵖ,
      ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
        (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).obj V ≅
        (_root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n).obj V),
      ∀ {V W : U.toScheme.Opensᵒᵖ} (f : V ⟶ W),
        ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
          (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).map f ≫
            (ModuleCat.restrictScalars
              ((U.toScheme.ringCatSheaf.obj.map f).hom)).map (app W).hom =
          (app V).hom ≫
            (_root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n).map f := by
  let P := (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)
  let Q := (openPresheafRestriction U.ι).obj P
  let e₀ : (PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj P ≅ Q :=
    ((openPresheafRestrictionAdjunction U.ι).leftAdjointUniq
      (PresheafOfModules.pullbackPushforwardAdjunction.{v}
        U.ι.toRingCatSheafHom.hom)).symm.app P
  let e₁ : Q ≅ (_root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n) :=
    PresheafOfModules.isoMk (openExteriorComponent M n U) (by
      intro V W f
      apply ringTransport_ext
        (X.presheaf.obj (U.ι.opensFunctor.op.obj V)) (U.toScheme.presheaf.obj V)
        (U.ι.appIso V.unop) (M.val.obj (U.ι.opensFunctor.op.obj V)) n
      intro a
      change (openExteriorComponent M n U W).hom
          (P.map (U.ι.opensFunctor.op.map f)
            (exteriorPower.ιMulti (X.presheaf.obj (U.ι.opensFunctor.op.obj V)) n a)) =
        ((_root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n).map f)
          ((openExteriorComponent M n U V).hom
            (exteriorPower.ιMulti (X.presheaf.obj (U.ι.opensFunctor.op.obj V)) n a))
      rw [restriction_wedge, openExteriorComponent_wedge, openExteriorComponent_wedge]
      exact (restriction_wedge (M.restrict U.ι) n f a).symm)
  let e := e₀ ≪≫ e₁
  exact ⟨fun V ↦ (PresheafOfModules.evaluation _ V).mapIso e, fun f ↦ e.hom.naturality f⟩

end AlgebraicGeometry.Scheme.Modules
