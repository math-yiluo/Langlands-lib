/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.CategoryTheory.Abelian.Images

import WeilConjectures.AlgebraicGeometry.StalkTensorMultiplicationRange
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-! # Image of multiplication by a principal closed-subscheme ideal

Source: Stacks Project, More on Morphisms, Tag 0EX8, divisibility step;
Modules, Tag 08KS, ideal-multiplication description.
(blueprint: lem-sc-principal-quotient-multiplication-image)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem hom_zero_of_stalk_zero {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N)
    (h : ∀ x : X, (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f = 0) :
    f = 0 := by
  ext U m
  apply TopCat.Presheaf.section_ext
    (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) U _ _
  intro x hx
  have hh := ConcreteCategory.congr_hom (h x)
    (TopCat.Presheaf.germ M.val.presheaf U x hx m)
  change RingedSpace.stalkAddMap X.toRingedSpace x f
    (TopCat.Presheaf.germ M.val.presheaf U x hx m) = 0 at hh
  dsimp only [RingedSpace.stalkAddMap] at hh
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hh
  change TopCat.Presheaf.germ N.val.presheaf U x hx (f.val.app (Opposite.op U) m) =
    TopCat.Presheaf.germ N.val.presheaf U x hx 0
  rw [map_zero]
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem image_iso_of_stalk_range {X : Scheme.{u}} {M N F : X.Modules}
    (a : M ⟶ F) (b : N ⟶ F)
    (h : ∀ x : X,
      LinearMap.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map a).hom =
        LinearMap.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map b).hom) :
    ∃ e : image a ≅ image b, e.hom ≫ image.ι b = image.ι a := by
  have vanish {P Q : X.Modules} (c : P ⟶ F) (d : Q ⟶ F)
      (hc : ∀ x : X,
        LinearMap.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map c).hom =
          LinearMap.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map d).hom) :
      c ≫ cokernel.π d = 0 := by
    apply hom_zero_of_stalk_zero
    intro x
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    rw [Functor.map_comp]
    ext z
    obtain ⟨w, hw⟩ := (hc x) ▸
      (show S.map c z ∈ LinearMap.range (S.map c).hom from ⟨z, rfl⟩)
    change S.map (cokernel.π d) (S.map c z) = 0
    rw [← hw]
    have hh := ConcreteCategory.congr_hom
      (show S.map d ≫ S.map (cokernel.π d) = 0 by
        rw [← S.map_comp, cokernel.condition, S.map_zero]) w
    exact hh
  have hab := vanish a b h
  have hba := vanish b a (fun x ↦ (h x).symm)
  have lift {P Q : X.Modules} (c : P ⟶ F) (d : Q ⟶ F)
      (hc : c ≫ cokernel.π d = 0) :
      ∃ l : image c ⟶ image d, l ≫ image.ι d = image.ι c := by
    have hi : image.ι c ≫ cokernel.π d = 0 := by
      apply (cancel_epi (factorThruImage c)).mp
      simpa only [← Category.assoc, image.fac, comp_zero] using hc
    refine ⟨kernel.lift (cokernel.π d) (image.ι c) hi ≫
      (Abelian.imageIsoImage d).hom, ?_⟩
    rw [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι]
  obtain ⟨l, hl⟩ := lift a b hab
  obtain ⟨r, hr⟩ := lift b a hba
  refine ⟨⟨l, r, ?_, ?_⟩, hl⟩
  · apply (cancel_mono (image.ι a)).mp
    simp only [Category.assoc, hr, hl, Category.id_comp]
  · apply (cancel_mono (image.ι b)).mp
    simp only [Category.assoc, hl, hr, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_smulHom {X : Scheme.{u}} (F : X.Modules) (r : Γ(X, ⊤)) (x : X)
    (m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map (F.smulHom r) m =
      X.presheaf.germ ⊤ x (by trivial) r • m := by
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  change RingedSpace.stalkAddMap X.toRingedSpace x (F.smulHom r)
    (TopCat.Presheaf.germ F.val.presheaf U x hx m) = _
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ F.val.presheaf U x hx ((F.smulHom r).app U m) = _
  rw [smulHom_app_apply, PresheafOfModules.germ_smul (R := X.presheaf),
    X.presheaf.germ_res_apply]


set_option backward.isDefEq.respectTransparency false in
private theorem principal_quotient_affine_ideal
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (π : A) (U : X.affineOpens) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π}))))
    let r := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)
    i.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE (le_top (a := U.1))).op r} := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π})))
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  have hk : RingHom.ker q.appTop.hom = (Ideal.span {π}).map e.symm.toRingHom := by
    calc
      _ = (Ideal.span {π}).comap e.toRingHom := by
        have hn := Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π})))
        have he := RingHom.ker_equiv_comp q.appTop.hom
          (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ Ideal.span {π}))).commRingCatIsoToRingEquiv
        rw [RingEquiv.toRingHom_eq_coe,
          Iso.commRingCatIsoToRingEquiv_toRingHom] at he
        change RingHom.ker (q.appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ Ideal.span {π}))).hom).hom = _ at he
        rw [hn] at he
        rw [← he, CommRingCat.hom_comp, ← RingHom.comap_ker]
        change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {π}))).comap e.toRingHom = _
        rw [Ideal.mk_ker]
      _ = _ := (Ideal.map_comap_of_equiv e.symm).symm
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  dsimp only
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ideal_comap_appLE q.ker f
      ⟨⊤, isAffineOpen_top _⟩ U (by simp),
    Scheme.ker_of_isAffine,
    Scheme.IdealSheafData.ofIdealTop_ideal]
  rw [hk]
  simp only [Ideal.map_span, Set.image_singleton]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private theorem principal_quotient_stalk_ideal
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (π : A) (x : X)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π}))))
    let r := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)
    LinearMap.range
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map i.ker.toModulesι ≫
        e.hom).hom = Ideal.span {X.presheaf.germ ⊤ x (by trivial) r} := by
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {π}))))
  let r := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have hg (U : X.Opens) (hx : x ∈ U) (m : Γ(i.ker.toModules, U)) :
      (S.map i.ker.toModulesι ≫ e.hom)
        (TopCat.Presheaf.germ i.ker.toModules.val.presheaf U x hx m) =
      X.presheaf.germ U x hx (i.ker.toModulesι.app U m) := by
    change e.hom (RingedSpace.stalkAddMap X.toRingedSpace x i.ker.toModulesι _) = _
    dsimp only [RingedSpace.stalkAddMap]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change e.hom (TopCat.Presheaf.germ
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf U x hx
      (i.ker.toModulesι.app U m)) = _
    rw [he]
  dsimp only
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    obtain ⟨U, hx, hU, m, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens
        i.ker.toModules.val.presheaf x m
    rw [hg]
    have hm : i.ker.toModulesι.app U m ∈ i.ker.ideal ⟨U, hU⟩ := by
      change i.ker.toModulesι.app U m ∈ (i.ker.ideal ⟨U, hU⟩ : Set Γ(X, U))
      rw [← i.ker.range_toModulesι_app ⟨U, hU⟩]
      exact ⟨m, rfl⟩
    rw [principal_quotient_affine_ideal A f π ⟨U, hU⟩] at hm
    obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton' (α := Γ(X, U))).mp hm
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨X.presheaf.germ U x hx a, ?_⟩
    rw [← X.presheaf.germ_res_apply (homOfLE le_top : U ⟶ ⊤) x hx r,
      ← map_mul, ha]
  · apply Ideal.span_le.mpr
    intro t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (⊤ : X.Opens) from trivial) isOpen_univ
    let rU := X.presheaf.map (homOfLE (le_top (a := U))).op r
    have hr : rU ∈ i.ker.ideal ⟨U, hU⟩ := by
      rw [principal_quotient_affine_ideal A f π ⟨U, hU⟩]
      exact Ideal.mem_span_singleton_self _
    change rU ∈ (i.ker.ideal ⟨U, hU⟩ : Set Γ(X, U)) at hr
    rw [← i.ker.range_toModulesι_app ⟨U, hU⟩] at hr
    obtain ⟨m, hm⟩ := hr
    refine ⟨TopCat.Presheaf.germ i.ker.toModules.val.presheaf U x hx m, ?_⟩
    rw [hg, hm]
    exact X.presheaf.germ_res_apply (homOfLE le_top : U ⟶ ⊤) x hx r

set_option backward.isDefEq.respectTransparency false in
/-- The image of the ideal of a base-changed principal quotient acting on a module
is the image of the corresponding scalar endomorphism.

Source: Stacks Project, Tag 0EX8, divisibility step, and Tag 08KS,
ideal-multiplication description of the closed-immersion restriction kernel.
(blueprint: lem-sc-principal-quotient-multiplication-image)

Proof: On an affine open Spec B of X, base change of A -> A/(pi) is
B -> B/(pi B), by the pushout universal property of the quotient. Its kernel is
the principal ideal generated by the image of pi. The ideal-sheaf inclusion
therefore has, on stalks, image pi O_{X,x}. Stalks commute with tensor products
and images. On a stalk M_x of F the ideal-action map has image
(pi O_{X,x}) M_x = pi M_x, which is exactly the image of the scalar
endomorphism. Thus the two image inclusions determine the same subobject of F:
every germ in one image locally lifts to the other, uniquely because the
image inclusions are monomorphisms. The local lifts agree on overlaps and glue
to mutually inverse maps of sheaves over F, giving the displayed isomorphism.
No flatness, invertibility, nonzeroness, or domain assumption is used.
For pi = 0 both images vanish. For pi a unit both inclusions are isomorphisms;
the quotient and its base change are empty. On an empty X all objects vanish. -/
theorem principal_quotient_multiplication_image
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (π : A) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π}))))
    let m := i.ker.toModulesι ▷ F ≫ (λ_ F).hom
    let μ := F.smulHom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)
    ∃ e : image μ ≅ image m, e.hom ≫ image.ι m = image.ι μ := by
  dsimp only
  apply image_iso_of_stalk_range
  intro x
  have hunit :
      let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
          ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
        ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
          e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
            U x hx r) = X.presheaf.germ U x hx r := by
    let D := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf
    let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}
    let e : ↑(TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) ≃+ X.presheaf.stalk x :=
      (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
    have hg (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
        e (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
      change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) ≫
        (preservesColimitIso A D).inv) r = _
      rw [ι_preservesColimitIso_inv]
      rfl
    let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (SheafOfModules.unit X.ringCatSheaf) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
      { e.toAddMonoidHom with
        map_smul' := by
          intro r m
          obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
          obtain ⟨V, hxV, m, rfl⟩ :=
            TopCat.Presheaf.exists_germ_eq
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
          have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
          rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
            ← TopCat.Presheaf.germ_res_apply
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf
              (homOfLE inf_le_right) x hx m,
            ← PresheafOfModules.germ_smul (R := X.presheaf)]
          let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
          let m' : Γ(X, U ⊓ V) :=
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf.map
              (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
          change e (TopCat.Presheaf.germ
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx (r' * m')) =
            X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx m') :
                X.presheaf.stalk x)
          rw [hg, hg]
          exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
    refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
    exact hg
  obtain ⟨e, he⟩ := hunit
  rw [Scheme.stalk_tensor_multiplication_range _ F x e he,
    principal_quotient_stalk_ideal A f π x e he, Submodule.ideal_span_singleton_smul]
  ext m
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, LinearMap.mem_range]
  apply exists_congr
  intro n
  rw [stalk_smulHom]

end AlgebraicGeometry.Scheme.Modules
