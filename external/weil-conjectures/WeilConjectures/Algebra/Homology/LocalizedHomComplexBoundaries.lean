/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Localized Hom boundaries and null-homotopies

Source: Stacks Project, Tag 0A8X, differential of the Hom complex,
and Equation 0A8Y, degree zero.
(blueprint: lem-pur-localized-hom-complex-boundaries)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

-- Package the definitional restriction comparison once; rechecking its maps is expensive.
private noncomputable def localizedSectionEquiv
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (M N : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :
    ((SheafOfModules.homObj (R := R) M N).val.obj (op U)) ≃+
      (M.over U ⟶ N.over U) where
  toFun s := ⟨s⟩
  invFun f := f.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private lemma localizedSectionEquiv_map
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    {M M' N N' : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)}
    (f : M' ⟶ M) (g : N ⟶ N')
    (s : (SheafOfModules.homObj (R := R) M N).val.obj (op U)) :
    localizedSectionEquiv R U M' N'
        ((SheafOfModules.homObjMap (R := R) f g).val.app (op U) s) =
      f.over U ≫ localizedSectionEquiv R U M N s ≫ g.over U := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

set_option backward.isDefEq.respectTransparency true in
-- Evaluated product projections unfold composed functors and restriction wrappers.
/-- A localized chain map represented by a cycle is null-homotopic exactly when
that cycle is a boundary in the section complex.
Source: Stacks Project, Tag 0A8X, differential of the Hom complex,
and Equation 0A8Y, degree zero.
(blueprint: lem-pur-localized-hom-complex-boundaries)

Proof: the product fan specified by homComplex_exists remains limiting after
forgetting module sheaves, evaluating at U, and forgetting modules to abelian
groups. In degree -1 it identifies a section x with the family of localized
maps h_p : L^p|_U → I^(p-1)|_U supplied by the projections. Lift the underlying
presheaf-module maps to sheaf-module maps using the fully faithful forgetful
functor. The differential projection formula in degree -1 says that the p-th
component of d(x) is h_p followed by d_I plus d_L followed by h_(p+1), since
(-1)^(-1)=-1. The identity toCycles followed by iCycles equals d therefore
shows, using the assumed component formula for f, that these h_p form a
null-homotopy of f when z=toCycles(x). This proves the boundary-to-homotopy direction.
Conversely, take the adjacent-degree components h_p of a null-homotopy of f.
Their underlying presheaf maps assemble uniquely into a degree -1 section x
by the evaluated product fan. The same differential identity and the homotopy
commutation equation give d(x)=iCycles(z), component by component. The product
projections are jointly injective on sections. Since iCycles is monic, the
identity iCycles(toCycles(x))=d(x) implies toCycles(x)=z.
There is no boundedness or finite support assumption. For zero complexes the
section and map groups are zero. If both differentials vanish, the homotopy
equation forces f=0 and both sides require z=0. -/
theorem localizedHomComplex_nullHomotopy_iff_boundary
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    let := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ (z : S.cycles 0) (f : res.obj L ⟶ res.obj I),
      (∀ (p : ℤ) (W : (Over U)ᵒᵖ),
        (f.f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
      (Nonempty (Homotopy f 0) ↔ ∃ x : S.X (-1), S.toCycles (-1) 0 x = z) := by
  classical
  intro R₀ H π S inst res z f hf
  let E := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat
  let := hzero
  let P : ∀ (n p q : ℤ), p + n = q →
      (H.X n ⟶ SheafOfModules.homObj (R := R) (L.X p) (I.X q)) := π L I
  have hprod (n : ℤ) : Nonempty (Limits.IsLimit
      (Limits.Fan.mk (H.X n) (fun p : ℤ ↦ P n p (p + n) rfl))) :=
    (Classical.choose_spec (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))).1 L I n
  have hdiff (p : ℤ) : H.d (-1) 0 ≫ P 0 p p (add_zero p) =
      P (-1) p (p - 1) (by omega) ≫
        SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (I.d (p - 1) p) -
      (-1 : ℤ).negOnePow • (P (-1) (p + 1) p (by omega) ≫
        SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (I.X p))) :=
    (Classical.choose_spec (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))).2.1
      L I (-1) 0 p p (p - 1) (p + 1) (by omega) (add_zero p)
        (by omega) (by omega)
  change ∀ (p : ℤ) (W : (Over U)ᵒᵖ),
    (f.f p).val.app W = (((P 0 p p (add_zero p)).val.app (op U))
      (S.iCycles 0 z)).app W at hf
  clear_value P
  clear π
  clear_value H
  let a (x : S.X (-1)) (p q : ℤ) (hpq : p + (-1) = q) :
      (res.obj L).X p ⟶ (res.obj I).X q :=
    localizedSectionEquiv R U (L.X p) (I.X q) (((P (-1) p q hpq).val.app (op U)) x)
  let b (y : S.X 0) (p : ℤ) : (res.obj L).X p ⟶ (res.obj I).X p :=
    localizedSectionEquiv R U (L.X p) (I.X p)
      (((P 0 p p (add_zero p)).val.app (op U)) y)
  have hd (x : S.X (-1)) (p : ℤ) :
      b (S.d (-1) 0 x) p =
        (res.obj L).d p (p + 1) ≫ a x (p + 1) p (by omega) +
        a x p (p - 1) (by omega) ≫ (res.obj I).d (p - 1) p := by
    have hd := hdiff p
    have he := congrArg
      (fun k : H.X (-1) ⟶ SheafOfModules.homObj (R := R) (L.X p) (I.X p) ↦
        (k.val.app (op U)) x) hd
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      sub_neg_eq_add] at he
    change ((P 0 p p (add_zero p)).val.app (op U)) (S.d (-1) 0 x) =
      (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (I.d (p - 1) p)).val.app (op U)
        (((P (-1) p (p - 1) (by omega)).val.app (op U)) x) +
      (SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (I.X p))).val.app (op U)
        (((P (-1) (p + 1) p (by omega)).val.app (op U)) x) at he
    have he' := congrArg (localizedSectionEquiv R U (L.X p) (I.X p)) he
    rw [map_add, localizedSectionEquiv_map, localizedSectionEquiv_map] at he'
    simp only [SheafOfModules.Hom.over, Functor.map_id, Category.id_comp,
      Category.comp_id] at he'
    exact he'.trans (add_comm _ _)
  have hf' (p : ℤ) : f.f p = b (S.iCycles 0 z) p := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    exact hf p
  constructor
  · rintro ⟨h⟩
    let T := E ⋙ forget AddCommGrpCat
    let c (n : ℤ) := Limits.Fan.mk (H.X n) (fun p : ℤ ↦ P n p (p + n) rfl)
    have hc (n : ℤ) : Limits.IsLimit (c n) := (hprod n).some
    let ht (n : ℤ) := (Limits.Fan.isLimitMapConeEquiv T _ (c n))
      (Limits.isLimitOfPreserves T (hc n))
    let family (p : ℤ) : PUnit ⟶ T.obj (SheafOfModules.homObj (R := R)
        (L.X p) (I.X (p + (-1)))) := ↾fun _ ↦
      (localizedSectionEquiv R U (L.X p) (I.X (p + (-1)))).symm
        (h.hom p (p + (-1)))
    let xx : PUnit ⟶ T.obj (H.X (-1)) := Limits.Fan.IsLimit.lift (ht (-1)) family
    let x : S.X (-1) := xx PUnit.unit
    have hx (p q : ℤ) (hpq : p + (-1) = q) : a x p q hpq = h.hom p q := by
      subst q
      apply (localizedSectionEquiv R U (L.X p) (I.X (p + (-1)))).symm.injective
      change ((P (-1) p (p + (-1)) rfl).val.app (op U)) x = _
      exact ConcreteCategory.congr_hom (Limits.Fan.IsLimit.fac (ht (-1)) family p)
        PUnit.unit
    have heq (p : ℤ) : b (S.d (-1) 0 x) p = f.f p := by
      rw [hd, hx, hx]
      have hh := h.comm p
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) by
        simp [ComplexShape.up_Rel]),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (p - 1) p by
          simp [ComplexShape.up_Rel]), HomologicalComplex.zero_f_apply, add_zero] at hh
      exact hh.symm
    refine ⟨x, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective (S.iCycles 0)).mp inferInstance
    have hd' := ConcreteCategory.congr_hom (S.toCycles_i (-1) 0) x
    change S.iCycles 0 (S.toCycles (-1) 0 x) = S.d (-1) 0 x at hd'
    rw [hd']
    have he : (↾fun _ : PUnit ↦ S.d (-1) 0 x) =
        (↾fun _ : PUnit ↦ S.iCycles 0 z) := by
      apply (ht 0).hom_ext
      intro ⟨p⟩
      apply ConcreteCategory.hom_ext
      intro t
      change ((P 0 p (p + 0) rfl).val.app (op U)) (S.d (-1) 0 x) =
        ((P 0 p (p + 0) rfl).val.app (op U)) (S.iCycles 0 z)
      have hh := congrArg (localizedSectionEquiv R U (L.X p) (I.X p)).symm
        ((heq p).trans (hf' p))
      cases p <;> exact hh
    exact ConcreteCategory.congr_hom he PUnit.unit
  · rintro ⟨x, hx⟩
    let h (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel q p) :
        (res.obj L).X p ⟶ (res.obj I).X q := a x p q (by
          simp only [ComplexShape.up_Rel] at hpq
          omega)
    have heq : f = Homotopy.nullHomotopicMap' h := by
      apply HomologicalComplex.hom_ext
      intro p
      rw [Homotopy.nullHomotopicMap'_f (k₂ := p - 1) (k₀ := p + 1)
        (by simp [ComplexShape.up_Rel]) (by simp [ComplexShape.up_Rel])]
      rw [hf']
      have hx' := ConcreteCategory.congr_hom (S.toCycles_i (-1) 0) x
      change S.iCycles 0 (S.toCycles (-1) 0 x) = S.d (-1) 0 x at hx'
      rw [hx] at hx'
      rw [hx']
      exact hd x p
    exact ⟨heq ▸ Homotopy.nullHomotopy' h⟩

end CategoryTheory
