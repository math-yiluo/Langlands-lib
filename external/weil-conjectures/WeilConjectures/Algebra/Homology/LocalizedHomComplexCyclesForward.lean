/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true in
/-- The projection components of a localized degree-zero cycle form a chain map.
Source: Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y.
(blueprint: lem-pur-localized-hom-complex-cycles-forward)

Proof: for a cycle z, define the degree-p component by applying the chosen
projection pi at U to iCycles z. An internal-Hom section is a linear natural
transformation on the slice; equip it with the sheaf-morphism wrapper. The cycle
inclusion followed by the differential is zero. Compose this equality with each
degree-one product projection and use the differential formula in
homComplex_exists at n = 0, m = 1. Since (-1)^0 = 1, it says that the component
followed by d_I equals d_L followed by the next component. These are exactly the
successive chain-map equations on the slice. Every other equation has both
complex differentials zero by the shape condition and preservation of zero
morphisms under restriction. Thus the components define a chain map for each z.
The asserted formula holds by construction. This argument needs neither an
inverse map nor preservation of the product by section evaluation. -/
theorem localizedHomComplex_cycles_forward
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
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∃ f : S.cycles 0 → (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((f z).f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let H := homComplex (R := R) L I
  let π := Classical.choose (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj H
  let := hzero
  let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let a (z : S.cycles 0) (p : ℤ) : (res.obj L).X p ⟶ (res.obj I).X p :=
    ⟨((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)⟩
  have ha (z : S.cycles 0) (p q : ℤ) (hpq : p + 1 = q) :
      a z p ≫ (res.obj I).d p q = (res.obj L).d p q ≫ a z q := by
    have hd := (Classical.choose_spec (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))).2.1
      L I 0 1 p q p q (by omega) hpq (add_zero p) (add_zero q)
    have hz := ConcreteCategory.congr_hom (S.iCycles_d 0 1) z
    change S.d 0 1 (S.iCycles 0 z) = 0 at hz
    have he := congrArg
      (fun k : H.X 0 ⟶ SheafOfModules.homObj (R := R) (L.X p) (I.X q) ↦
        (k.val.app (op U)) (S.iCycles 0 z)) hd
    simp only [Int.negOnePow_zero, one_smul] at he
    change ((π L I 1 p q hpq).val.app (op U)) (S.d 0 1 (S.iCycles 0 z)) =
      (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (I.d p q)).val.app (op U)
        (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)) -
      (SheafOfModules.homObjMap (R := R) (L.d p q) (𝟙 (I.X q))).val.app (op U)
        (((π L I 0 q q (add_zero q)).val.app (op U)) (S.iCycles 0 z)) at he
    have hzπ := (congrArg ((π L I 1 p q hpq).val.app (op U)) hz).trans
      ((π L I 1 p q hpq).val.app (op U)).hom.map_zero
    have hc := sub_eq_zero.mp (he.symm.trans hzπ)
    -- Compare components before unfolding the two restriction constructions.
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext t
    exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app W) hc) t
  refine ⟨fun z ↦ { f := a z, comm' := ?_ }, ?_⟩
  · intro p q hpq
    exact ha z p q hpq
  · intro z p W
    rfl

end CategoryTheory
