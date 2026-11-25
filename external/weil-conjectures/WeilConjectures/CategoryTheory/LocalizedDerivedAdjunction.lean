/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.ResolvingLeftDerivedAbsolute
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Shift.Localization

/-!
# Localized derived adjunction from a resolving class

Source: Stacks Project, Tags 06XN, 05SE, 05SU and 0FND.
(blueprint: lem-sf-localized-derived-adjunction).

This file records the statement corresponding to Stacks Project, Tags 06XN,
05SE, 05SU and 0FND.  It is the arbitrary triangulated-category form used by
the six-functors construction.  Proof sketch: the resolving-class
hypotheses give essential constancy of the denominator diagrams, hence a
pointwise and universal left derived functor.  The induced right functor is an
absolute right derived functor by the localization universal property.  The
absolute-derived-adjunction theorem then supplies the adjunction; its unit and
counit are normalized by the displayed equations.  Shift compatibility is
transported through the same universal properties, with coherence forced by
uniqueness.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uK vK uH vH uA vA uB vB uJ vJ

namespace CategoryTheory

/-- Stacks Project, Tags 06XN, 05SE, 05SU and 0FND (blueprint: lem-sf-localized-derived-adjunction).

Let `K` and `H` be triangulated categories, with saturated multiplicative
systems `W` and `V` compatible with their triangulations.  Let `Q` and `Q'`
be triangulated localization functors.  For an exact adjunction `E ⊣ R`,
assume that `R` carries `V`-arrows to `W`-arrows, and fix the induced-functor
comparison `β : R ⋙ Q ≅ Q' ⋙ Rbar`.  If `P` resolves every object of `K`
and `E` sends `W`-arrows between `P`-objects to isomorphisms, then the
localized left functor has an everywhere-defined pointwise and universal left
derived functor.  Its comparison is invertible on `P`, it is adjoint to
`Rbar`, and the unit and counit are uniquely characterized by the normalized
equations below. For every category `J` and every functor `F : B ⥤ J`, the
postcomposed pair is pointwise and universal as well: the pointwise clause is
`Nonempty (RightExtension.mk ...).IsPointwiseRightKanExtension`, and the
universal clause is `IsLeftDerivedFunctor`. No limits need be preserved by `F`.
All derived functors, comparisons, and the adjunction commute with integer
shifts; the shift structure `hRbar` on `Rbar` is the one induced from that of
`R ⋙ Q` through `β` (the conjunct making `β` shift-compatible pins it), so the
adjunction is compatible with the canonical shift of `Rbar` and not merely
with the one `Adjunction.commShift_of_leftAdjoint` would supply for any `L`.
No ordinary-complex realization is assumed.

Proof (blueprint steps):
1. `W` has a right calculus of fractions and two-out-of-three (MS1–MS4).  The
   resolving-class lemma (Tag 06XN) makes every denominator diagram
   `W/X → B` of `F = E ⋙ Q'` essentially constant, with cone `u_s`, and
   `u_{id_X}` is invertible for `X ∈ P`.
2. The pointwise-Kan bridge identifies these values with the pointwise right
   Kan extension of `F` along `Q`; total-left-derived assembly gives `L` and
   `c : Q ⋙ L ⟶ F`, universal (Tags 05S9, 05SE), with `c_X = u_{id_X}`.
3. `(L, c)` is absolute. For any `G : B ⥤ J`, the functor `F ⋙ G` again
   satisfies the hypotheses of steps 1–2, so it has a pointwise left derived
   functor whose counit is invertible on `P`. The comparison from
   `(L ⋙ G, c ⋙ G)` to it is therefore invertible at `Q(X)` for `X ∈ P`,
   hence everywhere since every object is isomorphic to such a `Q(X)`. Thus
   `(L ⋙ G, c ⋙ G)` is a left derived functor, and pointwise because
   `F ⋙ G` has a pointwise left derived functor.
4. `(Rbar, β)` is an absolute right derived pair, because precomposition with
   `Q'` is fully faithful on natural transformations.
5. The absolute-derived-adjunction theorem (Tag 0FND) gives `L ⊣ Rbar`.
6. The unit is the unique lift of `Q(u_X) ≫ β_{EX}` through the universal
   property of `(L ⋙ Rbar, whiskerRight c Rbar)`. The counit descends
   `L(β_Y⁻¹) ≫ c_{RY} ≫ Q'(v_Y)` along `Q'`. These universal properties
   also give uniqueness among all natural transformations satisfying the
   respective normalization equation, not just among adjunctions.
7. Set `h = L(η) ≫ ε_L`. Naturality of `ε`, the two normalization equations,
   naturality of `c`, and the underived left triangle give `h_Q ≫ c = c`.
   Injectivity of the derived universal bijection gives `h = 1`; individual
   `c_X` need not be invertible. For `k = η_Rbar ≫ Rbar(ε)`, naturality of
   `η`, the two normalization equations and naturality of `β` give
   `β_Y ≫ k_{Q'Y} = Q(u_{RY} ≫ R(v_Y)) ≫ β_Y = β_Y`. Cancel `β_Y`, then
   use full faithfulness of precomposition with `Q'` to obtain `k = 1`.
8. The shift on `Rbar` is induced from `R ⋙ Q` through `β` by the
   localization property of `Q'`, which makes `β` shift-compatible.
9. The shift on `L` is the one induced from that of `Rbar` through the
   adjunction, so the adjunction is shift-compatible. By the unit equation,
   `c_X = L(Q(u_X) ≫ β_{EX}) ≫ ε_{Q'EX}`, a composite of shift-compatible
   transformations, so `c` is shift-compatible (Tag 05SU).
-/
theorem exists_localizedDerivedAdjunction
    {K : Type uK} [Category.{vK} K] [HasZeroObject K] [HasShift K ℤ]
    [Preadditive K] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K] [IsTriangulated K]
    {H : Type uH} [Category.{vH} H] [HasZeroObject H] [HasShift H ℤ]
    [Preadditive H] [∀ n : ℤ, (shiftFunctor H n).Additive]
    [Pretriangulated H] [IsTriangulated H]
    {A : Type uA} [Category.{vA} A] [HasZeroObject A] [HasShift A ℤ]
    [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive]
    [Pretriangulated A] [IsTriangulated A]
    {B : Type uB} [Category.{vB} B] [HasZeroObject B] [HasShift B ℤ]
    [Preadditive B] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated B] [IsTriangulated B]
    (W : MorphismProperty K) (V : MorphismProperty H)
    (hW : W.IsSaturatedTriangulatedMultiplicativeSystem)
    (hV : V.IsSaturatedTriangulatedMultiplicativeSystem)
    (Q : K ⥤ A) (Q' : H ⥤ B)
    [Q.IsLocalization W] [Q'.IsLocalization V]
    [Q.CommShift ℤ] [Q'.CommShift ℤ]
    [Q.IsTriangulated] [Q'.IsTriangulated]
    (E : K ⥤ H) (R : H ⥤ K)
    [E.CommShift ℤ] [R.CommShift ℤ]
    [E.IsTriangulated] [R.IsTriangulated]
    (adj : E ⊣ R) [adj.CommShift ℤ]
    (hRV : ∀ {X Y : H} (f : X ⟶ Y), V f → W (R.map f))
    (Rbar : B ⥤ A)
    (β : R ⋙ Q ≅ Q' ⋙ Rbar)
    (P : Set K)
    (hres : ∀ X : K, ∃ (P' : K) (p : P' ⟶ X), P P' ∧ W p)
    (hinv : ∀ {X Y : K} (s : X ⟶ Y), P X → P Y → W s →
      IsIso ((E ⋙ Q').map s)) :
    ∃ (L : A ⥤ B) (c : Q ⋙ L ⟶ E ⋙ Q')
      (hL : L.CommShift ℤ) (hRbar : Rbar.CommShift ℤ) (d : L ⊣ Rbar),
      Functor.HasPointwiseLeftDerivedFunctor (E ⋙ Q') W ∧
      L.IsLeftDerivedFunctor c W ∧
      (∀ X : K, P X → IsIso (c.app X)) ∧
      (∀ (J : Type uJ) (_ : Category.{vJ} J) (F : B ⥤ J),
        Nonempty (Functor.RightExtension.IsPointwiseRightKanExtension
          (Functor.RightExtension.mk (L ⋙ F)
            ((Functor.associator Q L F).inv ≫ Functor.whiskerRight c F))) ∧
        (L ⋙ F).IsLeftDerivedFunctor
          ((Functor.associator Q L F).inv ≫ Functor.whiskerRight c F) W) ∧
      @NatTrans.CommShift _ _ _ _ (Q ⋙ L) (E ⋙ Q') c ℤ
        inferInstance inferInstance inferInstance
        (@Functor.CommShift.comp _ _ _ _ _ _ Q L ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : Q.CommShift ℤ) hL)
        (@Functor.CommShift.comp _ _ _ _ _ _ E Q' ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : E.CommShift ℤ) (inferInstance : Q'.CommShift ℤ)) ∧
      @Adjunction.CommShift A B _ _ L Rbar d ℤ
        inferInstance inferInstance inferInstance hL hRbar ∧
      @NatTrans.CommShift _ _ _ _ (R ⋙ Q) (Q' ⋙ Rbar) β.hom ℤ
        inferInstance inferInstance inferInstance
        (@Functor.CommShift.comp _ _ _ _ _ _ R Q ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : R.CommShift ℤ) (inferInstance : Q.CommShift ℤ))
        (@Functor.CommShift.comp _ _ _ _ _ _ Q' Rbar ℤ
          inferInstance inferInstance inferInstance inferInstance
          (inferInstance : Q'.CommShift ℤ) hRbar) ∧
      (∀ X : K,
        d.unit.app (Q.obj X) ≫ Rbar.map (c.app X) =
          Q.map (adj.unit.app X) ≫ β.hom.app (E.obj X)) ∧
      (∀ Y : H,
        L.map (β.hom.app Y) ≫ d.counit.app (Q'.obj Y) =
          c.app (R.obj Y) ≫ Q'.map (adj.counit.app Y)) ∧
      (∀ η : 𝟭 A ⟶ L ⋙ Rbar,
        (∀ X : K, η.app (Q.obj X) ≫ Rbar.map (c.app X) =
          Q.map (adj.unit.app X) ≫ β.hom.app (E.obj X)) → η = d.unit) ∧
      (∀ ε : Rbar ⋙ L ⟶ 𝟭 B,
        (∀ Y : H, L.map (β.hom.app Y) ≫ ε.app (Q'.obj Y) =
          c.app (R.obj Y) ≫ Q'.map (adj.counit.app Y)) → ε = d.counit) := by
  -- `hRV` is not needed: the comparison `β` already exhibits `Rbar` as induced by `R ⋙ Q`.
  have _ := @hRV
  have : W.HasRightCalculusOfFractions := hW.1.1.2
  have : W.HasTwoOutOfThreeProperty := hW.1.hasTwoOutOfThreeProperty Q
  have : V.IsCompatibleWithShift ℤ := hV.2.toIsCompatibleWithShift
  have hinv' (X X' : K) (s : X ⟶ X') (hX : X ∈ P) (hX' : X' ∈ P) (hs : W s) :
      IsIso ((E ⋙ Q').map s) :=
    hinv s hX hX' hs
  have hpw := Functor.hasPointwiseLeftDerivedFunctor_of_resolving W (E ⋙ Q') P hres hinv'
  let L := (E ⋙ Q').totalLeftDerived Q W
  let c := (E ⋙ Q').totalLeftDerivedCounit Q W
  have := Functor.isLeftDerivedFunctor_comp_of_resolving W Q (E ⋙ Q') P hres hinv' L c Rbar
  have : Rbar.IsRightDerivedFunctor β.hom V :=
    Functor.isRightDerivedFunctor_of_inverts V Rbar β.symm
  have : (Rbar ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight β.hom L ≫ (Functor.associator _ _ _).hom) V :=
    Functor.isRightDerivedFunctor_of_inverts V (Rbar ⋙ L)
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight β.symm L)
  let d := adj.derived W V c β.hom
  have hunit (X : K) : d.unit.app (Q.obj X) ≫ Rbar.map (c.app X) =
      Q.map (adj.unit.app X) ≫ β.hom.app (E.obj X) :=
    adj.derivedη_fac_app W c β.hom X
  have hcounit (Y : H) : L.map (β.hom.app Y) ≫ d.counit.app (Q'.obj Y) =
      c.app (R.obj Y) ≫ Q'.map (adj.counit.app Y) :=
    adj.derivedε_fac_app V c β.hom Y
  let : Localization.Lifting Q' V (R ⋙ Q) Rbar := ⟨β.symm⟩
  let hRbar : Rbar.CommShift ℤ := Functor.commShiftOfLocalization Q' V ℤ (R ⋙ Q) Rbar
  let hL : L.CommShift ℤ := d.leftAdjointCommShift ℤ
  have hd : d.CommShift ℤ := d.commShift_of_rightAdjoint ℤ
  have : NatTrans.CommShift β.symm.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso Q' V (R ⋙ Q) Rbar).hom ℤ)
  have hβ : NatTrans.CommShift β.hom ℤ := NatTrans.CommShift.of_iso_inv β.symm ℤ
  have hc : c = Functor.whiskerRight (Q.leftUnitor.inv ≫ Functor.whiskerRight adj.unit Q ≫
      (Functor.associator E R Q).hom ≫ Functor.whiskerLeft E β.hom ≫
      (Functor.associator E Q' Rbar).inv) L ≫ (Functor.associator (E ⋙ Q') Rbar L).hom ≫
      Functor.whiskerLeft (E ⋙ Q') d.counit ≫ (E ⋙ Q').rightUnitor.hom := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_hom_app, Functor.map_comp, Category.id_comp,
      Category.comp_id, Category.assoc]
    rw [← L.map_comp_assoc, ← hunit]
    simp [L]
  have hcs : NatTrans.CommShift c ℤ := by
    rw [hc]
    infer_instance
  refine ⟨L, c, hL, hRbar, d, hpw, inferInstance,
    fun X hX ↦ Functor.isIso_app_of_resolving W Q (E ⋙ Q') P hres hinv' L c X hX,
    fun J _ F ↦ ⟨Functor.isPointwiseRightKanExtension_comp_of_resolving W Q (E ⋙ Q') P hres
      hinv' L c F, Functor.isLeftDerivedFunctor_comp_of_resolving W Q (E ⋙ Q') P hres
      hinv' L c F⟩, hcs, hd, hβ, hunit, hcounit, fun η hη ↦ ?_, fun ε hε ↦ ?_⟩
  · apply (L ⋙ Rbar).leftDerived_ext
      ((Functor.associator Q L Rbar).inv ≫ Functor.whiskerRight c Rbar) W
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp]
    rw [hη X, hunit X]
  · apply (Rbar ⋙ L).rightDerived_ext
      (Functor.whiskerRight β.hom L ≫ (Functor.associator _ _ _).hom) V
    ext Y
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.id_comp, Category.assoc]
    rw [hε Y, hcounit Y]

end CategoryTheory

end
