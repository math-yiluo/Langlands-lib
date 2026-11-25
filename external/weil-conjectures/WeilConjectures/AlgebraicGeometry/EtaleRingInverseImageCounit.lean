/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Lifting the étale set counit to ring sheaves

Source: Stacks Project, Proposition 00YV, proof of (2), ring paragraph.
(blueprint: lem-weil-pbc-etale-ring-inverse-image-counit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry

private local instance forgottenRingSheafHasBinaryProduct.{uC, vC, w}
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget CommRingCat.{w})] (G H : Sheaf J CommRingCat.{w}) :
    HasBinaryProduct (C := Sheaf J (Type w))
      ((sheafForget J).obj G) ((sheafForget J).obj H) := by
  let : HasBinaryProducts (Sheaf J (Type w)) := Sheaf.instHasLimitsOfShape
  exact HasLimitsOfShape.has_limit _

attribute [-instance] instHasBinaryProductObjOfPreservesLimitDiscreteWalkingPairPair in
private noncomputable def ringAdd.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) := by
  let H : Sheaf J (Type w) := (sheafForget J).obj G
  change H ⨯ H ⟶ H
  refine ⟨{
    app := fun W ↦ ↾(fun x ↦ @Add.add (G.obj.obj W) inferInstance
      ((prod.fst : H ⨯ H ⟶ H).hom.app W x : G.obj.obj W)
      ((prod.snd : H ⨯ H ⟶ H).hom.app W x : G.obj.obj W))
    naturality := ?_ }⟩
  intro W W' f
  ext x
  have hf := types_congr_hom ((prod.fst : H ⨯ H ⟶ H).hom.naturality f) x
  have hs := types_congr_hom ((prod.snd : H ⨯ H ⟶ H).hom.naturality f) x
  dsimp at hf hs ⊢
  rw [hf, hs]
  exact (G.obj.map f).hom.map_add _ _ |>.symm
attribute [-instance] instHasBinaryProductObjOfPreservesLimitDiscreteWalkingPairPair in
private noncomputable def ringMul.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) := by
  let H : Sheaf J (Type w) := (sheafForget J).obj G
  change H ⨯ H ⟶ H
  refine ⟨{
    app := fun W ↦ ↾(fun x ↦ @Mul.mul (G.obj.obj W) inferInstance
      ((prod.fst : H ⨯ H ⟶ H).hom.app W x : G.obj.obj W)
      ((prod.snd : H ⨯ H ⟶ H).hom.app W x : G.obj.obj W))
    naturality := ?_ }⟩
  intro W W' f
  ext x
  have hf := types_congr_hom ((prod.fst : H ⨯ H ⟶ H).hom.naturality f) x
  have hs := types_congr_hom ((prod.snd : H ⨯ H ⟶ H).hom.naturality f) x
  dsimp at hf hs ⊢
  rw [hf, hs]
  exact (G.obj.map f).hom.map_mul _ _ |>.symm
private noncomputable def ringZero.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : ⊤_ (Sheaf J (Type w)) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (0 : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_zero |>.symm }⟩
private noncomputable def ringOne.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : ⊤_ (Sheaf J (Type w)) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_one |>.symm }⟩


set_option backward.isDefEq.respectTransparency false in
-- Product comparisons and sectionwise operations require repeated functor reduction.
/-- Source: Stacks Project, Proposition 00YV, proof of (2), ring paragraph.
(blueprint: lem-weil-pbc-etale-ring-inverse-image-counit).

Proof: Put β_F = er_F* followed by the set counit (where er_F* is the component
at Rr F). The unit formula and the right triangle identity imply that the forgotten
ring unit at Rr F, followed by R(β_F), is the identity. For a binary operation,
precompose the desired compatibility of β_F with the isomorphism
L(X × X) → Y × Y obtained from the product comparison and two inverse components
of er, with X the underlying sheaf of Rr F and Y that of Lr(Rr F).
Apply the injective set-adjunction bijection. The adjunct t of this isomorphism has
projections equal to the forgotten ring unit composed with the projections of X × X:
this follows from unit naturality and the projection equations for the comparison.
On sections, replace those projections by the unit applied to each coordinate.
Because the unit is a ring homomorphism, their sum (or product) is the unit of the
sum (or product). Applying β_F now cancels the unit by the preceding identity.
This proves compatibility with addition and multiplication. For zero and one,
precompose with the invertible terminal comparison, apply the same bijection,
and use preservation of the constant by the ring unit and its cancellation by β_F.
The categorical product has all pairs of sections: map the sectionwise Cartesian
tensor product to it by its two projections. The categorical terminal sheaf has
a section at every object: map the singleton Cartesian unit to it. Evaluating the
four operation equalities on these sections gives the ring-homomorphism axioms
for β_F at every site object. Its naturality in the site object is already that of
the underlying sheaf morphism, so these homomorphisms define a ring-sheaf morphism.
Finally naturality of er and of the set counit proves naturality in F. Negation
preservation follows from the ring-homomorphism axioms. No ring adjunction is used. -/
theorem etaleRingInverseImageCounit (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let R := b.sheafPushforwardContinuous (Type (u + 1))
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∀ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (er : Lr ⋙ FrU ≅ FrV ⋙ L) (η : 𝟭 _ ⟶ Lr ⋙ Rr),
      (∀ G, FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)) →
      ∃ ε : Rr ⋙ Lr ⟶ 𝟭 _,
        ∀ F, FrU.map (ε.app F) = er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F) :=
  by
  dsimp only
  intro Lr er η hη
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let R : Sheaf U.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf V.smallEtaleTopology (Type (u + 1)) := b.sheafPushforwardContinuous _
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let Rr : Sheaf U.smallEtaleTopology CommRingCat.{u + 1} ⥤
      Sheaf V.smallEtaleTopology CommRingCat.{u + 1} := b.sheafPushforwardContinuous _
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
  let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
  let a : L ⊣ R := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
    (U.smallGrothendieckTopology @Etale)
  let : PreservesFiniteLimits L := hL
  let : PreservesFiniteProducts L := ⟨fun _ ↦ inferInstance⟩
  change ∀ G, FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G) at hη
  let β (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) :
      FrU.obj (Lr.obj (Rr.obj F)) ⟶ FrU.obj F :=
    er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F)
  have hβ (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) :
      FrV.map (η.app (Rr.obj F)) ≫ R.map (β F) = 𝟙 (FrV.obj (Rr.obj F)) := by
    rw [hη]
    change (a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (er.inv.app (Rr.obj F))) ≫
      R.map (er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F)) = 𝟙 _
    calc
      _ = a.unit.app (FrV.obj (Rr.obj F)) ≫
          R.map ((er.inv.app (Rr.obj F) ≫ er.hom.app (Rr.obj F)) ≫
            a.counit.app (FrU.obj F)) := by simp only [R.map_comp, Category.assoc]
      _ = a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (a.counit.app (FrU.obj F)) := by
        erw [er.inv_hom_id_app, Category.id_comp]
      _ = 𝟙 _ := a.right_triangle_components (FrU.obj F)
  have hbin (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (opY : FrU.obj (Lr.obj (Rr.obj F)) ⨯ FrU.obj (Lr.obj (Rr.obj F)) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : FrU.obj F ⨯ FrU.obj F ⟶ FrU.obj F)
      (op : ∀ S : CommRingCat.{u + 1}, S → S → S)
      (hy : ∀ W x, opY.hom.app W x = op ((Lr.obj (Rr.obj F)).obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x))
      (hz : ∀ W x, opZ.hom.app W x = op (F.obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj F).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj F).hom.app W x))
      (hηop : ∀ W x y, (η.app (Rr.obj F)).hom.app W
        (op ((Rr.obj F).obj.obj W) x y) =
        op ((Lr.obj (Rr.obj F)).obj.obj (b.op.obj W))
          ((η.app (Rr.obj F)).hom.app W x) ((η.app (Rr.obj F)).hom.app W y)) :
      opY ≫ β F = prod.map (β F) (β F) ≫ opZ := by
    let X := FrV.obj (Rr.obj F)
    let Y := FrU.obj (Lr.obj (Rr.obj F))
    let q : L.obj (X ⨯ X) ⟶ Y ⨯ Y :=
      prodComparison L X X ≫ prod.map (er.inv.app (Rr.obj F)) (er.inv.app (Rr.obj F))
    have : IsIso q := by dsimp [q]; infer_instance
    let t : X ⨯ X ⟶ R.obj (Y ⨯ Y) := a.homEquiv _ _ q
    have ht (p : X ⨯ X ⟶ X) (p' : Y ⨯ Y ⟶ Y)
        (hp : q ≫ p' = L.map p ≫ er.inv.app (Rr.obj F)) :
        t ≫ R.map p' = p ≫ FrV.map (η.app (Rr.obj F)) := by
      change (a.unit.app (X ⨯ X) ≫ R.map q) ≫ R.map p' = _
      have hn : a.unit.app (X ⨯ X) ≫ R.map (L.map p) = p ≫ a.unit.app X :=
        a.unit_naturality p
      rw [Category.assoc, ← R.map_comp, hp, R.map_comp, ← Category.assoc,
        hn, Category.assoc, ← hη]
    have hf := ht prod.fst prod.fst (by
      dsimp only [q]
      rw [Category.assoc, prod.map_fst, ← Category.assoc, prodComparison_fst])
    have hs := ht prod.snd prod.snd (by
      dsimp only [q]
      rw [Category.assoc, prod.map_snd, ← Category.assoc, prodComparison_snd])
    apply (cancel_epi q).1
    apply (a.homEquiv _ _).injective
    change a.unit.app (X ⨯ X) ≫ R.map (q ≫ opY ≫ β F) =
      a.unit.app (X ⨯ X) ≫ R.map (q ≫ prod.map (β F) (β F) ≫ opZ)
    simp only [R.map_comp, ← Category.assoc]
    change (t ≫ R.map opY) ≫ R.map (β F) =
      (t ≫ R.map (prod.map (β F) (β F))) ≫ R.map opZ
    ext W x
    have hf' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hf) x
    have hs' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hs) x
    have hb (z : X.obj.obj W) := types_congr_hom
      (congrArg (fun k : X ⟶ X ↦ k.hom.app W) (hβ F)) z
    change (β F).hom.app (b.op.obj W) (opY.hom.app (b.op.obj W) (t.hom.app W x)) =
      opZ.hom.app (b.op.obj W)
        ((prod.map (β F) (β F)).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hy, hz]
    have hpf := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app (b.op.obj W))
        (prod.map_fst (β F) (β F))) (t.hom.app W x)
    have hps := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app (b.op.obj W))
        (prod.map_snd (β F) (β F))) (t.hom.app W x)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      types_comp_apply] at hpf hps
    rw [hpf, hps]
    change (β F).hom.app (b.op.obj W)
        (op ((Lr.obj (Rr.obj F)).obj.obj (b.op.obj W))
          ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
          ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))) =
      op (F.obj.obj (b.op.obj W))
        ((β F).hom.app (b.op.obj W)
          ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x)))
        ((β F).hom.app (b.op.obj W)
          ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x)))
    change (prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (η.app (Rr.obj F)).hom.app W
        ((prod.fst : X ⨯ X ⟶ X).hom.app W x) at hf'
    change (prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (η.app (Rr.obj F)).hom.app W
        ((prod.snd : X ⨯ X ⟶ X).hom.app W x) at hs'
    change ∀ z, (β F).hom.app (b.op.obj W) ((η.app (Rr.obj F)).hom.app W z) = z at hb
    rw [hf', hs', ← hηop]
    exact (hb _).trans (congrArg₂ (op (F.obj.obj (b.op.obj W))) (hb _).symm (hb _).symm)
  have hadd (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) :
      ringAdd _ (Lr.obj (Rr.obj F)) ≫ β F =
        prod.map (β F) (β F) ≫ ringAdd _ F := by
    apply hbin F _ _ (fun S x y ↦ x + y) (by intros; rfl) (by intros; rfl)
    intro W x y
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_add x y
  have hmul (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) :
      ringMul _ (Lr.obj (Rr.obj F)) ≫ β F =
        prod.map (β F) (β F) ≫ ringMul _ F := by
    apply hbin F _ _ (fun S x y ↦ x * y) (by intros; rfl) (by intros; rfl)
    intro W x y
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_mul x y
  have hcst (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (opY : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ FrU.obj F)
      (c : ∀ S : CommRingCat.{u + 1}, S)
      (hy : ∀ W x, opY.hom.app W x = c ((Lr.obj (Rr.obj F)).obj.obj W))
      (hz : ∀ W x, opZ.hom.app W x = c (F.obj.obj W))
      (hηc : ∀ W, (η.app (Rr.obj F)).hom.app W (c ((Rr.obj F).obj.obj W)) =
        c ((Lr.obj (Rr.obj F)).obj.obj (b.op.obj W))) : opY ≫ β F = opZ := by
    apply (cancel_epi (terminalComparison L)).1
    apply (a.homEquiv _ _).injective
    let t := a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
      R.map (terminalComparison L)
    change a.unit.app _ ≫ R.map (terminalComparison L ≫ opY ≫ β F) =
      a.unit.app _ ≫ R.map (terminalComparison L ≫ opZ)
    simp only [R.map_comp, ← Category.assoc]
    change (t ≫ R.map opY) ≫ R.map (β F) = t ≫ R.map opZ
    ext W x
    change (β F).hom.app (b.op.obj W) (opY.hom.app (b.op.obj W) (t.hom.app W x)) =
      opZ.hom.app (b.op.obj W) (t.hom.app W x)
    rw [hy, hz, ← hηc]
    exact types_congr_hom
      (congrArg (fun k : FrV.obj (Rr.obj F) ⟶ FrV.obj (Rr.obj F) ↦ k.hom.app W)
        (hβ F)) (c ((Rr.obj F).obj.obj W))
  have hzero (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) :
      ringZero _ (Lr.obj (Rr.obj F)) ≫ β F = ringZero _ F := by
    apply hcst F _ _ (fun _ ↦ 0) (by intros; rfl) (by intros; rfl)
    intro W
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_zero
  have hone (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) :
      ringOne _ (Lr.obj (Rr.obj F)) ≫ β F = ringOne _ F := by
    apply hcst F _ _ (fun _ ↦ 1) (by intros; rfl) (by intros; rfl)
    intro W
    exact ((η.app (Rr.obj F)).hom.app W).hom.map_one
  have coords (Y : Sheaf U.smallEtaleTopology (Type (u + 1)))
      (W : U.Etaleᵒᵖ) (x y : Y.obj.obj W) :
      ∃ s : (Y ⨯ Y).obj.obj W,
        (prod.fst : Y ⨯ Y ⟶ Y).hom.app W s = x ∧
        (prod.snd : Y ⨯ Y ⟶ Y).hom.app W s = y := by
    let c : Y ⊗ Y ⟶ Y ⨯ Y := prod.lift
      (CartesianMonoidalCategory.fst Y Y) (CartesianMonoidalCategory.snd Y Y)
    refine ⟨c.hom.app W (x, y), ?_, ?_⟩
    · exact types_congr_hom (congrArg (fun k : Y ⊗ Y ⟶ Y ↦ k.hom.app W)
        (prod.lift_fst (CartesianMonoidalCategory.fst Y Y)
          (CartesianMonoidalCategory.snd Y Y))) (x, y)
    · exact types_congr_hom (congrArg (fun k : Y ⊗ Y ⟶ Y ↦ k.hom.app W)
        (prod.lift_snd (CartesianMonoidalCategory.fst Y Y)
          (CartesianMonoidalCategory.snd Y Y))) (x, y)
  have hbinary_sections (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (opY : FrU.obj (Lr.obj (Rr.obj F)) ⨯ FrU.obj (Lr.obj (Rr.obj F)) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : FrU.obj F ⨯ FrU.obj F ⟶ FrU.obj F)
      (op : ∀ S : CommRingCat.{u + 1}, S → S → S)
      (hy : ∀ W x, opY.hom.app W x = op ((Lr.obj (Rr.obj F)).obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj (Lr.obj (Rr.obj F))).hom.app W x))
      (hz : ∀ W x, opZ.hom.app W x = op (F.obj.obj W)
        ((prod.fst : _ ⟶ FrU.obj F).hom.app W x)
        ((prod.snd : _ ⟶ FrU.obj F).hom.app W x))
      (he : opY ≫ β F = prod.map (β F) (β F) ≫ opZ)
      (W : U.Etaleᵒᵖ) (x y : (Lr.obj (Rr.obj F)).obj.obj W) :
      (β F).hom.app W (op ((Lr.obj (Rr.obj F)).obj.obj W) x y) =
        op (F.obj.obj W) ((β F).hom.app W x) ((β F).hom.app W y) := by
    let Y := FrU.obj (Lr.obj (Rr.obj F))
    obtain ⟨s, hs₁, hs₂⟩ := coords Y W x y
    have hp₁ := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app W)
        (prod.map_fst (β F) (β F))) s
    have hp₂ := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app W)
        (prod.map_snd (β F) (β F))) s
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      types_comp_apply] at hp₁ hp₂
    have hh := types_congr_hom
      (congrArg (fun k : Y ⨯ Y ⟶ FrU.obj F ↦ k.hom.app W) he) s
    change (β F).hom.app W (opY.hom.app W s) =
      opZ.hom.app W ((prod.map (β F) (β F)).hom.app W s) at hh
    rw [hy, hz, hp₁, hp₂, hs₁, hs₂] at hh
    exact hh
  have hconstant_sections (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (opY : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶
        FrU.obj (Lr.obj (Rr.obj F)))
      (opZ : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ FrU.obj F)
      (c : ∀ S : CommRingCat.{u + 1}, S)
      (hy : ∀ W x, opY.hom.app W x = c ((Lr.obj (Rr.obj F)).obj.obj W))
      (hz : ∀ W x, opZ.hom.app W x = c (F.obj.obj W))
      (he : opY ≫ β F = opZ) (W : U.Etaleᵒᵖ) :
      (β F).hom.app W (c ((Lr.obj (Rr.obj F)).obj.obj W)) = c (F.obj.obj W) := by
    let t : 𝟙_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶
        ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) := terminal.from _
    have hh := types_congr_hom
      (congrArg (fun k : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶
        FrU.obj F ↦ k.hom.app W) he) (t.hom.app W PUnit.unit)
    change (β F).hom.app W (opY.hom.app W _) = opZ.hom.app W _ at hh
    rw [hy, hz] at hh
    exact hh
  let ε : Rr ⋙ Lr ⟶ 𝟭 _ := {
    app := fun F ↦ ⟨{
      app := fun W ↦ CommRingCat.ofHom {
        toFun := (β F).hom.app W
        map_zero' := hconstant_sections F _ _ (fun _ ↦ 0)
          (by intros; rfl) (by intros; rfl) (hzero F) W
        map_one' := hconstant_sections F _ _ (fun _ ↦ 1)
          (by intros; rfl) (by intros; rfl) (hone F) W
        map_add' := hbinary_sections F _ _ (fun S x y ↦ x + y)
          (by intros; rfl) (by intros; rfl) (hadd F) W
        map_mul' := hbinary_sections F _ _ (fun S x y ↦ x * y)
          (by intros; rfl) (by intros; rfl) (hmul F) W }
      naturality := by
        intro W W' g
        ext x
        exact types_congr_hom ((β F).hom.naturality g) x }⟩
    naturality := by
      intro F F' g
      apply FrU.map_injective
      change FrU.map (Lr.map (Rr.map g)) ≫ β F' = β F ≫ FrU.map g
      dsimp only [β]
      have he : FrU.map (Lr.map (Rr.map g)) ≫ er.hom.app (Rr.obj F') =
          er.hom.app (Rr.obj F) ≫ L.map (FrV.map (Rr.map g)) :=
        er.hom.naturality (Rr.map g)
      rw [← Category.assoc, he]
      change (er.hom.app (Rr.obj F) ≫ L.map (R.map (FrU.map g))) ≫
          a.counit.app (FrU.obj F') =
        (er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F)) ≫ FrU.map g
      have hn : L.map (R.map (FrU.map g)) ≫ a.counit.app (FrU.obj F') =
          a.counit.app (FrU.obj F) ≫ FrU.map g := a.counit_naturality (FrU.map g)
      rw [Category.assoc, hn, Category.assoc] }
  refine ⟨ε, ?_⟩
  intro F
  rfl

end AlgebraicGeometry
