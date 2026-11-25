/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-! # Multiplication and unit for a supplied ring inverse image comparison

Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-weil-pbc-supplied-ring-comparison-operations). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private local instance sheafTypesHasBinaryProduct.{uC, vC, w}
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (X Y : Sheaf J (Type w)) : HasBinaryProduct X Y :=
  have : HasBinaryProducts (Sheaf J (Type w)) := Sheaf.instHasLimitsOfShape
  HasLimitsOfShape.has_limit _

private noncomputable def ringMul.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Mul.mul (G.obj.obj W) inferInstance
       ((prod.fst : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W)
       ((prod.snd : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       have hf := ConcreteCategory.congr_hom ((prod.fst : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       have hs := ConcreteCategory.congr_hom ((prod.snd : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       dsimp at hf hs ⊢
       rw [hf, hs]
       exact (G.obj.map f).hom.map_mul _ _ |>.symm }⟩
private noncomputable def ringOne.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : ⊤_ (Sheaf J (Type w)) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_one |>.symm }⟩

/-- Source: Stacks Project, Tags 00YV and 03D2, identification of transported
ring operations by uniqueness of the lifted adjoint.
(blueprint: lem-weil-pbc-supplied-ring-comparison-operations).

Proof: Define multiplication and one as their sectionwise sheaf maps. Apply
compatibility to the identity of Lr(O) to express the underlying ring-adjunction
unit through the set unit and er.inv. Under the set adjunction, the two
projections of the inverse-image product comparison followed by er.inv become
the source projections followed by that ring unit. The multiplication transport
equation therefore becomes the assertion that this unit preserves
multiplication, checked sectionwise as a ring homomorphism. The constant one
transport equation similarly becomes preservation of one; there is only one
map to the terminal object. Cancel er.inv to recover the required equations.
This is the multiplication and unit part of the argument of
`etaleInverseImageRingLift`, applied to the supplied lift instead of a chosen
canonical lift. No choice of a lifted object and no module action is required. -/
theorem etaleInverseImageRingComparisonOperations (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    [PreservesFiniteLimits (Scheme.etaleSetPullback f)] :
    let L := Scheme.etaleSetPullback f
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let aS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    ∀ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
        Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) →
    ∃ (mulV : (FrV.obj O) ⨯ (FrV.obj O) ⟶ FrV.obj O)
      (mulU : (FrU.obj (Lr.obj O)) ⨯ (FrU.obj (Lr.obj O)) ⟶ FrU.obj (Lr.obj O))
      (oneV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ FrV.obj O)
      (oneU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ FrU.obj (Lr.obj O)),
      (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj O) ⨯ (FrV.obj O)).obj.obj W),
        mulV.hom.app W x =
          @Mul.mul (O.obj.obj W) inferInstance
          ((prod.fst : (FrV.obj O) ⨯ (FrV.obj O) ⟶ FrV.obj O).hom.app W x :
            O.obj.obj W)
          ((prod.snd : (FrV.obj O) ⨯ (FrV.obj O) ⟶ FrV.obj O).hom.app W x :
            O.obj.obj W)) ∧
      (∀ (W : U.Etaleᵒᵖ)
          (x : ((FrU.obj (Lr.obj O)) ⨯ (FrU.obj (Lr.obj O))).obj.obj W),
        mulU.hom.app W x =
          @Mul.mul ((Lr.obj O).obj.obj W) inferInstance
          ((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FrU.obj (Lr.obj O)) ⟶
            FrU.obj (Lr.obj O)).hom.app W x : (Lr.obj O).obj.obj W)
          ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FrU.obj (Lr.obj O)) ⟶
            FrU.obj (Lr.obj O)).hom.app W x : (Lr.obj O).obj.obj W)) ∧
      (∀ (W : V.Etaleᵒᵖ)
          (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
        oneV.hom.app W x = (1 : O.obj.obj W)) ∧
      (∀ (W : U.Etaleᵒᵖ)
          (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
        oneU.hom.app W x = (1 : (Lr.obj O).obj.obj W)) ∧
      L.map mulV = prodComparison L (FrV.obj O) (FrV.obj O) ≫
        prod.map (er.inv.app O) (er.inv.app O) ≫ mulU ≫ er.hom.app O ∧
      L.map oneV = terminal.from _ ≫ oneU ≫ er.hom.app O  := by
  dsimp only
  intro Lr ar er h
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
    (U.smallGrothendieckTopology @Etale)
  let R := b.sheafPushforwardContinuous (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  have hη := h O (Lr.obj O) (𝟙 _)
  rw [ar.homEquiv_id, a.homEquiv_apply] at hη
  change (sheafForget V.smallEtaleTopology).map (ar.unit.app O) =
    a.unit.app ((sheafForget V.smallEtaleTopology).obj O) ≫
      (b.sheafPushforwardContinuous (Type (u + 1))
        (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)).map
        (er.inv.app O) at hη
  let X := (sheafForget V.smallEtaleTopology).obj O
  let Y := (sheafForget U.smallEtaleTopology).obj (Lr.obj O)
  let q : L.obj (X ⨯ X) ⟶ Y ⨯ Y :=
    prodComparison L X X ≫ prod.map (er.inv.app O) (er.inv.app O)
  let t : X ⨯ X ⟶ R.obj (Y ⨯ Y) := a.unit.app (X ⨯ X) ≫ R.map q
  have ht (p : X ⨯ X ⟶ X) (p' : Y ⨯ Y ⟶ Y)
      (hp : q ≫ p' = L.map p ≫ er.inv.app O) :
      t ≫ R.map p' = p ≫ (sheafForget V.smallEtaleTopology).map (ar.unit.app O) := by
    dsimp only [t]
    have hn : a.unit.app (X ⨯ X) ≫ R.map (L.map p) = p ≫ a.unit.app X :=
      a.unit_naturality p
    rw [Category.assoc, ← R.map_comp, hp, R.map_comp, ← Category.assoc, hn,
      Category.assoc, ← hη]
  have hf := ht prod.fst prod.fst (by
    dsimp only [q]
    rw [Category.assoc, prod.map_fst, ← Category.assoc, prodComparison_fst])
  have hs := ht prod.snd prod.snd (by
    dsimp only [q]
    rw [Category.assoc, prod.map_snd, ← Category.assoc, prodComparison_snd])
  refine ⟨ringMul _ O, ringMul _ (Lr.obj O), ringOne _ O, ringOne _ (Lr.obj O),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (intros; rfl)
  · apply (cancel_mono (er.inv.app O)).1
    change L.map (ringMul _ O) ≫ er.inv.app O =
      (q ≫ ringMul _ (Lr.obj O) ≫ er.hom.app O) ≫ er.inv.app O
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app (X ⨯ X) ≫ R.map (L.map (ringMul _ O) ≫ er.inv.app O) =
      a.unit.app (X ⨯ X) ≫ R.map (q ≫ ringMul _ (Lr.obj O))
    have hn : a.unit.app (X ⨯ X) ≫ R.map (L.map (ringMul _ O)) =
        ringMul _ O ≫ a.unit.app X := a.unit_naturality (ringMul _ O)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc, ← hη]
    change ringMul _ O ≫ (sheafForget V.smallEtaleTopology).map (ar.unit.app O) =
      t ≫ R.map (ringMul _ (Lr.obj O))
    ext W x
    have hf' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hf) x
    have hs' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hs) x
    change (prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (ar.unit.app O).hom.app W ((prod.fst : X ⨯ X ⟶ X).hom.app W x) at hf'
    change (prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (ar.unit.app O).hom.app W ((prod.snd : X ⨯ X ⟶ X).hom.app W x) at hs'
    change (ar.unit.app O).hom.app W
        (@Mul.mul (O.obj.obj W) inferInstance
          ((prod.fst : X ⨯ X ⟶ X).hom.app W x)
          ((prod.snd : X ⨯ X ⟶ X).hom.app W x)) =
      @Mul.mul ((Lr.obj O).obj.obj (b.op.obj W)) inferInstance
        ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
        ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hf', hs']
    exact ((ar.unit.app O).hom.app W).hom.map_mul _ _
  · apply (cancel_mono (er.inv.app O)).1
    change L.map (ringOne _ O) ≫ er.inv.app O =
      (terminal.from _ ≫ ringOne _ (Lr.obj O) ≫ er.hom.app O) ≫ er.inv.app O
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
      R.map (L.map (ringOne _ O) ≫ er.inv.app O) =
      a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
        R.map (terminal.from _ ≫ ringOne _ (Lr.obj O))
    have hn : a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
        R.map (L.map (ringOne _ O)) =
        ringOne _ O ≫ a.unit.app ((sheafForget V.smallEtaleTopology).obj O) :=
      a.unit_naturality (ringOne _ O)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc, ← hη]
    ext W x
    exact ((ar.unit.app O).hom.app W).hom.map_one


end AlgebraicGeometry
