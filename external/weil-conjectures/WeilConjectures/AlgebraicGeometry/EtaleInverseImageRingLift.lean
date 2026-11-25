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
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageRingAdjunction
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# EtaleInverseImageRingLift

Source: Stacks Project, Sites and Sheaves, Proposition 00YV.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private local instance sheafTypesHasBinaryProduct.{uC, vC, w}
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (X Y : Sheaf J (Type w)) : HasBinaryProduct X Y :=
  have : HasBinaryProducts (Sheaf J (Type w)) := Sheaf.instHasLimitsOfShape
  HasLimitsOfShape.has_limit _

private noncomputable def ringAdd.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (G.obj.obj W) inferInstance
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
       exact (G.obj.map f).hom.map_add _ _ |>.symm }⟩
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
private def ringNeg.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Neg.neg (G.obj.obj W) inferInstance x)
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_neg x |>.symm }⟩
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

-- The exposed operation formulas require repeated reduction of the étale sheaf functors.
set_option backward.isDefEq.respectTransparency false in

/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV and its preceding
quadruple/sextuple descriptions.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-lift).

Proof: Identify ring-valued sheaves on both sites with internal commutative ring
objects using `sheaves_algebraicStructures_objects`. Apply the ring clause of
`Adjunction.liftsGroupRingObjects` to the set adjunction and `hL`. Transport its
left functor through the inverse ring-object/sheaf functors to obtain `Lr`.
The right functor so obtained is canonically the sectionwise direct image `Rr`:
evaluation at each base-changed object preserves all five ring operations and all
restriction homomorphisms. Use this identification to transport the lifted adjunction
and call it `ar`. The underlying left comparison gives `er`; restricting the set
adjunction bijection gives the displayed hom-set equation. Choose addition, zero,
negation, multiplication and one to be the sectionwise operations under the
ring-object/sheaf identification. The five lift formulas, expressed through `er`,
give their transport equations below. For the binary operations compose the inverse
product comparison with the two inverse components of `er`, and then cancel the
comparison; for the constants use the unique map to the terminal object; for negation
use the inverse component directly. Their section formulas are precisely those of
the identification of ring sheaves with ring objects. The unit equation is not
assumed here and will be deduced from the hom-set equation in the parent theorem. -/
theorem etaleInverseImageRingLift (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
        (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
          FrV.map (ar.homEquiv G F h) =
            a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
        (∀ G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1},
          ∃ (addV : (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G))
            (addU : (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶ (FrU.obj (Lr.obj G)))
            (zeroV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ (FrV.obj G))
            (zeroU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ (FrU.obj (Lr.obj G)))
            (negV : (FrV.obj G) ⟶ (FrV.obj G))
            (negU : (FrU.obj (Lr.obj G)) ⟶ (FrU.obj (Lr.obj G)))
            (mulV : (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G))
            (mulU : (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶ (FrU.obj (Lr.obj G)))
            (oneV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ (FrV.obj G))
            (oneU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ (FrU.obj (Lr.obj G))),
            (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj G) ⨯ (FrV.obj G)).obj.obj W),
              addV.hom.app W x =
                (@Add.add (G.obj.obj W) inferInstance
                  ((prod.fst : (FrV.obj G) ⨯ (FrV.obj G) ⟶
                      (FrV.obj G)).hom.app W x : G.obj.obj W)
                  ((prod.snd :
                    (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G)).hom.app W x :
                    G.obj.obj W))) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : ((FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G))).obj.obj W),
              addU.hom.app W x =
                (@Add.add ((Lr.obj G).obj.obj W) inferInstance
                  ((prod.fst :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W)
                  ((prod.snd :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W))) ∧
            L.map addV = prodComparison L (FrV.obj G) (FrV.obj G) ≫
              prod.map (er.inv.app G) (er.inv.app G) ≫ addU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroV.hom.app W x = (0 : G.obj.obj W)) ∧
            (∀ (W : U.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroU.hom.app W x = (0 : (Lr.obj G).obj.obj W)) ∧
            L.map zeroV = terminal.from _ ≫ zeroU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ) (x : (FrV.obj G).obj.obj W),
              negV.hom.app W x = @Neg.neg (G.obj.obj W) inferInstance x) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : (FrU.obj (Lr.obj G)).obj.obj W),
              negU.hom.app W x = @Neg.neg ((Lr.obj G).obj.obj W) inferInstance x) ∧
            L.map negV = er.inv.app G ≫ negU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj G) ⨯ (FrV.obj G)).obj.obj W),
              mulV.hom.app W x =
                (@Mul.mul (G.obj.obj W) inferInstance
                  ((prod.fst : (FrV.obj G) ⨯ (FrV.obj G) ⟶
                      (FrV.obj G)).hom.app W x : G.obj.obj W)
                  ((prod.snd :
                    (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G)).hom.app W x :
                    G.obj.obj W))) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : ((FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G))).obj.obj W),
              mulU.hom.app W x =
                (@Mul.mul ((Lr.obj G).obj.obj W) inferInstance
                  ((prod.fst :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W)
                  ((prod.snd :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W))) ∧
            L.map mulV = prodComparison L (FrV.obj G) (FrV.obj G) ≫
              prod.map (er.inv.app G) (er.inv.app G) ≫ mulU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              oneV.hom.app W x = (1 : G.obj.obj W)) ∧
            (∀ (W : U.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              oneU.hom.app W x = (1 : (Lr.obj G).obj.obj W)) ∧
            L.map oneV = terminal.from _ ≫ oneU ≫ er.hom.app G) := by
  obtain ⟨Lr, ar, er, hr⟩ := etaleInverseImageRingAdjunction U V f hL
  refine ⟨Lr, ar, er, hr, ?_⟩
  intro G
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
    (U.smallGrothendieckTopology @Etale)
  let R := b.sheafPushforwardContinuous (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  have hη := hr G (Lr.obj G) (𝟙 _)
  rw [ar.homEquiv_id, a.homEquiv_apply] at hη
  change (sheafForget V.smallEtaleTopology).map (ar.unit.app G) =
    a.unit.app ((sheafForget V.smallEtaleTopology).obj G) ≫
      (b.sheafPushforwardContinuous (Type (u + 1))
        (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)).map
        (er.inv.app G) at hη
  let X := (sheafForget V.smallEtaleTopology).obj G
  let Y := (sheafForget U.smallEtaleTopology).obj (Lr.obj G)
  let q : L.obj (X ⨯ X) ⟶ Y ⨯ Y :=
    prodComparison L X X ≫ prod.map (er.inv.app G) (er.inv.app G)
  let t : X ⨯ X ⟶ R.obj (Y ⨯ Y) := a.unit.app (X ⨯ X) ≫ R.map q
  have ht (p : X ⨯ X ⟶ X) (p' : Y ⨯ Y ⟶ Y)
      (hp : q ≫ p' = L.map p ≫ er.inv.app G) :
      t ≫ R.map p' = p ≫ (sheafForget V.smallEtaleTopology).map (ar.unit.app G) := by
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
  refine ⟨ringAdd _ G, ringAdd _ (Lr.obj G), ringZero _ G,
    ringZero _ (Lr.obj G), ringNeg _ G, ringNeg _ (Lr.obj G),
    ringMul _ G, ringMul _ (Lr.obj G), ringOne _ G, ringOne _ (Lr.obj G),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (intros; rfl)
  · apply (cancel_mono (er.inv.app G)).1
    change L.map (ringAdd _ G) ≫ er.inv.app G =
      (q ≫ ringAdd _ (Lr.obj G) ≫ er.hom.app G) ≫ er.inv.app G
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app (X ⨯ X) ≫ R.map (L.map (ringAdd _ G) ≫ er.inv.app G) =
      a.unit.app (X ⨯ X) ≫ R.map (q ≫ ringAdd _ (Lr.obj G))
    have hn : a.unit.app (X ⨯ X) ≫ R.map (L.map (ringAdd _ G)) =
        ringAdd _ G ≫ a.unit.app X := a.unit_naturality (ringAdd _ G)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc, ← hη]
    change ringAdd _ G ≫ (sheafForget V.smallEtaleTopology).map (ar.unit.app G) =
      t ≫ R.map (ringAdd _ (Lr.obj G))
    ext W x
    have hf' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hf) x
    have hs' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hs) x
    change (prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (ar.unit.app G).hom.app W ((prod.fst : X ⨯ X ⟶ X).hom.app W x) at hf'
    change (prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (ar.unit.app G).hom.app W ((prod.snd : X ⨯ X ⟶ X).hom.app W x) at hs'
    change (ar.unit.app G).hom.app W
        (@Add.add (G.obj.obj W) inferInstance
          ((prod.fst : X ⨯ X ⟶ X).hom.app W x)
          ((prod.snd : X ⨯ X ⟶ X).hom.app W x)) =
      @Add.add ((Lr.obj G).obj.obj (b.op.obj W)) inferInstance
        ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
        ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hf', hs']
    exact ((ar.unit.app G).hom.app W).hom.map_add _ _
  · apply (cancel_mono (er.inv.app G)).1
    change L.map (ringZero _ G) ≫ er.inv.app G =
      (terminal.from _ ≫ ringZero _ (Lr.obj G) ≫ er.hom.app G) ≫ er.inv.app G
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
      R.map (L.map (ringZero _ G) ≫ er.inv.app G) =
      a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
        R.map (terminal.from _ ≫ ringZero _ (Lr.obj G))
    have hn : a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
        R.map (L.map (ringZero _ G)) =
        ringZero _ G ≫ a.unit.app ((sheafForget V.smallEtaleTopology).obj G) :=
      a.unit_naturality (ringZero _ G)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc, ← hη]
    ext W x
    exact ((ar.unit.app G).hom.app W).hom.map_zero
  · apply (cancel_mono (er.inv.app G)).1
    change L.map (ringNeg _ G) ≫ er.inv.app G =
      (er.inv.app G ≫ ringNeg _ (Lr.obj G) ≫ er.hom.app G) ≫ er.inv.app G
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app ((sheafForget V.smallEtaleTopology).obj G) ≫
      R.map (L.map (ringNeg _ G) ≫ er.inv.app G) =
      a.unit.app ((sheafForget V.smallEtaleTopology).obj G) ≫
        R.map (er.inv.app G ≫ ringNeg _ (Lr.obj G))
    have hn : a.unit.app ((sheafForget V.smallEtaleTopology).obj G) ≫
        R.map (L.map (ringNeg _ G)) =
        ringNeg _ G ≫ a.unit.app ((sheafForget V.smallEtaleTopology).obj G) :=
      a.unit_naturality (ringNeg _ G)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc]
    rw [← hη, ← Category.assoc, ← hη]
    ext W x
    exact ((ar.unit.app G).hom.app W).hom.map_neg x
  · apply (cancel_mono (er.inv.app G)).1
    change L.map (ringMul _ G) ≫ er.inv.app G =
      (q ≫ ringMul _ (Lr.obj G) ≫ er.hom.app G) ≫ er.inv.app G
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app (X ⨯ X) ≫ R.map (L.map (ringMul _ G) ≫ er.inv.app G) =
      a.unit.app (X ⨯ X) ≫ R.map (q ≫ ringMul _ (Lr.obj G))
    have hn : a.unit.app (X ⨯ X) ≫ R.map (L.map (ringMul _ G)) =
        ringMul _ G ≫ a.unit.app X := a.unit_naturality (ringMul _ G)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc, ← hη]
    change ringMul _ G ≫ (sheafForget V.smallEtaleTopology).map (ar.unit.app G) =
      t ≫ R.map (ringMul _ (Lr.obj G))
    ext W x
    have hf' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hf) x
    have hs' := types_congr_hom
      (congrArg (fun k : X ⨯ X ⟶ R.obj Y ↦ k.hom.app W) hs) x
    change (prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (ar.unit.app G).hom.app W ((prod.fst : X ⨯ X ⟶ X).hom.app W x) at hf'
    change (prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      (ar.unit.app G).hom.app W ((prod.snd : X ⨯ X ⟶ X).hom.app W x) at hs'
    change (ar.unit.app G).hom.app W
        (@Mul.mul (G.obj.obj W) inferInstance
          ((prod.fst : X ⨯ X ⟶ X).hom.app W x)
          ((prod.snd : X ⨯ X ⟶ X).hom.app W x)) =
      @Mul.mul ((Lr.obj G).obj.obj (b.op.obj W)) inferInstance
        ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
        ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hf', hs']
    exact ((ar.unit.app G).hom.app W).hom.map_mul _ _
  · apply (cancel_mono (er.inv.app G)).1
    change L.map (ringOne _ G) ≫ er.inv.app G =
      (terminal.from _ ≫ ringOne _ (Lr.obj G) ≫ er.hom.app G) ≫ er.inv.app G
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
      R.map (L.map (ringOne _ G) ≫ er.inv.app G) =
      a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
        R.map (terminal.from _ ≫ ringOne _ (Lr.obj G))
    have hn : a.unit.app (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))) ≫
        R.map (L.map (ringOne _ G)) =
        ringOne _ G ≫ a.unit.app ((sheafForget V.smallEtaleTopology).obj G) :=
      a.unit_naturality (ringOne _ G)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc, ← hη]
    ext W x
    exact ((ar.unit.app G).hom.app W).hom.map_one

end AlgebraicGeometry
