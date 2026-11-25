/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftOperations
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Addition transport for supplied inverse image comparisons

Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-comparison-addition). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

private theorem tensor_add_transport
    {C D : Type*} [Category C] [Category D]
    [HasBinaryProducts C] [HasBinaryProducts D]
    (L : C ⥤ D) (X : C) (Y : D) [IsIso (prodComparison L X X)]
    (e : Y ≅ L.obj X) {T : C} {S : D} (v : X ⨯ X ≅ T) (w : Y ⨯ Y ≅ S)
    (m : X ⨯ X ⟶ X) (n : Y ⨯ Y ⟶ Y)
    (h : L.map m = prodComparison L X X ≫ prod.map e.inv e.inv ≫ n ≫ e.hom) :
    (w.inv ≫ prod.map e.hom e.hom ≫ inv (prodComparison L X X) ≫ L.map v.hom) ≫
      L.map (v.inv ≫ m) ≫ e.inv = w.inv ≫ n := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc, v.hom_inv_id, L.map_id, Category.id_comp, h]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  simp [← Category.assoc, prod.map_map]

private theorem tensor_to_product_fst
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (X : Sheaf J (Type (u + 1))) :
    ((limit.isLimit (pair X X)).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X X)).inv ≫
        (prod.fst : X ⨯ X ⟶ X) = CartesianMonoidalCategory.fst X X :=
  (limit.isLimit (pair X X)).conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X X) ⟨.left⟩

private theorem tensor_to_product_snd
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (X : Sheaf J (Type (u + 1))) :
    ((limit.isLimit (pair X X)).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X X)).inv ≫
        (prod.snd : X ⨯ X ⟶ X) = CartesianMonoidalCategory.snd X X :=
  (limit.isLimit (pair X X)).conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X X) ⟨.right⟩

-- The dependent sheaf comparisons require repeated unfolding of the forgetful functors.
/-- Source: Stacks Project, Tags 00X6, 00YV, and 03D2, proof of
lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-comparison-addition).

Proof: Apply etaleInverseImageAlgebraicStructures to obtain the canonical
abelian and commutative-ring lifts and their addition transport equations.
The ring lift is identified with Lr by uniqueness of left adjoints to Rr;
the abelian lift is the fixed La. Apply the two hom-equivalence compatibility
hypotheses to identity maps and use injectivity of the set adjunction's hom
bijection. This identifies the supplied comparisons with the canonical ones,
after the unique ring isomorphism. Naturality of that isomorphism and the fact
that its components are ring homomorphisms carry canonical addition to addition
on Lr. The abelian comparison is identified in the same manner. Precompose
categorical addition maps with the canonical tensor-to-product isomorphisms;
their section values are the sums of the two coordinates, because these
isomorphisms preserve both projections. Substitute the canonical transport
equations and cancel inverse comparison pairs to obtain the two equations.
No scalar action or distributivity law is used. -/
theorem etaleInverseImageComparisonAddition (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    [PreservesFiniteLimits (Scheme.etaleSetPullback f)] :
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
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
    let OR := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
    let OV := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
    ∀ G : SheafOfModules.{u + 1} OV,
    let X := FrV.obj O
    let Y := FaV.obj (FV.obj G)
    let X' := FrU.obj (Lr.obj O)
    let Y' := FaU.obj (La.obj (FV.obj G))
    let eV := fun (P Q : Sheaf V.smallEtaleTopology (Type (u + 1))) ↦
      (limit.isLimit (pair P Q)).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
    let eU := fun (P Q : Sheaf U.smallEtaleTopology (Type (u + 1))) ↦
      (limit.isLimit (pair P Q)).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
    ∃ (axV : X ⊗ X ⟶ X) (ayV : Y ⊗ Y ⟶ Y)
      (ax : X' ⊗ X' ⟶ X') (ay : Y' ⊗ Y' ⟶ Y'),
      (∀ (W : V.Etaleᵒᵖ) (r s : O.obj.obj W), axV.hom.app W (r, s) = r + s) ∧
      (∀ (W : V.Etaleᵒᵖ) (x y : G.val.obj W), ayV.hom.app W (x, y) = x + y) ∧
      (∀ (W : U.Etaleᵒᵖ) (r s : OR.obj.obj W), ax.hom.app W (r, s) = r + s) ∧
      (∀ (W : U.Etaleᵒᵖ) (x y : (La.obj (FV.obj G)).obj.obj W),
        ay.hom.app W (x, y) = x + y) ∧
      ((eU X' X').inv ≫ prod.map (er.hom.app O) (er.hom.app O) ≫
        inv (prodComparison L X X) ≫ L.map (eV X X).hom) ≫
          L.map axV ≫ er.inv.app O = ax ∧
      ((eU Y' Y').inv ≫
        prod.map (ea.hom.app (FV.obj G)) (ea.hom.app (FV.obj G)) ≫
        inv (prodComparison L Y Y) ≫ L.map (eV Y Y).hom) ≫
          L.map ayV ≫ ea.inv.app (FV.obj G) = ay := by
  dsimp only
  intro Lr ar er ea hcompat G
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
    (U.smallGrothendieckTopology @Etale)
  let R := b.sheafPushforwardContinuous (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  have hη := hcompat.1 O (Lr.obj O) (𝟙 _)
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
  have hr : L.map (ringAdd _ O) = q ≫ ringAdd _ (Lr.obj O) ≫ er.hom.app O := by
    apply (cancel_mono (er.inv.app O)).1
    change L.map (ringAdd _ O) ≫ er.inv.app O =
      (q ≫ ringAdd _ (Lr.obj O) ≫ er.hom.app O) ≫ er.inv.app O
    simp only [Category.assoc, er.hom_inv_id_app]
    apply (a.homEquiv _ _).injective
    change a.unit.app (X ⨯ X) ≫ R.map (L.map (ringAdd _ O) ≫ er.inv.app O) =
      a.unit.app (X ⨯ X) ≫ R.map (q ≫ ringAdd _ (Lr.obj O))
    have hn : a.unit.app (X ⨯ X) ≫ R.map (L.map (ringAdd _ O)) =
        ringAdd _ O ≫ a.unit.app X := a.unit_naturality (ringAdd _ O)
    rw [R.map_comp, R.map_comp, ← Category.assoc, hn, Category.assoc, ← hη]
    change ringAdd _ O ≫ (sheafForget V.smallEtaleTopology).map (ar.unit.app O) =
      t ≫ R.map (ringAdd _ (Lr.obj O))
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
        (@Add.add (O.obj.obj W) inferInstance
          ((prod.fst : X ⨯ X ⟶ X).hom.app W x)
          ((prod.snd : X ⨯ X ⟶ X).hom.app W x)) =
      @Add.add ((Lr.obj O).obj.obj (b.op.obj W)) inferInstance
        ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
        ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hf', hs']
    exact ((ar.unit.app O).hom.app W).hom.map_add _ _
  obtain ⟨addV, addU, zeroV, zeroU, negV, negU, hv, hu, ha, _⟩ :=
    etaleInverseImageAbelianLift_operations U V f inferInstance ea hcompat.2
      ((SheafOfModules.toSheaf _).obj G)
  let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
  let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
  let YV := FaV.obj ((SheafOfModules.toSheaf _).obj G)
  let YU := FaU.obj ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj
    ((SheafOfModules.toSheaf _).obj G))
  let eV := fun (P Q : Sheaf V.smallEtaleTopology (Type (u + 1))) ↦
    (limit.isLimit (pair P Q)).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
  let eU := fun (P Q : Sheaf U.smallEtaleTopology (Type (u + 1))) ↦
    (limit.isLimit (pair P Q)).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
  refine ⟨(eV X X).inv ≫ ringAdd _ O, (eV YV YV).inv ≫ addV,
    (eU Y Y).inv ≫ ringAdd _ (Lr.obj O), (eU YU YU).inv ≫ addU,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W r s
    have hf := congrArg (fun k ↦ k.hom.app W (r, s))
      (tensor_to_product_fst V.smallEtaleTopology X)
    have hs := congrArg (fun k ↦ k.hom.app W (r, s))
      (tensor_to_product_snd V.smallEtaleTopology X)
    change @Add.add (O.obj.obj W) inferInstance
      ((prod.fst : X ⨯ X ⟶ X).hom.app W ((eV X X).inv.hom.app W (r, s)))
      ((prod.snd : X ⨯ X ⟶ X).hom.app W ((eV X X).inv.hom.app W (r, s))) = r + s
    dsimp at hf hs
    erw [hf, hs]
    rfl
  · intro W x y
    change addV.hom.app W ((eV YV YV).inv.hom.app W (x, y)) = x + y
    rw [hv]
    have hf := congrArg (fun k ↦ k.hom.app W (x, y))
      (tensor_to_product_fst V.smallEtaleTopology YV)
    have hs := congrArg (fun k ↦ k.hom.app W (x, y))
      (tensor_to_product_snd V.smallEtaleTopology YV)
    dsimp at hf hs
    erw [hf, hs]
    rfl
  · intro W r s
    have hf := congrArg (fun k ↦ k.hom.app W (r, s))
      (tensor_to_product_fst U.smallEtaleTopology Y)
    have hs := congrArg (fun k ↦ k.hom.app W (r, s))
      (tensor_to_product_snd U.smallEtaleTopology Y)
    change @Add.add ((Lr.obj O).obj.obj W) inferInstance
      ((prod.fst : Y ⨯ Y ⟶ Y).hom.app W ((eU Y Y).inv.hom.app W (r, s)))
      ((prod.snd : Y ⨯ Y ⟶ Y).hom.app W ((eU Y Y).inv.hom.app W (r, s))) = r + s
    dsimp at hf hs
    erw [hf, hs]
    rfl
  · intro W x y
    change addU.hom.app W ((eU YU YU).inv.hom.app W (x, y)) = x + y
    rw [hu]
    have hf := congrArg (fun k ↦ k.hom.app W (x, y))
      (tensor_to_product_fst U.smallEtaleTopology YU)
    have hs := congrArg (fun k ↦ k.hom.app W (x, y))
      (tensor_to_product_snd U.smallEtaleTopology YU)
    dsimp at hf hs
    erw [hf, hs]
    rfl
  · exact tensor_add_transport L X Y (er.app O) (eV X X) (eU Y Y)
      (ringAdd _ O) (ringAdd _ (Lr.obj O)) hr
  · exact tensor_add_transport L YV YU (ea.app ((SheafOfModules.toSheaf _).obj G))
      (eV YV YV) (eU YU YU) addV addU ha


end AlgebraicGeometry
