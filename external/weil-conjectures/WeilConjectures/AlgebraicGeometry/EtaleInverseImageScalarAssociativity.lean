/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageRingComparisonOperations
import WeilConjectures.CategoryTheory.TransportScalarActionDiagrams

/-! # Associativity and unit of the transported scalar action

Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-associativity). -/

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

private noncomputable def pairSection {C : Type*} [Category C]
    {J : GrothendieckTopology C} (X Y : Sheaf J (Type (u + 1)))
    (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) : (X ⨯ Y).obj.obj W :=
  ((limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)).inv.hom.app W (x, y)

private theorem section_comp {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type (u + 1))}
    (f : X ⟶ Y) (g : Y ⟶ Z) (W : Cᵒᵖ) (x : X.obj.obj W) :
    (f ≫ g).hom.app W x = g.hom.app W (f.hom.app W x) := rfl

private theorem section_id {C : Type*} [Category C]
    {J : GrothendieckTopology C} (X : Sheaf J (Type (u + 1)))
    (W : Cᵒᵖ) (x : X.obj.obj W) : (𝟙 X : X ⟶ X).hom.app W x = x := rfl

private theorem section_fst_lift {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type (u + 1))}
    (f : X ⟶ Y) (g : X ⟶ Z) (W : Cᵒᵖ) (x : X.obj.obj W) :
    (prod.fst : Y ⨯ Z ⟶ Y).hom.app W ((prod.lift f g).hom.app W x) =
      f.hom.app W x :=
  ConcreteCategory.congr_hom (C := Type (u + 1))
    (congrArg (fun k ↦ k.hom.app W) (prod.lift_fst f g)) x

private theorem section_snd_lift {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type (u + 1))}
    (f : X ⟶ Y) (g : X ⟶ Z) (W : Cᵒᵖ) (x : X.obj.obj W) :
    (prod.snd : Y ⨯ Z ⟶ Z).hom.app W ((prod.lift f g).hom.app W x) =
      g.hom.app W x :=
  ConcreteCategory.congr_hom (C := Type (u + 1))
    (congrArg (fun k ↦ k.hom.app W) (prod.lift_snd f g)) x

private theorem section_fst_map {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y Z T : Sheaf J (Type (u + 1))}
    (f : X ⟶ Y) (g : Z ⟶ T) (W : Cᵒᵖ) (x : (X ⨯ Z).obj.obj W) :
    (prod.fst : Y ⨯ T ⟶ Y).hom.app W ((prod.map f g).hom.app W x) =
      f.hom.app W ((prod.fst : X ⨯ Z ⟶ X).hom.app W x) :=
  ConcreteCategory.congr_hom (C := Type (u + 1))
    (congrArg (fun k ↦ k.hom.app W) (prod.map_fst f g)) x

private theorem section_snd_map {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y Z T : Sheaf J (Type (u + 1))}
    (f : X ⟶ Y) (g : Z ⟶ T) (W : Cᵒᵖ) (x : (X ⨯ Z).obj.obj W) :
    (prod.snd : Y ⨯ T ⟶ T).hom.app W ((prod.map f g).hom.app W x) =
      g.hom.app W ((prod.snd : X ⨯ Z ⟶ Z).hom.app W x) :=
  ConcreteCategory.congr_hom (C := Type (u + 1))
    (congrArg (fun k ↦ k.hom.app W) (prod.map_snd f g)) x

private theorem pairSection_fst {C : Type*} [Category C]
    {J : GrothendieckTopology C} (X Y : Sheaf J (Type (u + 1)))
    (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (prod.fst : X ⨯ Y ⟶ X).hom.app W (pairSection X Y W x y) = x := by
  let e := (limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
  have hh : e.inv ≫ (prod.fst : X ⨯ Y ⟶ X) = CartesianMonoidalCategory.fst X Y :=
    IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit (pair X Y))
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.left⟩
  exact congrArg (fun k ↦ k.hom.app W (x, y)) hh

private theorem pairSection_snd {C : Type*} [Category C]
    {J : GrothendieckTopology C} (X Y : Sheaf J (Type (u + 1)))
    (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (prod.snd : X ⨯ Y ⟶ Y).hom.app W (pairSection X Y W x y) = y := by
  let e := (limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
  have hh : e.inv ≫ (prod.snd : X ⨯ Y ⟶ Y) = CartesianMonoidalCategory.snd X Y :=
    IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit (pair X Y))
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.right⟩
  exact congrArg (fun k ↦ k.hom.app W (x, y)) hh

private theorem pairSection_eta {C : Type*} [Category C]
    {J : GrothendieckTopology C} (X Y : Sheaf J (Type (u + 1)))
    (W : Cᵒᵖ) (z : (X ⨯ Y).obj.obj W) :
    pairSection X Y W ((prod.fst : X ⨯ Y ⟶ X).hom.app W z)
      ((prod.snd : X ⨯ Y ⟶ Y).hom.app W z) = z := by
  let e := (limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
  have hp : e.hom.hom.app W z =
      ((prod.fst : X ⨯ Y ⟶ X).hom.app W z,
        (prod.snd : X ⨯ Y ⟶ Y).hom.app W z) := by
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (C := Type (u + 1)) (congrArg (fun k ↦ k.hom.app W)
        (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (pair X Y))
          (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.left⟩)) z
    · exact ConcreteCategory.congr_hom (C := Type (u + 1)) (congrArg (fun k ↦ k.hom.app W)
        (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (pair X Y))
          (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.right⟩)) z
  change e.inv.hom.app W _ = z
  rw [← hp]
  exact ConcreteCategory.congr_hom (C := Type (u + 1))
    (congrArg (fun k ↦ k.hom.app W) e.hom_inv_id) z

/-- Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-associativity).

Proof: Obtain the canonical ring and abelian lifts and the multiplication
and one transport equations from `etaleInverseImageAlgebraicStructures`.
As in the additive case, uniqueness of the lifted left adjoints and the two
assumed hom-equivalence equations identify the supplied er and ea with the
canonical comparisons after the lifted adjoint isomorphisms. Consequently the
multiplication and one of Lr(O) are the transported multiplication and one of O.

The source associativity diagram on (O times O) times G equates multiplication
of the two scalar factors followed by muV with the iterated action of the second
scalar and then the first. The source unit diagram on G inserts the constant
one in the first factor and applies muV; it equals the identity. Check both
diagrams on sections by the assumed formula for muV and the source module's
`mul_smul` and `one_smul` axioms. Apply L to these equalities. Rewrite the
triple-product comparison by its projections and naturality, and substitute
the multiplication transport formula; cancelling er and ea gives the
associativity diagram for mu. For the unit diagram use preservation of the
terminal object and its unique map, together with the one transport formula.
Evaluate the resulting diagrams at ((r,s),x) and at x. Sectionwise products
identify these evaluations with the two displayed equalities. This proves
associativity and the unit without assuming or asserting distributivity. -/
theorem etaleInverseImageScalarAssociativity (U V : Scheme.{u}) (f : U ⟶ V)
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
    ∀ muV : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶ (FaV.obj (FV.obj G)),
      (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj O) ⨯ (FaV.obj (FV.obj G))).obj.obj W),
        muV.hom.app W x =
          @SMul.smul (O.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
            ((prod.fst : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
              FrV.obj O).hom.app W x : O.obj.obj W)
            ((prod.snd : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
              FaV.obj (FV.obj G)).hom.app W x : G.val.obj W)) →
    let A := La.obj (FV.obj G)
    let mu := prod.map (er.hom.app O) (ea.hom.app (FV.obj G)) ≫
      inv (prodComparison L (FrV.obj O) (FaV.obj (FV.obj G))) ≫
      L.map muV ≫ ea.inv.app (FV.obj G)
    let e : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ≅
        (FrU.obj (Lr.obj O)) ⊗ (FaU.obj A) :=
      (limit.isLimit _).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
    let act : ∀ W : U.Etaleᵒᵖ, OR.obj.obj W → A.obj.obj W → A.obj.obj W :=
      fun W r x ↦ (e.inv ≫ mu).hom.app W (r, x)
    ∀ W : U.Etaleᵒᵖ,
      (∀ (r s : OR.obj.obj W) (x : A.obj.obj W),
        act W (r * s) x = act W r (act W s x)) ∧
      (∀ x : A.obj.obj W, act W 1 x = x)
    := by
  dsimp only
  intro Lr ar er ea h G muV hmu
  obtain ⟨mulV, mulU, oneV, oneU, hmv, hmuU, hov, hou, hMul, hOne⟩ :=
    etaleInverseImageRingComparisonOperations U V f O Lr ar er h.1
  let RV := (sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj O
  let AV := (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
    ((SheafOfModules.toSheaf.{u + 1} _).obj G)
  let RU := (sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj O)
  let AU := (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj
      ((SheafOfModules.toSheaf.{u + 1} _).obj G))
  have hAssoc : prod.map mulV (𝟙 AV) ≫ muV =
      prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ muV) ≫ muV := by
    dsimp only [RV, AV]
    ext W z
    change (prod.map mulV (𝟙 AV) ≫ muV).hom.app W z =
      (prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ muV) ≫ muV).hom.app W z
    dsimp only [AV, RV]
    simp only [section_comp, hmu, hmv, section_fst_map, section_snd_map,
      section_fst_lift, section_snd_lift, section_id]
    exact @mul_smul (O.obj.obj W) (G.val.obj W) _
      (G.val.obj W).isModule.toMulAction.toSemigroupAction _ _ _
  have hUnit : prod.lift (terminal.from AV ≫ oneV) (𝟙 AV) ≫ muV = 𝟙 AV := by
    dsimp only [RV, AV]
    ext W z
    change (prod.lift (terminal.from AV ≫ oneV) (𝟙 AV) ≫ muV).hom.app W z = z
    dsimp only [AV, RV]
    simp only [section_comp, hmu, section_fst_lift, section_snd_lift, section_id, hov]
    exact @one_smul (O.obj.obj W) (G.val.obj W) _ (G.val.obj W).isModule.toMulAction _
  have ht := transportScalarActionDiagrams (Scheme.etaleSetPullback f) RV AV RU AU
    (er.app O) (ea.app ((SheafOfModules.toSheaf.{u + 1} _).obj G))
    mulV mulU oneV oneU muV hMul hOne hAssoc hUnit
  let mu : RU ⨯ AU ⟶ AU := prod.map (er.hom.app O)
      (ea.hom.app ((SheafOfModules.toSheaf.{u + 1} _).obj G)) ≫
    inv (prodComparison (Scheme.etaleSetPullback f) RV AV) ≫
      (Scheme.etaleSetPullback f).map muV ≫
      ea.inv.app ((SheafOfModules.toSheaf.{u + 1} _).obj G)
  let act : ∀ W : U.Etaleᵒᵖ, (Lr.obj O).obj.obj W → AU.obj.obj W → AU.obj.obj W :=
    fun W r x ↦ mu.hom.app W (pairSection RU AU W r x)
  change ∀ W : U.Etaleᵒᵖ,
    (∀ (r s : (Lr.obj O).obj.obj W) (x : AU.obj.obj W),
      act W (r * s) x = act W r (act W s x)) ∧
    (∀ x : AU.obj.obj W, act W 1 x = x)
  have heval (W : U.Etaleᵒᵖ) (z : (RU ⨯ AU).obj.obj W) :
      mu.hom.app W z = act W
        ((prod.fst : RU ⨯ AU ⟶ RU).hom.app W z)
        ((prod.snd : RU ⨯ AU ⟶ AU).hom.app W z) := by
    exact congrArg (fun q ↦ mu.hom.app W q) (pairSection_eta RU AU W z).symm
  intro W
  constructor
  · intro r s x
    have heq := congrArg
      (fun k : (RU ⨯ RU) ⨯ AU ⟶ AU ↦ k.hom.app W
        (pairSection (RU ⨯ RU) AU W (pairSection RU RU W r s) x)) ht.1
    change (prod.map mulU (𝟙 AU) ≫ mu).hom.app W _ =
      (prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ mu) ≫ mu).hom.app W _ at heq
    simp only [section_comp] at heq
    rw [heval, heval] at heq
    dsimp only [RU, AU] at heq
    simp only [section_comp, section_fst_map, section_snd_map,
      section_fst_lift, section_snd_lift, section_id, pairSection_fst,
      pairSection_snd] at heq
    have hm := hmuU W (pairSection RU RU W r s)
    dsimp only [RU] at hm
    simp only [pairSection_fst, pairSection_snd] at hm
    rw [hm, heval] at heq
    dsimp only [RU, AU] at heq
    simp only [section_fst_lift, section_snd_lift, section_comp,
      pairSection_fst, pairSection_snd] at heq
    exact heq
  · intro x
    have heq := congrArg (fun k : AU ⟶ AU ↦ k.hom.app W x) ht.2
    change (prod.lift (terminal.from AU ≫ oneU) (𝟙 AU) ≫ mu).hom.app W x = x at heq
    rw [section_comp, heval] at heq
    dsimp only [RU, AU] at heq
    simp only [section_fst_lift, section_snd_lift, section_comp, section_id] at heq
    rw [hou] at heq
    exact heq

end AlgebraicGeometry
