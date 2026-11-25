/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageComparisonAddition
import WeilConjectures.CategoryTheory.CartesianScalarDistributivityTransport

/-! # Distributivity of the transported scalar action

Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-distributivity-right). -/

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

private theorem pairIso_inv_fst
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (X Y : Sheaf J (Type (u + 1))) :
    ((limit.isLimit (pair X Y)).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)).inv ≫ prod.fst =
        CartesianMonoidalCategory.fst X Y := by
  exact (limit.isLimit (pair X Y)).conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.left⟩

private theorem pairIso_inv_snd
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (X Y : Sheaf J (Type (u + 1))) :
    ((limit.isLimit (pair X Y)).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)).inv ≫ prod.snd =
        CartesianMonoidalCategory.snd X Y := by
  exact (limit.isLimit (pair X Y)).conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y) ⟨WalkingPair.right⟩

/-- Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-distributivity-right).

Proof: First apply `etaleInverseImageAlgebraicStructures` to obtain canonical
ring and abelian lifts and their operation transport equations. The hom-equivalence
compatibility of the supplied comparisons identifies them with these canonical
comparisons: use uniqueness of left adjoints, and cancel the set-adjunction
hom equivalence to identify the underlying comparison components. Thus the
addition operations on `Lr.obj O` and `La.obj (FV.obj G)` are exactly the
conjugates of source addition by the supplied comparisons and product comparison.

Write the first source distributivity diagram on O times (G times G): the
composite adding the last two factors and then applying muV equals the composite
applying muV to the first and second, and to the first and third factors, and
then adding. Write the second diagram on (O times O) times G in the same way,
adding the first two factors. Both equalities hold on sections by the supplied
formula for muV and the source module's `smul_add` and `add_smul` axioms.
Apply L to both equalities. Its product comparison is invertible because L
preserves finite limits. Naturality of that comparison with respect to
projections, diagonals and addition rewrites the two transported diagrams as
the corresponding diagrams for mu. Substitute the addition transport equations
just identified, cancel comparison isomorphisms, and evaluate at (r,(x,y)) and
((r,s),x). Products of set sheaves are sectionwise products, so these are valid
sections for every W. The resulting equalities are precisely the two displayed
laws. No multiplicative or unit law is asserted here. -/
theorem etaleInverseImageScalarDistributivity_right (U V : Scheme.{u}) (f : U ⟶ V)
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
        act W (r + s) x = act W r x + act W s x)
    := by
  dsimp only
  intro Lr ar er ea hcompat G muV hmu
  obtain ⟨axV, ayV, ax, ay, haxV, hayV, hax, hay, hx, hy⟩ :=
    etaleInverseImageComparisonAddition U V f O Lr ar er ea hcompat G
  let X := (sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj O
  let Y := (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
    ((SheafOfModules.toSheaf.{u + 1}
      ((sheafCompose V.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)).obj G)
  let eV := (limit.isLimit (pair X Y)).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
  have hnu (W : V.Etaleᵒᵖ) (r : O.obj.obj W) (x : G.val.obj W) :
      (eV.inv ≫ muV).hom.app W (r, x) =
        @SMul.smul (O.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul r x := by
    change muV.hom.app W (eV.inv.hom.app W (r, x)) = _
    rw [hmu]
    have hf := congrArg (fun k : X ⊗ Y ⟶ X ↦ k.hom.app W (r, x))
      (pairIso_inv_fst V.smallEtaleTopology X Y)
    have hs := congrArg (fun k : X ⊗ Y ⟶ Y ↦ k.hom.app W (r, x))
      (pairIso_inv_snd V.smallEtaleTopology X Y)
    change (prod.fst : X ⨯ Y ⟶ X).hom.app W (eV.inv.hom.app W (r, x)) = r at hf
    change (prod.snd : X ⨯ Y ⟶ Y).hom.app W (eV.inv.hom.app W (r, x)) = x at hs
    rw [hf, hs]
  have hsource : ∀ (W : V.Etaleᵒᵖ) (r s : X.obj.obj W) (x : Y.obj.obj W),
      (eV.inv ≫ muV).hom.app W (axV.hom.app W (r, s), x) =
        ayV.hom.app W
          ((eV.inv ≫ muV).hom.app W (r, x), (eV.inv ≫ muV).hom.app W (s, x)) := by
    intro W r s x
    rw [haxV, hnu, hnu, hnu, hayV]
    exact @add_smul (O.obj.obj W) (G.val.obj W) _ _ (G.val.obj W).isModule r s x
  have ht := cartesianScalarDistributivityTransport V.smallEtaleTopology
    U.smallEtaleTopology (Scheme.etaleSetPullback f) X Y _ _
    (er.app O) (ea.app _) axV ayV ax ay muV hx hy hsource
  intro W r s x
  have htW := ht W r s x
  simp only [Functor.comp_obj] at htW
  simp only [hax W r s, hay] at htW
  exact htW

end AlgebraicGeometry
