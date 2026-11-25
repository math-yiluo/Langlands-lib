/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftOperations
import WeilConjectures.AlgebraicGeometry.ProductComparisonDistributivity

/-! # Distributivity of the transported scalar action

Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-distributivity-left). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem fst_lift_app {T : Scheme.{u}}
    {B C D : Sheaf T.smallEtaleTopology (Type (u + 1))}
    (g : D ⟶ B) (h : D ⟶ C) (W : T.Etaleᵒᵖ) (z : D.obj.obj W) :
    (prod.fst : B ⨯ C ⟶ B).hom.app W ((prod.lift g h).hom.app W z) =
      g.hom.app W z := by
  exact congrArg (fun k ↦ k.hom.app W z) (prod.lift_fst g h)

private theorem snd_lift_app {T : Scheme.{u}}
    {B C D : Sheaf T.smallEtaleTopology (Type (u + 1))}
    (g : D ⟶ B) (h : D ⟶ C) (W : T.Etaleᵒᵖ) (z : D.obj.obj W) :
    (prod.snd : B ⨯ C ⟶ C).hom.app W ((prod.lift g h).hom.app W z) =
      h.hom.app W z := by
  exact congrArg (fun k ↦ k.hom.app W z) (prod.lift_snd g h)

private noncomputable def sectionProduct {T : Scheme.{u}}
    (B C : Sheaf T.smallEtaleTopology (Type (u + 1))) : B ⨯ C ≅ B ⊗ C :=
  (limit.isLimit _).conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)

private theorem sectionProduct_inv_fst {T : Scheme.{u}}
    (B C : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (W : T.Etaleᵒᵖ) (b : B.obj.obj W) (c : C.obj.obj W) :
    (prod.fst : B ⨯ C ⟶ B).hom.app W ((sectionProduct B C).inv.hom.app W (b, c)) = b := by
  exact congrArg (fun k ↦ k.hom.app W (b, c))
    (IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _)
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct B C) ⟨WalkingPair.left⟩)

private theorem sectionProduct_inv_snd {T : Scheme.{u}}
    (B C : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (W : T.Etaleᵒᵖ) (b : B.obj.obj W) (c : C.obj.obj W) :
    (prod.snd : B ⨯ C ⟶ C).hom.app W ((sectionProduct B C).inv.hom.app W (b, c)) = c := by
  exact congrArg (fun k ↦ k.hom.app W (b, c))
    (IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _)
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct B C) ⟨WalkingPair.right⟩)

private theorem product_section_ext {T : Scheme.{u}}
    (B C : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (W : T.Etaleᵒᵖ) (z z' : (B ⨯ C).obj.obj W)
    (hf : (prod.fst : B ⨯ C ⟶ B).hom.app W z = (prod.fst : B ⨯ C ⟶ B).hom.app W z')
    (hs : (prod.snd : B ⨯ C ⟶ C).hom.app W z = (prod.snd : B ⨯ C ⟶ C).hom.app W z') : z = z' := by
  let e := sectionProduct B C
  have hf' := IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct B C) ⟨WalkingPair.left⟩
  have hs' := IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct B C) ⟨WalkingPair.right⟩
  have he : e.hom.hom.app W z = e.hom.hom.app W z' := by
    apply Prod.ext
    · exact (congrArg (fun k ↦ k.hom.app W z) hf').trans
        (hf.trans (congrArg (fun k ↦ k.hom.app W z') hf').symm)
    · exact (congrArg (fun k ↦ k.hom.app W z) hs').trans
        (hs.trans (congrArg (fun k ↦ k.hom.app W z') hs').symm)
  have h := congrArg (fun t ↦ e.inv.hom.app W t) he
  simp only [← types_comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id] at h
  exact h

/-- Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-distributivity-left).

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
theorem etaleInverseImageScalarDistributivity_left (U V : Scheme.{u}) (f : U ⟶ V)
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
      (∀ (r : OR.obj.obj W) (x y : A.obj.obj W),
        act W r (x + y) = act W r x + act W r y )
    := by
  -- Select products directly in the set-sheaf categories, avoiding searches through module lifts.
  have (B C : Sheaf V.smallEtaleTopology (Type (u + 1))) : HasBinaryProduct B C :=
    let _ : HasBinaryProducts (Sheaf V.smallEtaleTopology (Type (u + 1))) :=
      Sheaf.instHasLimitsOfShape
    HasLimitsOfShape.has_limit _
  have (B C : Sheaf U.smallEtaleTopology (Type (u + 1))) : HasBinaryProduct B C :=
    let _ : HasBinaryProducts (Sheaf U.smallEtaleTopology (Type (u + 1))) :=
      Sheaf.instHasLimitsOfShape
    HasLimitsOfShape.has_limit _
  dsimp only
  intro Lr ar er ea hcompat G muV hmu
  let L := Scheme.etaleSetPullback f
  let La := Etale.upperStar AddCommGrpCat.{u + 1} f
  let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
  let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
  let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
  let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
  let OV := (sheafCompose V.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let FV := SheafOfModules.toSheaf.{u + 1} OV
  let X := FaV.obj (FV.obj G)
  let R := FrV.obj O
  let A := La.obj (FV.obj G)
  let X' := FaU.obj A
  let R' := FrU.obj (Lr.obj O)
  obtain ⟨addV, addU, zeroV, zeroU, negV, negU, hv, hu, ht, _⟩ :=
    etaleInverseImageAbelianLift_operations U V f inferInstance ea hcompat.2 (FV.obj G)
  have hd : prod.map (𝟙 R) addV ≫ muV =
      prod.lift
        (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ muV)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ muV) ≫ addV := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro z
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
    rw [hmu, hv, fst_lift_app, snd_lift_app]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
    rw [hmu, hmu, fst_lift_app, snd_lift_app, fst_lift_app, snd_lift_app]
    have hf := congrArg (fun k ↦ k.hom.app W z)
      (prod.map_fst (𝟙 R) addV)
    have hs := congrArg (fun k ↦ k.hom.app W z)
      (prod.map_snd (𝟙 R) addV)
    dsimp at hf hs
    erw [hf, hs, hv]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
    exact @smul_add (OV.obj.obj W) (G.val.obj W) _ (G.val.obj W).isModule.toDistribSMul _ _ _
  let mu := prod.map (er.hom.app O) (ea.hom.app (FV.obj G)) ≫
    inv (prodComparison L R X) ≫ L.map muV ≫ ea.inv.app (FV.obj G)
  have htransport : prod.map (𝟙 R') addU ≫ mu =
      prod.lift
        (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ mu)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ mu) ≫ addU :=
    productComparison_distributivity L (er.app O) (ea.app (FV.obj G)) addV addU muV ht hd
  intro W r x y
  change R'.obj.obj W at r
  let z := (sectionProduct R' (X' ⨯ X')).inv.hom.app W
    (r, (sectionProduct X' X').inv.hom.app W (x, y))
  have hf : (prod.fst : R' ⨯ (X' ⨯ X') ⟶ R').hom.app W z = r :=
    sectionProduct_inv_fst _ _ _ _ _
  have hs : (prod.snd : R' ⨯ (X' ⨯ X') ⟶ X' ⨯ X').hom.app W z =
      (sectionProduct X' X').inv.hom.app W (x, y) :=
    sectionProduct_inv_snd _ _ _ _ _
  have hxy : addU.hom.app W ((prod.snd : R' ⨯ (X' ⨯ X') ⟶ X' ⨯ X').hom.app W z) =
      ((x : X'.obj.obj W) + (y : X'.obj.obj W)) := by
    erw [hs, hu, sectionProduct_inv_fst, sectionProduct_inv_snd]
    rfl
  have ha : (prod.map (𝟙 R') addU).hom.app W z =
      (sectionProduct R' X').inv.hom.app W (r, x + y) := by
    apply product_section_ext R' X' W
    · have h := congrArg (fun k ↦ k.hom.app W z) (prod.map_fst (𝟙 R') addU)
      dsimp at h
      simpa only [sectionProduct_inv_fst] using h.trans hf
    · have h := congrArg (fun k ↦ k.hom.app W z) (prod.map_snd (𝟙 R') addU)
      dsimp at h
      rw [sectionProduct_inv_snd]
      convert h.trans hxy using 1
  have hx : (prod.lift prod.fst (prod.snd ≫ prod.fst) : R' ⨯ (X' ⨯ X') ⟶ R' ⨯ X').hom.app
      W z = (sectionProduct R' X').inv.hom.app W (r, x) := by
    apply product_section_ext R' X' W
    · rw [fst_lift_app, hf, sectionProduct_inv_fst]
    · rw [snd_lift_app]
      change (prod.fst : X' ⨯ X' ⟶ X').hom.app W
        ((prod.snd : R' ⨯ (X' ⨯ X') ⟶ X' ⨯ X').hom.app W z) = _
      rw [hs, sectionProduct_inv_fst, sectionProduct_inv_snd]
  have hy : (prod.lift prod.fst (prod.snd ≫ prod.snd) : R' ⨯ (X' ⨯ X') ⟶ R' ⨯ X').hom.app
      W z = (sectionProduct R' X').inv.hom.app W (r, y) := by
    apply product_section_ext R' X' W
    · rw [fst_lift_app, hf, sectionProduct_inv_fst]
    · rw [snd_lift_app]
      change (prod.snd : X' ⨯ X' ⟶ X').hom.app W
        ((prod.snd : R' ⨯ (X' ⨯ X') ⟶ X' ⨯ X').hom.app W z) = _
      rw [hs, sectionProduct_inv_snd, sectionProduct_inv_snd]
  have hxm := congrArg (fun t ↦ mu.hom.app W t) hx
  have hym := congrArg (fun t ↦ mu.hom.app W t) hy
  have h := congrArg (fun k ↦ k.hom.app W z) htransport
  change mu.hom.app W ((prod.map (𝟙 R') addU).hom.app W z) =
    addU.hom.app W ((prod.lift
      (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ mu)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ mu)).hom.app W z) at h
  erw [ha, hu, fst_lift_app, snd_lift_app] at h
  have hxm' :
      (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ mu).hom.app W z =
        mu.hom.app W ((sectionProduct R' X').inv.hom.app W (r, x)) := by
    convert hxm using 1 ; rfl
  have hym' :
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ mu).hom.app W z =
        mu.hom.app W ((sectionProduct R' X').inv.hom.app W (r, y)) := by
    convert hym using 1 ; rfl
  exact h.trans (by
    apply congrArg₂
    · exact hxm'
    · exact hym')

end AlgebraicGeometry
