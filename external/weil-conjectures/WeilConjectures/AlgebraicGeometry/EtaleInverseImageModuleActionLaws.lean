/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageScalarDistributivity
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageScalarAssociativity
import Mathlib.Algebra.Module.MinimalAxioms
/-! # Transporting modules through the etale inverse image

Source: Stacks Project, Tags 03D1 and 03D2
(blueprint: lem-weil-pbc-inverse-image-module-action-laws). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The scalar action as a morphism of sheaves of sets.
Source: Stacks Project, Tag 03D2, multiplication map in lemma-pullback-module.
Naturality is the semilinearity of the module restriction maps.
(blueprint: lem-weil-pbc-inverse-image-module-action-laws). -/
noncomputable def etaleModuleScalarAction (V : Scheme.{u})
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    (sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj O ⨯
      (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj G) ⟶
      (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj G) where
  hom := {
    app := fun W ↦ ↾fun x ↦
      @SMul.smul (O.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
      ((prod.fst : _ ⟶ (sheafForget (D := CommRingCat.{u + 1})
        V.smallEtaleTopology).obj O).hom.app W x : O.obj.obj W)
      ((prod.snd : _ ⟶ (sheafForget (D := AddCommGrpCat.{u + 1})
        V.smallEtaleTopology).obj ((SheafOfModules.toSheaf.{u + 1} _).obj G)).hom.app W x :
        G.val.obj W)
    naturality := by
      intro W Z i
      ext x
      dsimp
      have hf := ConcreteCategory.congr_hom
        ((prod.fst : _ ⟶ (sheafForget (D := CommRingCat.{u + 1})
          V.smallEtaleTopology).obj O).hom.naturality i) x
      have hs := ConcreteCategory.congr_hom
        ((prod.snd : _ ⟶ (sheafForget (D := AddCommGrpCat.{u + 1})
          V.smallEtaleTopology).obj ((SheafOfModules.toSheaf.{u + 1} _).obj G)).hom.naturality i) x
      dsimp at hf hs
      rw [hf, hs]
      exact (G.val.map_smul i _ _).symm }

/-- Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-module-action-laws).

Proof: the compatibility of the two hom equivalences identifies the ring and
abelian comparisons with those of the canonical algebraic lifts, by uniqueness
of left adjoints. Hence they intertwine addition, zero, negation, multiplication
and one with the operations transported by the set inverse image. Conjugate the
original scalar action by these comparisons and the inverse product comparison.
Apply the finite-product-preserving inverse image to each source module diagram:
addition in either variable, zero in either variable, multiplication of scalars,
and the unit. Cancel the invertible product comparisons and substitute the
identified ring and abelian operations. Evaluating these diagram identities on
sections gives the module axioms for the displayed action, on the existing
abelian groups. Products of set sheaves are computed sectionwise, so every pair
of sections occurs. This proves the asserted sectionwise Module structures and
their scalar-action values. Restriction maps and a sheaf of modules are not
constructed in this lemma. -/
theorem etaleInverseImageModuleActionLaws (U V : Scheme.{u}) (f : U ⟶ V)
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
    let A := La.obj (FV.obj G)
    let mu := prod.map (er.hom.app O) (ea.hom.app (FV.obj G)) ≫
      inv (prodComparison L (FrV.obj O) (FaV.obj (FV.obj G))) ≫
      L.map (etaleModuleScalarAction V O G) ≫ ea.inv.app (FV.obj G)
    ∃ m : ∀ W : U.Etaleᵒᵖ, Module (OR.obj.obj W) (A.obj.obj W),
      ∀ (W : U.Etaleᵒᵖ) (x : ((FrU.obj (Lr.obj O)) ⨯ (FaU.obj A)).obj.obj W),
        @SMul.smul (OR.obj.obj W) (A.obj.obj W) (m W).toSMul
          ((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶
            FrU.obj (Lr.obj O)).hom.app W x : OR.obj.obj W)
          ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶
            FaU.obj A).hom.app W x : A.obj.obj W) = mu.hom.app W x := by
  dsimp only
  intro Lr ar er ea h G
  have hadd := etaleInverseImageScalarDistributivity U V f O Lr ar er ea h G
    (etaleModuleScalarAction V O G) (by intro W x; rfl)
  have hmul := etaleInverseImageScalarAssociativity U V f O Lr ar er ea h G
    (etaleModuleScalarAction V O G) (by intro W x; rfl)
  let A := (Etale.upperStar AddCommGrpCat.{u + 1} f).obj
    ((SheafOfModules.toSheaf.{u + 1} _).obj G)
  let mu := prod.map (er.hom.app O)
      (ea.hom.app ((SheafOfModules.toSheaf.{u + 1} _).obj G)) ≫
    inv (prodComparison (Scheme.etaleSetPullback f)
      ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj O)
      ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj G))) ≫
    (Scheme.etaleSetPullback f).map (etaleModuleScalarAction V O G) ≫
      ea.inv.app ((SheafOfModules.toSheaf.{u + 1} _).obj G)
  let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
  let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
  let e : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ≅
      MonoidalCategory.tensorObj (FrU.obj (Lr.obj O)) (FaU.obj A) :=
    (limit.isLimit _).conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
  let m : ∀ W : U.Etaleᵒᵖ, Module ((Lr.obj O).obj.obj W) (A.obj.obj W) := fun W ↦ by
    let : SMul ((Lr.obj O).obj.obj W) (A.obj.obj W) :=
      ⟨fun r x ↦ (e.inv ≫ mu).hom.app W (r, x)⟩
    exact Module.ofMinimalAxioms (hadd W).1 (hadd W).2 (hmul W).1 (hmul W).2
  refine ⟨m, ?_⟩
  intro W x
  change (e.inv ≫ mu).hom.app W
      (((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶
        FrU.obj (Lr.obj O)).hom.app W x),
       ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶
        FaU.obj A).hom.app W x)) = mu.hom.app W x
  have hf : e.hom ≫ CartesianMonoidalCategory.fst _ _ =
      (prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶ FrU.obj (Lr.obj O)) := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit (pair (FrU.obj (Lr.obj O)) (FaU.obj A)))
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _) ⟨WalkingPair.left⟩
  have hs : e.hom ≫ CartesianMonoidalCategory.snd _ _ =
      (prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶ FaU.obj A) := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit (pair (FrU.obj (Lr.obj O)) (FaU.obj A)))
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _) ⟨WalkingPair.right⟩
  have hp : (e.hom.hom.app W x) =
      (((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶
        FrU.obj (Lr.obj O)).hom.app W x),
       ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ⟶
        FaU.obj A).hom.app W x)) := by
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (C := Type (u + 1))
        (congrArg (fun k ↦ k.hom.app W) hf) x
    · exact ConcreteCategory.congr_hom (C := Type (u + 1))
        (congrArg (fun k ↦ k.hom.app W) hs) x
  rw [← hp]
  exact ConcreteCategory.congr_hom (C := Type (u + 1))
    (congrArg (fun k ↦ k.hom.app W) (e.hom_inv_id_assoc mu)) x

end AlgebraicGeometry
