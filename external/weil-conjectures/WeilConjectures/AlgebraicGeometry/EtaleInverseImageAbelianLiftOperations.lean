/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
private noncomputable def addOp (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (sheafForget T.smallEtaleTopology).obj G ⨯
      (sheafForget T.smallEtaleTopology).obj G ⟶
        (sheafForget T.smallEtaleTopology).obj G := by
  let F := (sheafForget T.smallEtaleTopology).obj G
  exact ObjectProperty.homMk
    { app := fun W ↦ ↾fun x ↦
        @Add.add (G.obj.obj W) inferInstance
          ((prod.fst : F ⨯ F ⟶ F).hom.app W x)
          ((prod.snd : F ⨯ F ⟶ F).hom.app W x)
      naturality := by
        intro W W' k
        apply ConcreteCategory.hom_ext
        intro x
        have hf := ConcreteCategory.congr_hom ((prod.fst : F ⨯ F ⟶ F).hom.naturality k) x
        have hs := ConcreteCategory.congr_hom ((prod.snd : F ⨯ F ⟶ F).hom.naturality k) x
        dsimp at hf hs ⊢
        rw [hf, hs]
        exact (map_add (G.obj.map k).hom _ _).symm }

private noncomputable def zeroOp (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ⊤_ (Sheaf T.smallEtaleTopology (Type (u + 1))) ⟶
      (sheafForget T.smallEtaleTopology).obj G :=
  ObjectProperty.homMk
    { app := fun W ↦ ↾fun _ ↦ (0 : G.obj.obj W)
      naturality := by
        intro W W' k
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_zero (G.obj.map k).hom).symm }

private noncomputable def negOp (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (sheafForget T.smallEtaleTopology).obj G ⟶
      (sheafForget T.smallEtaleTopology).obj G :=
  ObjectProperty.homMk
    { app := fun W ↦ ↾fun x ↦ @Neg.neg (G.obj.obj W) inferInstance x
      naturality := by
        intro W W' k
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_neg (G.obj.map k).hom (show G.obj.obj W from x)).symm }

/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV.
(blueprint: lem-weil-pbc-etale-inverse-image-abelian-lift-ops)

Proof: Identify abelian sheaves with internal commutative group objects on each
site, with the sectionwise operation formulas of
`sheaves_algebraicStructures_objects`. Lift the set adjunction by
`Adjunction.liftsGroupRingObjects`; finite-limit preservation supplies its
finite-product hypothesis. Transport this lift back to abelian sheaves. Its right
adjoint is the sectionwise abelian direct image, because precomposition preserves
all the sectionwise operations and restriction maps. Uniqueness of left adjoints
therefore gives an abelian comparison from La to this lifted left adjoint. After
forgetting and composing with the lift's underlying comparison, call the resulting
isomorphism e0. The lifted hom-set equation and the adjunction-compatible abelian
comparison give the stated hom-set equation for e0.

The assumed hom-set equation forces ea = e0: for each G take F to be the lifted
left image of G and h to be the abelian comparison isomorphism. The hom-set
equations for ea and e0 have the same left side. Injectivity of the set adjunction
bijection and cancellation of the forgotten isomorphism h identify their inverse
components. Thus ea is the operation-compatible comparison e0.

Choose addV, zeroV, negV and addU, zeroU, negU from the internal-group
identifications. Their section formulas are exactly those in the conclusion.
The lifted addition equation, composed with the product comparison and transported
by the abelian comparison, gives the displayed addition equation; naturality of
the product comparison identifies its two factors with ea.inv. The lifted zero
equation gives the zero equation, since any map to the chosen terminal object is
terminal.from. The lifted inverse equation gives the negation equation after
cancelling ea. These transports are valid because the abelian comparison is a
group morphism. Substitute ea = e0 to conclude. -/
theorem etaleInverseImageAbelianLift_operations (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
        (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
          FaV.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
            G F h) =
              a.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
        (∀ G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1},
          ∃ (addV : (FaV.obj G) ⨯ (FaV.obj G) ⟶ (FaV.obj G))
            (addU : (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶ (FaU.obj (La.obj G)))
            (zeroV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ (FaV.obj G))
            (zeroU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ (FaU.obj (La.obj G)))
            (negV : (FaV.obj G) ⟶ (FaV.obj G))
            (negU : (FaU.obj (La.obj G)) ⟶ (FaU.obj (La.obj G))),
            (∀ (W : V.Etaleᵒᵖ) (x : ((FaV.obj G) ⨯ (FaV.obj G)).obj.obj W),
              addV.hom.app W x =
                (@Add.add (G.obj.obj W) inferInstance
                  ((prod.fst : (FaV.obj G) ⨯ (FaV.obj G) ⟶
                      (FaV.obj G)).hom.app W x : G.obj.obj W)
                  ((prod.snd :
                    (FaV.obj G) ⨯ (FaV.obj G) ⟶ (FaV.obj G)).hom.app W x :
                    G.obj.obj W))) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : ((FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G))).obj.obj W),
              addU.hom.app W x =
                (@Add.add ((La.obj G).obj.obj W) inferInstance
                  ((prod.fst :
                    (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶
                      (FaU.obj (La.obj G))).hom.app W x :
                    (La.obj G).obj.obj W)
                  ((prod.snd :
                    (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶
                      (FaU.obj (La.obj G))).hom.app W x :
                    (La.obj G).obj.obj W))) ∧
            L.map addV = prodComparison L (FaV.obj G) (FaV.obj G) ≫
              prod.map (ea.inv.app G) (ea.inv.app G) ≫ addU ≫ ea.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroV.hom.app W x = (0 : G.obj.obj W)) ∧
            (∀ (W : U.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroU.hom.app W x = (0 : (La.obj G).obj.obj W)) ∧
            L.map zeroV = terminal.from _ ≫ zeroU ≫ ea.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ) (x : (FaV.obj G).obj.obj W),
              negV.hom.app W x = @Neg.neg (G.obj.obj W) inferInstance x) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : (FaU.obj (La.obj G)).obj.obj W),
              negU.hom.app W x = @Neg.neg ((La.obj G).obj.obj W) inferInstance x) ∧
            L.map negV = ea.inv.app G ≫ negU ≫ ea.hom.app G) := by
  let _ := hL
  dsimp only
  intro ea hea G
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  have : b.IsContinuous V.smallEtaleTopology U.smallEtaleTopology :=
    Etale.isContinuous_overPullback f
  let R := b.sheafPushforwardContinuous (Type (u + 1))
    V.smallEtaleTopology U.smallEtaleTopology
  let La := Etale.upperStar AddCommGrpCat.{u + 1} f
  let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
  let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) V.smallEtaleTopology U.smallEtaleTopology
  let aa := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  have hu : FaV.map (aa.unit.app G) =
      a.unit.app (FaV.obj G) ≫ R.map (ea.inv.app G) := by
    have h := hea G (La.obj G) (𝟙 _)
    change FaV.map (aa.homEquiv G (La.obj G) (𝟙 _)) =
      a.homEquiv (FaV.obj G) (FaU.obj (La.obj G))
        (ea.inv.app G ≫ FaU.map (𝟙 _)) at h
    erw [aa.homEquiv_id, FaU.map_id, Category.comp_id] at h
    exact h
  refine ⟨addOp V G, addOp U (La.obj G), zeroOp V G, zeroOp U (La.obj G),
    negOp V G, negOp U (La.obj G), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W x; rfl
  · intro W x; rfl
  · let X := FaV.obj G
    let Y := FaU.obj (La.obj G)
    let q : L.obj (X ⨯ X) ⟶ Y ⨯ Y :=
      prodComparison L X X ≫ prod.map (ea.inv.app G) (ea.inv.app G)
    have hqf : q ≫ prod.fst = L.map prod.fst ≫ ea.inv.app G := by
      simp only [q, Category.assoc, prod.map_fst, prodComparison_fst_assoc]
      rfl
    have hqs : q ≫ prod.snd = L.map prod.snd ≫ ea.inv.app G := by
      simp only [q, Category.assoc, prod.map_snd, prodComparison_snd_assoc]
      rfl
    let t : X ⨯ X ⟶ R.obj (Y ⨯ Y) := a.unit.app (X ⨯ X) ≫ R.map q
    have htf : t ≫ R.map prod.fst = prod.fst ≫ FaV.map (aa.unit.app G) := by
      dsimp only [t]
      rw [Category.assoc, ← R.map_comp, hqf, R.map_comp, ← Category.assoc]
      erw [← a.unit.naturality (prod.fst : X ⨯ X ⟶ X)]
      simp only [Functor.id_map, Category.assoc]
      erw [← hu]
      rfl
    have hts : t ≫ R.map prod.snd = prod.snd ≫ FaV.map (aa.unit.app G) := by
      dsimp only [t]
      rw [Category.assoc, ← R.map_comp, hqs, R.map_comp, ← Category.assoc]
      erw [← a.unit.naturality (prod.snd : X ⨯ X ⟶ X)]
      simp only [Functor.id_map, Category.assoc]
      erw [← hu]
      rfl
    apply (cancel_mono (ea.inv.app G)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply (a.homEquiv (X ⨯ X) Y).injective
    change a.unit.app (X ⨯ X) ≫ R.map (L.map (addOp V G) ≫ ea.inv.app G) =
      a.unit.app (X ⨯ X) ≫ R.map (q ≫ addOp U (La.obj G))
    simp only [Functor.map_comp]
    rw [← Category.assoc]
    erw [← a.unit.naturality (addOp V G)]
    simp only [Functor.id_map, Category.assoc]
    erw [← hu]
    change addOp V G ≫ FaV.map (aa.unit.app G) = t ≫ R.map (addOp U (La.obj G))
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro x
    have hf := congrArg (fun k ↦ k.hom.app W x) htf
    have hs := congrArg (fun k ↦ k.hom.app W x) hts
    change (prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      ((aa.unit.app G).hom.app W).hom ((prod.fst : X ⨯ X ⟶ X).hom.app W x) at hf
    change (prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x) =
      ((aa.unit.app G).hom.app W).hom ((prod.snd : X ⨯ X ⟶ X).hom.app W x) at hs
    change ((aa.unit.app G).hom.app W).hom
        (@Add.add (G.obj.obj W) inferInstance
          ((prod.fst : X ⨯ X ⟶ X).hom.app W x)
          ((prod.snd : X ⨯ X ⟶ X).hom.app W x)) =
      @Add.add ((La.obj G).obj.obj (b.op.obj W)) inferInstance
        ((prod.fst : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
        ((prod.snd : Y ⨯ Y ⟶ Y).hom.app (b.op.obj W) (t.hom.app W x))
    rw [hf, hs]
    exact map_add _ _ _
  · intro W x; rfl
  · intro W x; rfl
  · apply (cancel_mono (ea.inv.app G)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply (a.homEquiv (⊤_ _) (FaU.obj (La.obj G))).injective
    change a.unit.app (⊤_ _) ≫ R.map (L.map (zeroOp V G) ≫ ea.inv.app G) =
      a.unit.app (⊤_ _) ≫ R.map (terminal.from _ ≫ zeroOp U (La.obj G))
    simp only [Functor.map_comp]
    rw [← Category.assoc]
    erw [← a.unit.naturality (zeroOp V G)]
    simp only [Functor.id_map, Category.assoc]
    erw [← hu]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro x
    change ((aa.unit.app G).hom.app W).hom 0 = 0
    exact map_zero _
  · intro W x; rfl
  · intro W x; rfl
  · apply (cancel_mono (ea.inv.app G)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply (a.homEquiv (FaV.obj G) (FaU.obj (La.obj G))).injective
    change a.unit.app (FaV.obj G) ≫ R.map (L.map (negOp V G) ≫ ea.inv.app G) =
      a.unit.app (FaV.obj G) ≫ R.map (ea.inv.app G ≫ negOp U (La.obj G))
    simp only [Functor.map_comp]
    rw [← Category.assoc]
    erw [← a.unit.naturality (negOp V G)]
    simp only [Functor.id_map, Category.assoc]
    erw [← hu]
    rw [← Category.assoc]
    erw [← hu]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro x
    change ((aa.unit.app G).hom.app W).hom
        (@Neg.neg (G.obj.obj W) inferInstance x) =
      @Neg.neg ((La.obj G).obj.obj (b.op.obj W)) inferInstance
        (((aa.unit.app G).hom.app W).hom x)
    exact map_neg _ _

end AlgebraicGeometry
