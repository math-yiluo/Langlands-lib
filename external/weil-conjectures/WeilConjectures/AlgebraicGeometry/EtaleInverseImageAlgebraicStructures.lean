/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLift
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageRingLift
/-!
# Inverse image on small étale sites and algebraic structures
Source: Stacks Project, Sites and Sheaves, Tags 00X6, 00X1, and 00YV
(blueprint: situation-conventions).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
private theorem unit_of_homEquiv
    {C : Type*} [Category C] {D : Type*} [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {X : C} {Y : D}
    (e : Y ≅ L.obj X) (η : X ⟶ R.obj Y)
    (h : η = a.homEquiv X Y e.inv) : η ≫ R.map e.hom = a.unit.app X := by
  rw [h, Adjunction.homEquiv_unit, Category.assoc, ← R.map_comp,
    e.inv_hom_id, R.map_id]
  exact Category.comp_id _

/-- Source: Stacks Project, Tags 00X6, 00X1, and 00YV
(blueprint: situation-conventions).
The set inverse image is the recorded `Scheme.etaleSetPullback` (def-weil-pbc-etale-sheaves):
left Kan extension along the opposite of base change, followed by sheafification.
The direct images are precomposition with base change. The lifted adjunctions
commute with forgetting, including their hom-set bijections and units. This
identifies the transported algebraic structures and the abelian inverse image.
Proof:
1. Base change is continuous and preserves finite limits, by
   situation-conventions and
   situation-conventions; direct image is precomposition.
2. Presheaf pullback and sheafification are left adjoints, by
   situation-conventions and def-weil-pbc-sheafification.
   Their composite with the fully faithful inclusion gives the set adjunction.
3. Presheaf pullback, inclusion, and sheafification preserve finite limits, by
   situation-conventions and
   situation-conventions. Hence so does set inverse image.
4. By situation-conventions and
   situation-conventions, transport the operations using
   the product and terminal comparisons. The adjunction restricts on hom sets,
   and its unit is the original set unit. Right images have sectionwise operations.
5. Uniqueness of left adjoints (situation-conventions) identifies
   the abelian lift with def-weil-pbc-inverse-image, compatibly with the units. -/
theorem etaleInverseImageAlgebraicStructures (U V : Scheme.{u}) (f : U ⟶ V) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let R := b.sheafPushforwardContinuous (Type (u + 1))
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let Ra := Etale.lowerStar AddCommGrpCat.{u + 1} f
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    PreservesFiniteLimits L ∧
      ∃ (ea : La ⋙ FaU ≅ FaV ⋙ L) (da : Ra ⋙ FaV ≅ FaU ⋙ R)
        (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
        (ar : Lr ⊣ Rr)
        (er : Lr ⋙ FrU ≅ FrV ⋙ L) (dr : Rr ⋙ FrV ≅ FrU ⋙ R),
        (∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
            (W : V.Etaleᵒᵖ) (x : (Ra.obj F).obj.obj W),
          (da.hom.app F).hom.app W x = x) ∧
        (∀ (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
            (W : V.Etaleᵒᵖ) (x : (Rr.obj F).obj.obj W),
          (dr.hom.app F).hom.app W x = x) ∧
        (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
          FaV.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
            G F h) ≫ da.hom.app F =
              a.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) ∧
        (∀ G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1},
          FaV.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            G) ≫ da.hom.app (La.obj G) ≫ R.map (ea.hom.app G) =
              a.unit.app (FaV.obj G)) ∧
        (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
          FrV.map (ar.homEquiv G F h) ≫ dr.hom.app F =
            a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
        (∀ G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1},
          FrV.map (ar.unit.app G) ≫ dr.hom.app (Lr.obj G) ≫ R.map (er.hom.app G) =
            a.unit.app (FrV.obj G)) ∧
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
            L.map negV = ea.inv.app G ≫ negU ≫ ea.hom.app G) ∧
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
  have hL : PreservesFiniteLimits (Scheme.etaleSetPullback f) := by
    unfold Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  refine ⟨hL, ?_⟩
  obtain ⟨ea, ha, opa⟩ := etaleInverseImageAbelianLift U V f hL
  obtain ⟨Lr, ar, er, hr, opr⟩ := etaleInverseImageRingLift U V f hL
  refine ⟨ea, Iso.refl _, Lr, ar, er, Iso.refl _, ?_, ?_, ?_, ?_, ?_, ?_, opa, opr⟩
  · intro F W x
    rfl
  · intro F W x
    rfl
  · simpa using ha
  · intro G
    have h := unit_of_homEquiv a (ea.app G)
      ((sheafForget V.smallEtaleTopology).map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G))
      (by
        have hh := ha G _ (𝟙 _)
        rw [(Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv_id] at hh
        simpa using hh)
    simpa using h
  · simpa using hr
  · intro G
    have h := unit_of_homEquiv a (er.app G)
      ((sheafForget V.smallEtaleTopology).map (ar.unit.app G))
      (by
        have hh := hr G _ (𝟙 _)
        rw [ar.homEquiv_id] at hh
        simpa using hh)
    simpa using h
end AlgebraicGeometry
