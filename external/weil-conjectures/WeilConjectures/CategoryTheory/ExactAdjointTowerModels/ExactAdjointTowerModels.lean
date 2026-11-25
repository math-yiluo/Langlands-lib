/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Simultaneous exact-adjoint tower models

Source: Stacks Project, Cohomology on Sites, Tag 0A07, first proof; Tags 0941,
079P, 08BJ, 0BK6, 070K and 070Y
(blueprint: lem-weil-pbc-exact-adjoint-tower-models).

The structures package the choices and assertions of the statement. In particular,
they do not choose any replacement or any derived functor from a bare existence axiom.
The positive tower level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u vA vB uA uB w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Functor Opposite

namespace CategoryTheory.ExactAdjointTowerModels

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Applying a functor levelwise to a strict tower complex.
Source: Stacks Tag 0A07, tower-topos square
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
abbrev tower (G : A ⥤ B) [G.Additive] :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- A total right derived functor with its universal unit, computed on K-injectives.
This only bundles the conclusion of the recorded K-injective total-derivation lemma.
Source: Stacks Tags 070K and 070Y
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure DerivedModel (H : CochainComplex A ℤ ⥤ CochainComplex B ℤ) where
  functor : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B
  unit : H ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  on_injectives : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)

variable [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- The negative-difference fibre coordinates, ordered as (y,x).
Source: Stacks Tag 0941 and the explicit sign calculation in the node
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
def negativeCoordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (ExactProductsRoos.fibre.obj X).X (p + 1) ≅
      (roosP X).X p ⊞ (roosP X).X (p + 1) :=
  (CochainComplex.mappingCone (-roosU X)).shiftFunctorObjXIso
      (-1) (p + 1) p (add_neg_cancel_right p 1).symm ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod (-roosU X) p (p + 1) rfl ≪≫
      biprod.braiding _ _

/-- The signed, unit-normalized Roos conclusions for one of the two categories.
The sign isomorphism and both comparisons are natural on all strict tower complexes.
The final fields transport the rotated cone triangle along the actual map j.
Source: Stacks Tag 0941, including the sign convention of the strict Roos model
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure NormalizedRoos (L : DerivedModel (roosLimitFunctor (A := A))) where
  sign : ExactProductsRoos.fibre (B := A) ≅ roosF
  sign_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (sign.hom.app X).f (p + 1) ≫ (roosχ X p).hom =
      (negativeCoordinates X p).hom ≫ biprod.map (-𝟙 _) (𝟙 _)
  negative : ExactProductsRoos.fibre ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.functor
  ordinary : ExactProductsRoos.ordinary (B := A) ≅ roosLimitFunctor
  ordinary_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) (p : ℤ),
    ((ordinary.hom.app X) ≫ limit.π X.asFunctor (op n)).f p =
      limit.π (X.X p) (op n)
  inclusion_sign : ExactProductsRoos.comparison ≫ sign.hom =
    ordinary.hom ≫ roosInclusion
  negative_normalization :
    Functor.whiskerRight ExactProductsRoos.comparison DerivedCategory.Q ≫ negative.hom =
      Functor.whiskerRight ordinary.hom DerivedCategory.Q ≫ L.unit
  comparison : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ L.functor
  comparison_sign : comparison =
    isoWhiskerRight sign.symm DerivedCategory.Q ≪≫ negative
  normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    DerivedCategory.Q.map (roosι X) ≫ comparison.hom.app X = L.unit.app X
  quasiIso : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) → QuasiIso (roosι I)
  triangle : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) →
    ∃ e : DerivedCategory.Q.obj (limit I.asFunctor) ≅
        DerivedCategory.Q.obj (roosF.obj I),
      e.hom = DerivedCategory.Q.map (roosι I) ∧
      Triangle.mk
        (DerivedCategory.Q.map (roosι I ≫ roosProj I))
        (DerivedCategory.Q.map (roosU I))
        (DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU I)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ≫
          e.inv⟦(1 : ℤ)⟧') ∈ distTriang (DerivedCategory.{w} A)
  unit_triangle : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
    (∀ r : ℤ, Injective (I.X r)) →
    Triangle.mk
      ((comparison.inv.app I) ≫ DerivedCategory.Q.map (roosProj I))
      (DerivedCategory.Q.map (roosU I))
      (DerivedCategory.Q.map (CochainComplex.mappingCocone.triangle (roosU I)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ≫
        (comparison.hom.app I)⟦(1 : ℤ)⟧') ∈ distTriang (DerivedCategory.{w} A)

variable [HasLimitsOfShape ℕᵒᵖ B] [HasCountableProducts B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

/-- All simultaneous models and their canonical normalizations. The derived models
are choices with universal units; c and beta are fixed by their projection equations.
No exact-product assumption is used except in the last field.
Source: Stacks Tag 0A07, first proof, and Tags 0BK6 and 0941
(blueprint: lem-weil-pbc-exact-adjoint-tower-models). -/
structure Models (G : A ⥤ B) [G.Additive] where
  direct : DerivedModel (G.mapHomologicalComplex (.up ℤ))
  towerDirect : DerivedModel (tower G)
  sourceLimit : DerivedModel (roosLimitFunctor (A := A))
  targetLimit : DerivedModel (roosLimitFunctor (A := B))
  resolution : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I),
      QuasiIso q ∧ I.IsKInjective ∧ ∀ r : ℤ, Injective (I.X r)
  kInjective : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      ((tower G).obj I).IsKInjective ∧
      (∀ r : ℤ, Injective (((tower G).obj I).X r)) ∧
      (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n)) ∧
        CochainComplex.IsKInjective
          ((G.mapHomologicalComplex (.up ℤ)).obj (I.asFunctor.obj (op n)))) ∧
      CochainComplex.IsKInjective (limit I.asFunctor) ∧
      CochainComplex.IsKInjective (limit ((tower G).obj I).asFunctor) ∧
      (roosP I).IsKInjective ∧ (roosP ((tower G).obj I)).IsKInjective ∧
      CochainComplex.IsKInjective
        ((G.mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor)) ∧
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj (roosP I))
  computes : ∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I),
    QuasiIso q → I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      (∃ e : DerivedCategory.Q.obj ((tower G).obj I) ≅
          towerDirect.functor.obj (DerivedCategory.Q.obj X),
        e.hom ≫ towerDirect.functor.map (DerivedCategory.Q.map q) =
          towerDirect.unit.app I) ∧
      (∃ e : DerivedCategory.Q.obj (limit I.asFunctor) ≅
          sourceLimit.functor.obj (DerivedCategory.Q.obj X),
        e.hom ≫ sourceLimit.functor.map (DerivedCategory.Q.map q) =
          sourceLimit.unit.app I) ∧
      (∃ e : DerivedCategory.Q.obj (limit ((tower G).obj I).asFunctor) ≅
          targetLimit.functor.obj (towerDirect.functor.obj (DerivedCategory.Q.obj X)),
        e.hom ≫ targetLimit.functor.map (towerDirect.functor.map (DerivedCategory.Q.map q)) =
          targetLimit.unit.app ((tower G).obj I) ≫
            targetLimit.functor.map (towerDirect.unit.app I)) ∧
      (∃ e : DerivedCategory.Q.obj
            ((G.mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor)) ≅
          direct.functor.obj (sourceLimit.functor.obj (DerivedCategory.Q.obj X)),
        e.hom ≫ direct.functor.map (sourceLimit.functor.map (DerivedCategory.Q.map q)) =
          direct.unit.app (limit I.asFunctor) ≫
            direct.functor.map (sourceLimit.unit.app I))
  products : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) →
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (limit.cone (Discrete.functor
          (fun n : ℕ ↦ ((tower G).obj I).asFunctor.obj (op n))))))
  c : ExactProductsRoos.product ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    tower G ⋙ ExactProductsRoos.product
  beta : roosLimitFunctor ⋙ G.mapHomologicalComplex (.up ℤ) ≅
    tower G ⋙ roosLimitFunctor
  c_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    c.hom.app X ≫ Pi.π (fun k : ℕ ↦ ((tower G).obj X).asFunctor.obj (op k)) n =
      (G.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n)
  beta_components : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    beta.hom.app X ≫ limit.π ((tower G).obj X).asFunctor (op n) =
      (G.mapHomologicalComplex (.up ℤ)).map (limit.π X.asFunctor (op n))
  shift_commutes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (G.mapHomologicalComplex (.up ℤ)).map
        (towerProductShift (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫
        c.hom.app X =
      c.hom.app X ≫ towerProductShift
        (fun n : ℕ ↦ ((tower G).obj X).asFunctor.map (homOfLE (Nat.le_succ n)).op)
  difference_commutes : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (G.mapHomologicalComplex (.up ℤ)).map (roosU X) ≫ c.hom.app X =
      c.hom.app X ≫ roosU ((tower G).obj X)
  derived_product_components : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    I.IsKInjective → (∀ r : ℤ, Injective (I.X r)) → ∀ n : ℕ,
      DerivedCategory.Q.map (c.hom.app I) ≫
          DerivedCategory.Q.map
            (Pi.π (fun k : ℕ ↦ ((tower G).obj I).asFunctor.obj (op k)) n) ≫
          direct.unit.app (I.asFunctor.obj (op n)) =
        direct.unit.app (roosP I) ≫ direct.functor.map
          (DerivedCategory.Q.map (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n))
  localized_maps : ∀ (I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
    I.IsKInjective → I'.IsKInjective →
    (∀ a : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I',
      ∃ f : I ⟶ I', DerivedCategory.Q.map f = a) ∧
    (∀ (f g : I ⟶ I'), DerivedCategory.Q.map f = DerivedCategory.Q.map g →
      DerivedCategory.Q.map (roosPmap f) = DerivedCategory.Q.map (roosPmap g) ∧
      DerivedCategory.Q.map (roosLimitFunctor.map f) =
        DerivedCategory.Q.map (roosLimitFunctor.map g) ∧
      DerivedCategory.Q.map ((ExactProductsRoos.product ⋙
        G.mapHomologicalComplex (.up ℤ)).map f) =
        DerivedCategory.Q.map ((ExactProductsRoos.product ⋙
          G.mapHomologicalComplex (.up ℤ)).map g) ∧
      DerivedCategory.Q.map ((tower G ⋙ ExactProductsRoos.product).map f) =
        DerivedCategory.Q.map ((tower G ⋙ ExactProductsRoos.product).map g) ∧
      DerivedCategory.Q.map ((roosLimitFunctor ⋙
        G.mapHomologicalComplex (.up ℤ)).map f) =
        DerivedCategory.Q.map ((roosLimitFunctor ⋙
          G.mapHomologicalComplex (.up ℤ)).map g) ∧
      DerivedCategory.Q.map ((tower G ⋙ roosLimitFunctor).map f) =
        DerivedCategory.Q.map ((tower G ⋙ roosLimitFunctor).map g))
  exact_products : HasExactLimitsOfShape (Discrete ℕ) A →
    HasExactLimitsOfShape (Discrete ℕ) B →
      Nonempty (NormalizedRoos sourceLimit) ∧ Nonempty (NormalizedRoos targetLimit)

private def ordinaryIso :
    ExactProductsRoos.ordinary (B := A) ≅ roosLimitFunctor :=
  (NatIso.ofComponents (fun X ↦
    limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩) (by
    intro X Y f
    apply (HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor).hom_ext
    intro n
    ext p
    have hπ (Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩).hom.f p ≫
            limit.π (Z.X p) n = (limit.π Z.asFunctor n).f p := by
      simpa only [HomologicalComplex.comp_f,
        HomologicalComplex.coneOfHasLimitEval_π_app_f, HomologicalComplex.asFunctor,
        HomologicalComplex.eval, Functor.comp] using
        congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
          (limit.isoLimitCone_hom_π
            ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
    have hm := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n)
    dsimp at hπ hm ⊢
    simp only [HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp] at hπ hm ⊢
    calc
      _ = (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).f p ≫
          (limit.π Y.asFunctor n).f p := by
        rw [Category.assoc, hπ Y]
        rfl
      _ = (limit.π X.asFunctor n).f p ≫ (f.f p).app n := hm
      _ = _ := by
        rw [Category.assoc]
        change _ = _ ≫ limMap (f.f p) ≫ limit.π (Y.X p) n
        rw [limMap_π, ← Category.assoc, hπ X]
        rfl)).symm

omit [HasDerivedCategory A] [HasCountableProducts A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem ordinaryIso_components (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (n : ℕᵒᵖ) (p : ℤ) :
    (ordinaryIso.hom.app X ≫ limit.π X.asFunctor n).f p =
      limit.π (X.X p) n := by
  have h := congrArg (fun f ↦ f.f p)
    (limit.isoLimitCone_inv_π
      ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
        HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩ n)
  exact h

private def productIso (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) (G.mapHomologicalComplex (.up ℤ))] :
    ExactProductsRoos.product ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      tower G ⋙ ExactProductsRoos.product :=
  NatIso.ofComponents (fun X ↦
    asIso (piComparison (G.mapHomologicalComplex (.up ℤ))
      (fun n : ℕ ↦ X.asFunctor.obj (op n)))) (by
    intro X Y f
    let H := G.mapHomologicalComplex (.up ℤ)
    change H.map (Limits.Pi.map
        (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
          (op n))) ≫ piComparison H (fun n : ℕ ↦ Y.asFunctor.obj (op n)) =
      piComparison H (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫
        Limits.Pi.map (f := fun n : ℕ ↦ H.obj (X.asFunctor.obj (op n)))
          (g := fun n : ℕ ↦ H.obj (Y.asFunctor.obj (op n)))
          (fun n : ℕ ↦ H.map
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)))
    apply Pi.hom_ext
    intro n
    dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
      piComparison_comp_π_assoc, ← H.map_comp])

private def limitIso (G : A ⥤ B) [G.Additive]
    [PreservesLimitsOfShape ℕᵒᵖ (G.mapHomologicalComplex (.up ℤ))] :
    roosLimitFunctor ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      tower G ⋙ roosLimitFunctor :=
  NatIso.ofComponents (fun X ↦
    preservesLimitIso (G.mapHomologicalComplex (.up ℤ)) X.asFunctor) (by
    intro X Y f
    exact (preservesLimitNatIso (G.mapHomologicalComplex (.up ℤ))).hom.naturality
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f))

private def signCone (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex.mappingCone (-roosU X) ≅ CochainComplex.mappingCone (roosU X) where
  hom := CochainComplex.mappingCone.map _ _ (𝟙 _) (-𝟙 _) (by simp)
  inv := CochainComplex.mappingCone.map _ _ (𝟙 _) (-𝟙 _) (by simp)
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    exact CochainComplex.mappingCone.map_id _
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
    exact CochainComplex.mappingCone.map_id _

omit [HasDerivedCategory A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem sign_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (((shiftFunctor _ (-1 : ℤ)).mapIso (signCone X)).hom).f (p + 1) ≫
        (roosχ X p).hom =
      (negativeCoordinates X p).hom ≫ biprod.map (-𝟙 _) (𝟙 _) := by
  dsimp only [Functor.mapIso_hom, roosχ, negativeCoordinates, Iso.trans_hom, signCone]
  rw [CochainComplex.shiftFunctor_map_f']
  simp only [Category.assoc, CochainComplex.shiftFunctorObjXIso]
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality]
  simp only [Category.assoc]
  congr 1
  apply CochainComplex.mappingCone.ext_from (-roosU X) (p + 1) p rfl
  · change (CochainComplex.mappingCone.inl (-roosU X)).v (p + 1) p (by omega) ≫
        (CochainComplex.mappingCone.map (-roosU X) (roosU X)
          (𝟙 _) (-𝟙 _) (by simp)).f p ≫ _ = _
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
    simp only [CochainComplex.mappingCone.inl,
      CochainComplex.HomComplex.Cochain.mk_v, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    apply biprod.hom_ext <;> simp
  · rw [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc]
    simp only [HomologicalComplex.comp_f, CochainComplex.mappingCone.inr, Category.assoc]
    apply biprod.hom_ext <;> simp

omit [HasDerivedCategory A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasCountableProducts A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem arrowMap_eq_coneMap {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (α : Arrow.mk f ⟶ Arrow.mk g) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α =
      CochainComplex.mappingCone.map f g α.left α.right α.w.symm := by
  ext n : 1
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n + 1) n rfl
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inlX_desc_f,
      Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero]
    change _ = (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _
        (n + 1) (n + 1) n (by omega) (by omega)]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ (n + 1) n rfl]
    simp only [CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v]
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrX_desc_f]
    change _ = (CochainComplex.mappingCone.inr f).f n ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl

private def signIso : ExactProductsRoos.fibre (B := A) ≅ roosF :=
  NatIso.ofComponents (fun X ↦ (shiftFunctor _ (-1 : ℤ)).mapIso (signCone X)) (by
    intro X Y f
    change (shiftFunctor _ (-1 : ℤ)).map _ ≫
        (shiftFunctor _ (-1 : ℤ)).map (signCone Y).hom =
      (shiftFunctor _ (-1 : ℤ)).map (signCone X).hom ≫
        (shiftFunctor _ (-1 : ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [arrowMap_eq_coneMap]
    dsimp only [signCone, ExactProductsRoos.arrowMap, roosConeFunctor]
    rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
    simp only [Category.comp_id, Category.id_comp,
      Preadditive.comp_neg, Preadditive.neg_comp])

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem inclusion_sign : ExactProductsRoos.comparison ≫ signIso.hom =
    ordinaryIso.hom ≫ roosInclusion (A := A) := by
  apply NatTrans.ext
  funext X
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change ((ExactProductsRoos.comparison ≫ signIso.hom).app X).f (p + 1) =
    ((ordinaryIso.hom ≫ roosInclusion).app X).f (p + 1)
  apply (cancel_mono (roosχ X p).hom).1
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    Category.assoc, roosInclusion, signIso, NatIso.ofComponents_hom_app, sign_coordinates]
  change (ExactProductsRoos.comparisonApp X).f (p + 1) ≫
      (negativeCoordinates X p).hom ≫ biprod.map (-𝟙 _) (𝟙 _) = _
  have hc : (ExactProductsRoos.comparisonApp X).f (p + 1) ≫
      (negativeCoordinates X p).hom =
      biprod.lift 0 ((ExactProductsRoos.inclusion.app X).f (p + 1)) := by
    apply biprod.hom_ext
    · have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
          HomologicalComplex.homotopyCofiber.sndX (-roosU X) r =
            (HomologicalComplex.homotopyCofiber.XIsoBiprod (-roosU X) r q hq).hom ≫
              biprod.snd := by
        obtain rfl := (ComplexShape.up ℤ).next_eq' hq
        dsimp only [HomologicalComplex.homotopyCofiber.sndX]
        rw [dite_eq_left hq]
      have h := CochainComplex.mappingCocone.lift_f_snd_v (-roosU X)
        (ExactProductsRoos.inclusion.app X) 0
        (ExactProductsRoos.comparison_condition X) (p + 1) p (by omega)
      simpa [ExactProductsRoos.comparisonApp, negativeCoordinates,
        CochainComplex.mappingCocone.snd, CochainComplex.HomComplex.Cochain.leftShift_v,
        Category.assoc, show Int.negOnePow 2 = 1 by rfl,
        CochainComplex.mappingCone.snd, hs p (p + 1) rfl] using h
    · simp only [Category.assoc, biprod.lift_snd]
      have hp : (CochainComplex.mappingCocone.fst (-roosU X)).f (p + 1) =
          (negativeCoordinates X p).hom ≫ biprod.snd := by
        simp [negativeCoordinates, CochainComplex.mappingCocone.fst,
          CochainComplex.HomComplex.Cocycle.homOf,
          CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.fst,
          HomologicalComplex.homotopyCofiber.fstX]
      rw [← hp]
      exact CochainComplex.mappingCocone.lift_f_fst_f _ _ _ _ _
  rw [← Category.assoc, hc, roosι_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.map_snd, Category.comp_id,
      biprod.lift_snd]
    change (ExactProductsRoos.inclusion.app X).f (p + 1) =
      (ordinaryIso.hom.app X).f (p + 1) ≫
        (Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)
    have hprod := isLimitFanMkObjOfIsLimit
      (HomologicalComplex.eval A (.up ℤ) (p + 1))
      (fun n : ℕ ↦ X.asFunctor.obj (op n))
      (Pi.π _) (productIsProduct _)
    apply hprod.hom_ext
    intro ⟨n⟩
    change (ExactProductsRoos.inclusion.app X).f (p + 1) ≫
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1) =
      ((ordinaryIso.hom.app X).f (p + 1) ≫
        (Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) ≫
          (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)
    rw [← HomologicalComplex.comp_f, Pi.lift_comp_π]
    rw [Category.assoc, ← HomologicalComplex.comp_f, Pi.lift_comp_π,
      ← HomologicalComplex.comp_f, ordinaryIso_components]
    rfl

end CategoryTheory.ExactAdjointTowerModels
