/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle

/-! # Composition of the canonical derived constant units

Source: blueprint lemma-class-diagonal-projective-line, adjunction-unit pasting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem pasteUnits {C D E : Type*} [Category C] [Category D] [Category E]
    {Fp : C ⥤ D} {Rp : D ⥤ C} {Fe : D ⥤ E} {Re : E ⥤ D}
    {Fr : C ⥤ E} {Rr : E ⥤ C}
    (adjp : Fp ⊣ Rp) (adje : Fe ⊣ Re) (adj : Fr ⊣ Rr)
    (lc : Fr ≅ Fp ⋙ Fe) (rc : Re ⋙ Rp ≅ Rr)
    (C₀ : C) (D₀ : D) (E₀ : E)
    (up : Fp.obj C₀ ⟶ D₀) (ue : Fe.obj D₀ ⟶ E₀) (ur : Fr.obj C₀ ⟶ E₀)
    (hu : (adjp.comp adje).unit.app C₀ ≫ rc.hom.app (Fe.obj (Fp.obj C₀)) =
      adj.unit.app C₀ ≫ Rr.map (lc.hom.app C₀))
    (hc : Fe.map up ≫ ue = lc.inv.app C₀ ≫ ur) :
    (adjp.unit.app C₀ ≫ Rp.map up) ≫
        Rp.map (adje.unit.app D₀ ≫ Re.map ue) ≫ rc.hom.app E₀ =
      adj.unit.app C₀ ≫ Rr.map ur := by
  calc
    _ = (adjp.comp adje).unit.app C₀ ≫ rc.hom.app (Fe.obj (Fp.obj C₀)) ≫
        Rr.map (Fe.map up ≫ ue) := by
      simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
      rw [← rc.hom.naturality_assoc]
      simp only [Functor.comp_map]
      rw [← Rp.map_comp_assoc, ← adje.unit_naturality, Rp.map_comp]
      simp only [Category.assoc]
      rw [← rc.hom.naturality]
      rfl
    _ = _ := by
      rw [← Category.assoc, hu, hc]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Rr.map_comp_assoc, Iso.hom_inv_id_app, Rr.map_id, Category.id_comp]

section
open MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{vC} C] [HasDerivedCategory.{vD} D]
  [HasKInjectiveResolutions D]
  {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
  [HasKInjectiveResolutions E]
  {f : C ⥤ D} {g : D ⥤ C} {f' : D ⥤ E} {g' : E ⥤ D}
  {h : C ⥤ E} {k : E ⥤ C}
  [f.Additive] [g.Additive] [f'.Additive] [g'.Additive] [h.Additive] [k.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits f'] [PreservesFiniteColimits f']
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

private theorem singleUnitsComp (adj : f ⊣ g) (adj' : f' ⊣ g') (adj'' : h ⊣ k)
    (lc : h.leftDerivedFunctor ≅ f.leftDerivedFunctor ⋙ f'.leftDerivedFunctor)
    (rc : g'.rightDerivedFunctor ⋙ g.rightDerivedFunctor ≅ k.rightDerivedFunctor)
    (X : C) (Y : D) (Z : E)
    (c : f.obj X ⟶ Y) (c' : f'.obj Y ⟶ Z) (c'' : h.obj X ⟶ Z)
    (hu : (adj.derivedAdjunction.comp adj'.derivedAdjunction).unit.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
        rc.hom.app (f'.leftDerivedFunctor.obj (f.leftDerivedFunctor.obj
          ((DerivedCategory.singleFunctor C 0).obj X))) =
      adj''.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        k.rightDerivedFunctor.map (lc.hom.app ((DerivedCategory.singleFunctor C 0).obj X)))
    (hc : f'.leftDerivedFunctor.map
        (f.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
          (DerivedCategory.singleFunctor D 0).map c) ≫
        f'.singleFunctorCompLeftDerivedFunctorIso.hom.app Y ≫
          (DerivedCategory.singleFunctor E 0).map c' =
      lc.inv.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        h.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
          (DerivedCategory.singleFunctor E 0).map c'') :
    adj.derivedSingleUnit X Y c ≫
        g.rightDerivedFunctor.map (adj'.derivedSingleUnit Y Z c') ≫
        rc.hom.app ((DerivedCategory.singleFunctor E 0).obj Z) =
      adj''.derivedSingleUnit X Z c'' := by
  rw [Adjunction.derivedSingleUnit_eq, Adjunction.derivedSingleUnit_eq,
    Adjunction.derivedSingleUnit_eq]
  exact pasteUnits adj.derivedAdjunction adj'.derivedAdjunction adj''.derivedAdjunction
    lc rc _ _ _
    (f.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map c)
    (f'.singleFunctorCompLeftDerivedFunctorIso.hom.app Y ≫
      (DerivedCategory.singleFunctor E 0).map c')
    (h.singleFunctorCompLeftDerivedFunctorIso.hom.app X ≫
      (DerivedCategory.singleFunctor E 0).map c'') hu hc
end

section
universe u'

/-- Pasting the two constant-object units gives the constant unit for the composite.
Source: blueprint lemma-class-diagonal-projective-line, proof step 3; the composition
normalization of upperStarConstantSheafIso.
(auxiliary; not a blueprint node)

Proof: expand the constant derived single units using derivedSingleUnit_eq. Naturality of the
second unit rewrites the two units as the unit of the composite adjunction, followed
by direct image of the two constant comparisons. The conjugate characterization of
rightDerivedLowerStarComp changes this to the unit of the composite morphism with
the pullback-composition comparison. On single objects the derived comparison is
the single of the underived comparison. upperStarConstantSheafIso_comp identifies
its product with the constant comparison for the composite. This gives precisely
the right-hand side, with no choice of comparison. -/
theorem constantDerivedUnit_comp (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z)
    (a : B) :
    let C₀ := (constantSheaf Z.smallEtaleTopology B).obj a
    let D₀ := (constantSheaf Y.smallEtaleTopology B).obj a
    let E₀ := (constantSheaf X.smallEtaleTopology B).obj a
    Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction B p) C₀ D₀
        ((Scheme.upperStarConstantSheafIso B p).hom.app a) ≫
      (lowerStar B p).rightDerivedFunctor.map
        (Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction B e) D₀ E₀
          ((Scheme.upperStarConstantSheafIso B e).hom.app a)) ≫
      (rightDerivedLowerStarComp B e p).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj E₀) =
    Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction B (e ≫ p)) C₀ E₀
      ((Scheme.upperStarConstantSheafIso B (e ≫ p)).hom.app a) := by
  dsimp only
  let C₀ := (constantSheaf Z.smallEtaleTopology B).obj a
  let D₀ := (constantSheaf Y.smallEtaleTopology B).obj a
  let E₀ := (constantSheaf X.smallEtaleTopology B).obj a
  let adjp := derivedUpperStarLowerStarAdjunction B p
  let adje := derivedUpperStarLowerStarAdjunction B e
  let adj := derivedUpperStarLowerStarAdjunction B (e ≫ p)
  let lc := leftDerivedUpperStarComp B e p
  let rc := rightDerivedLowerStarComp B e p
  have hm : conjugateEquiv (adjp.comp adje) adj lc.hom = rc.hom := by
    rw [conjugateEquiv_leftDerivedUpperStarComp_hom]
    rfl
  have hu := unit_conjugateEquiv (adjp.comp adje) adj lc.hom
    ((DerivedCategory.singleFunctor _ 0).obj C₀)
  rw [hm] at hu
  simp only [Functor.comp_obj] at hu
  refine singleUnitsComp
    (upperStarLowerStarAdjunction B p)
    (upperStarLowerStarAdjunction B e)
    (upperStarLowerStarAdjunction B (e ≫ p)) lc rc
    C₀ D₀ E₀
    ((Scheme.upperStarConstantSheafIso B p).hom.app
      a)
    ((Scheme.upperStarConstantSheafIso B e).hom.app
      a)
    ((Scheme.upperStarConstantSheafIso B (e ≫ p)).hom.app
      a) ?_ ?_
  · exact hu
  · exact
      leftDerivedUpperStar_map_singleFunctor_comp B e p
        (e ≫ p) rfl C₀
        ((Scheme.upperStarConstantSheafIso B p).hom.app
          a)
        ((Scheme.upperStarConstantSheafIso B (e ≫ p)).hom.app
          a)
        ((Scheme.upperStarConstantSheafIso B e).hom.app
          a)
        (Scheme.upperStarConstantSheafIso_comp B e p a)

end

section
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local instance 100001] ordinaryFiniteDerivedCategoryInstance
attribute [local implicit_reducible] ordinaryFiniteDerivedCategoryInstance
  ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor

attribute [local semireducible] supportedDerivedUnit
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors

private theorem nativeAdjunction_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedAdjunction =
      ordinaryFiniteAdjunction A f := by
  unfold ordinaryFiniteAdjunction derivedUpperStarLowerStarAdjunction
  rfl

private theorem nativeSingleComparison_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).singleFunctorCompLeftDerivedFunctorIso =
      singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f := by
  unfold singleFunctorCompLeftDerivedUpperStarIso
  rfl

/-- Expand the supported constant unit through the recorded finite adjunction.
Source: the canonical derived constant unit, Stacks 0A45.
(auxiliary; not a blueprint node).
Proof: first identify the full derived adjunction and single-comparison isomorphism
with their recorded forms. Expand the unchanged supported unit by derivedSingleUnit_eq,
apply those equations, and use ordinaryFiniteUnitPullback_hom for the two factors. -/
theorem supportedDerivedUnit_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportedDerivedUnit A f =
      (ordinaryFiniteAdjunction A f).unit.app (ordinaryFiniteUnit A Y) ≫
        (ordinaryFinitePushforward A f).map (ordinaryFiniteUnitPullback A f).hom := by
  unfold supportedDerivedUnit
  rw [Adjunction.derivedSingleUnit_eq, nativeAdjunction_eq, nativeSingleComparison_eq,
    ← ordinaryFiniteUnitPullback_hom]
  rfl

/-- The recorded constant units respect composition and the canonical direct-image
comparison. Source: blueprint projective-line diagonal calculation, unit pasting.
(auxiliary; not a blueprint node).

Proof: expand the recorded units. The generic constant-unit composition theorem
pastes the two derived adjunction units and identifies their constant-sheaf
comparison with the comparison for the composite. -/
theorem supportedDerivedUnit_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) :
    supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (supportedDerivedUnit A e) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p).hom.app
          (ordinaryFiniteUnit A X) = supportedDerivedUnit A (e ≫ p) := by
  exact constantDerivedUnit_comp (ModuleCat.{u + 1} A) e p (ModuleCat.of A A)

end

end AlgebraicGeometry.Etale
