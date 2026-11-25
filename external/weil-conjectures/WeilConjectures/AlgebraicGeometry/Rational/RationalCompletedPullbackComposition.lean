/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange

/-! # Completed composition and descent to all raw rational fraction arrows.

## References

* Bhatt--Scholze, Remark 6.8.15, p. 62
* Stacks Tags 03CB, 0D6D, 07A4, 099N
* Stacks Tags 099N, 099J, 0A0E, 0B65 and 0DV0
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

/-- Completed composition and descent to all raw rational fraction arrows. -/
theorem rationalCompletedPullbackComposition (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX)
    (hcoefficient : (ac.rationalCoefficient =
  (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l X E) ≫
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.rationalCoefficient ≫
    ah.rationalCoefficient))
    (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
    rationalPullModule l E h ah.rationalCoefficient ≅
  rationalPullModule l E (h ≫ g) ac.rationalCoefficient)
    (hmodule :
      let unitSection {S T : Scheme.{u}} (g : S ⟶ T)
          (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
          (M : pbcModules T (rationalCoefficientSheaf l T E))
          (V : T.ProEt) (m : M.val.obj (op V)) :
          ((rationalPullModule l E g c).obj M).val.obj
            (op ((proEtaleBaseChange g).obj V)) :=
        pbcTensorSection c
          ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)
      let scalarSection {S T : Scheme.{u}} (g : S ⟶ T)
          (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
          (V : T.ProEt) (e : (rationalCoefficientSheaf l T E).obj.obj (op V)) :
          (rationalCoefficientSheaf l S E).obj.obj (op ((proEtaleBaseChange g).obj V)) :=
        c.hom.app (op ((proEtaleBaseChange g).obj V))
          (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
            (rationalCoefficientSheaf l T E)).hom.app (op V) e)
      let scalarMul (T : Scheme.{u})
          (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
          (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
        e • m
      (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
        (m : M.val.obj (op V))
        (e' : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange g).obj V)))
        (e'' : (rationalCoefficientSheaf l Z E).obj.obj
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
      (moduleComp.hom.app M).val.app
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (scalarMul Z
          ((rationalPullModule l E h ah.rationalCoefficient).obj
            ((rationalPullModule l E g ag.rationalCoefficient).obj M))
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) e''
          (unitSection h ah.rationalCoefficient
            ((rationalPullModule l E g ag.rationalCoefficient).obj M)
            ((proEtaleBaseChange g).obj V)
            (scalarMul Y
              ((rationalPullModule l E g ag.rationalCoefficient).obj M)
              (op ((proEtaleBaseChange g).obj V)) e'
              (unitSection g ag.rationalCoefficient M V m)))) =
        scalarMul Z
          ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
          (e'' * scalarSection h ah.rationalCoefficient
            ((proEtaleBaseChange g).obj V) e')
          -- The semilinear view exposes the target carrier without unfolding chart rings.
          (((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.restrictₛₗ
            ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
              (unitSection (h ≫ g) ac.rationalCoefficient M V m))))
    (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
    rationalPullDerived l E h ah.rationalCoefficient ≅
  rationalPullDerived l E (h ≫ g) ac.rationalCoefficient)
    (hderived : (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
  ambientComp.hom.app (DerivedCategory.Q.obj P) ≫
      rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient P =
    (rationalPullDerived l E h ah.rationalCoefficient).map
        (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
      rationalPullComplexCounit l E h ah.rationalCoefficient
        (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex moduleComp (.up ℤ)).hom.app P))) :
    ∃ (integralComp : ag.integral.completedFunctor l E ⋙ ah.integral.completedFunctor l E ≅
      ac.integral.completedFunctor l E),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
          ((ag.integral.completedFunctor l E).obj K).obj ≫
        (integralComp.hom.app K).hom =
      (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ g)).app K.obj) ∧
      ∃ (rawComp : ag.rawPull ⋙ ah.rawPull ≅ ac.rawPull),
      (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      rawComp.hom.app
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
        eqToHom (congrArg ah.rawPull.obj (ag.raw_objects K)) ≫
          eqToHom (ah.raw_objects ((ag.integral.completedFunctor l E).obj K)) ≫
          (pbcRationalization Z (pbcIntegralDatum l E) (pbcUniformizer l E)).map
            (integralComp.hom.app K) ≫ eqToHom (ac.raw_objects K).symm) ∧
      (whiskerRight rawComp.hom sZ.J ≫ ac.alpha.hom =
      whiskerLeft ag.rawPull ah.alpha.hom ≫
        whiskerRight ag.alpha.hom (rationalPullDerived l E h ah.rationalCoefficient) ≫
        whiskerLeft sX.J ambientComp.hom) := by sorry

end AlgebraicGeometry.Scheme
