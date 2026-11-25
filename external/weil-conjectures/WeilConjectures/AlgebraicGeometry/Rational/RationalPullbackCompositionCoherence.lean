/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.CategoryTheory.ReflectedCompositor.ReflectedCompositorUnitNormalization
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.CategoryTheory.Ringed.RingedPushforwardCompletion
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

import WeilConjectures.AlgebraicGeometry.LocalizedOrdinary.LocalizedOrdinaryCoefficientCoherence
import WeilConjectures.AlgebraicGeometry.Rational.RationalOrdinaryPullbackComposition
import WeilConjectures.AlgebraicGeometry.Rational.RationalOrdinaryPullbackIdentity
import WeilConjectures.AlgebraicGeometry.Rational.RationalCompletedPullbackComposition
import WeilConjectures.AlgebraicGeometry.Rational.RationalCompletedPullbackIdentity

/-! # Composition and identity of normalized rational pullback

The ordinary maps are fixed on sheafified tensor generators and derived computation
counits. Completed maps retain the strict quotient-tower units; their raw
rationalizations retain all fraction arrows.

## References

* Bhatt--Scholze, Remark 6.8.15, p. 62
* Stacks 03D2
* Stacks 03CB, 0D6D, 07A4 and 099N
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

/-- The tensor-unit section of ordinary rational pullback on a pulled-back chart. -/
def rationalCoherenceUnit {S T : Scheme.{u}} (g : S ⟶ T)
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

/-- Pull a rational coefficient section through the ring adjunction unit and structure map. -/
def rationalCoherenceScalar {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (V : T.ProEt) (e : (rationalCoefficientSheaf l T E).obj.obj (op V)) :
    (rationalCoefficientSheaf l S E).obj.obj (op ((proEtaleBaseChange g).obj V)) :=
  c.hom.app (op ((proEtaleBaseChange g).obj V))
    (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
      (rationalCoefficientSheaf l T E)).hom.app (op V) e)

/-- Scalar multiplication on the rational module at a chart, with explicit section types. -/
def rationalCoherenceSmul (T : Scheme.{u})
    (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
    (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
  e • m

attribute [irreducible] rationalCoherenceUnit rationalCoherenceScalar rationalCoherenceSmul

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

set_option maxHeartbeats 700000 in
-- Tensor-generator coordinates unfold nested inverse-image and scalar-extension sections.
/-- The composition equation with all specified ordinary, completed and raw maps.
The module formula uses generators on base-changed charts; sheafification and balancing
extend it to local tensors. Derived normalization fixes the ambient comparison itself. -/
def HasRationalPullbackCompositionCoherence (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX) : Prop :=
  (∀ n : ℕ,
  completedFiniteCoefficientMap (h ≫ g) (pbcIntegralDatum l E) n =
    (proEtaleRingInverseImageComp h g).hom.app
        ((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n)) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n) ≫
      completedFiniteCoefficientMap h (pbcIntegralDatum l E) n) ∧
  (completedCoefficientMap (h ≫ g) (pbcIntegralDatum l E) =
  (proEtaleRingInverseImageComp h g).hom.app (pbcAdicCompletion X (pbcIntegralDatum l E)) ≫
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
      (completedCoefficientMap g (pbcIntegralDatum l E)) ≫
    completedCoefficientMap h (pbcIntegralDatum l E)) ∧
  (∀ n : ℕ,
  (proEtaleRingInverseImageComp h g).hom.app (pbcAdicCompletion X (pbcIntegralDatum l E)) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (completedCoefficientMap g (pbcIntegralDatum l E)) ≫
      completedCoefficientMap h (pbcIntegralDatum l E) ≫
      pbcAdicProjection Z (pbcIntegralDatum l E) n =
    completedCoefficientComponent (h ≫ g) (pbcIntegralDatum l E) n) ∧
  (ac.rationalCoefficient =
  (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l X E) ≫
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.rationalCoefficient ≫
    ah.rationalCoefficient) ∧
  ∃ (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
    rationalPullModule l E h ah.rationalCoefficient ≅
  rationalPullModule l E (h ≫ g) ac.rationalCoefficient),
  (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e' : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (e'' : (rationalCoefficientSheaf l Z E).obj.obj
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
  (moduleComp.hom.app M).val.app
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
    (rationalCoherenceSmul l E Z
      ((rationalPullModule l E h ah.rationalCoefficient).obj
        ((rationalPullModule l E g ag.rationalCoefficient).obj M))
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) e''
      (rationalCoherenceUnit l E h ah.rationalCoefficient
        ((rationalPullModule l E g ag.rationalCoefficient).obj M)
        ((proEtaleBaseChange g).obj V)
        (rationalCoherenceSmul l E Y
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          (op ((proEtaleBaseChange g).obj V)) e'
          (rationalCoherenceUnit l E g ag.rationalCoefficient M V m)))) =
    rationalCoherenceSmul l E Z
      ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M)
      (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (e'' * rationalCoherenceScalar l E h ah.rationalCoefficient
        ((proEtaleBaseChange g).obj V) e')
      (((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.map
        ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
          (rationalCoherenceUnit l E (h ≫ g) ac.rationalCoefficient M V m))) ∧
  ∃ (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
    rationalPullDerived l E h ah.rationalCoefficient ≅
  rationalPullDerived l E (h ≫ g) ac.rationalCoefficient),
  (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
  ambientComp.hom.app (DerivedCategory.Q.obj P) ≫
      rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient P =
    (rationalPullDerived l E h ah.rationalCoefficient).map
        (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
      rationalPullComplexCounit l E h ah.rationalCoefficient
        (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex moduleComp (.up ℤ)).hom.app P)) ∧
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
    whiskerLeft sX.J ambientComp.hom)

/-- Identity normalization, including the ordinary tensor formula and the raw natural equation. -/
def HasRationalPullbackIdentityCoherence (sX : RationalModuleRealization l E X)
    (a : RationalRealizationPullbackComparison l E (𝟙 X) sX sX) : Prop :=
  (∀ n : ℕ,
  completedFiniteCoefficientMap (𝟙 X) (pbcIntegralDatum l E) n =
    (proEtaleRingInverseImageId X).hom.app
      ((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n))) ∧
  (completedCoefficientMap (𝟙 X) (pbcIntegralDatum l E) =
  (proEtaleRingInverseImageId X).hom.app
    (pbcAdicCompletion X (pbcIntegralDatum l E))) ∧
  (a.rationalCoefficient =
  (proEtaleRingInverseImageId X).hom.app
    (rationalCoefficientSheaf l X E)) ∧
  ∃ (moduleId : rationalPullModule l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _),
  (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
    (m : M.val.obj (op V))
    (e : (rationalCoefficientSheaf l X E).obj.obj (op ((proEtaleBaseChange (𝟙 X)).obj V))),
  (moduleId.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
      (rationalCoherenceSmul l E X
        ((rationalPullModule l E (𝟙 X) a.rationalCoefficient).obj M)
        (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
        (rationalCoherenceUnit l E (𝟙 X) a.rationalCoefficient M V m)) =
    rationalCoherenceSmul l E X M (op ((proEtaleBaseChange (𝟙 X)).obj V)) e
      (M.val.map ((MorphismProperty.Over.pullbackId _ _ X).hom.app V).op m)) ∧
  ∃ (ambientId : rationalPullDerived l E (𝟙 X) a.rationalCoefficient ≅ 𝟭 _),
  (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
  ambientId.hom.app (DerivedCategory.Q.obj P) =
    rationalPullComplexCounit l E (𝟙 X) a.rationalCoefficient P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex moduleId (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P)) ∧
  ∃ (integralId : a.integral.completedFunctor l E ≅ 𝟭 _),
  (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
  (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (𝟙 X)).app K.obj ≫
    (integralId.hom.app K).hom =
      (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) X).hom.app K.obj) ∧
  ∃ (rawId : a.rawPull ≅ 𝟭 _),
  (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
  rawId.hom.app
      ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
    eqToHom (a.raw_objects K) ≫
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (integralId.hom.app K)) ∧
  (a.alpha.hom ≫ whiskerLeft sX.J ambientId.hom = whiskerRight rawId.hom sX.J)

attribute [irreducible] HasRationalPullbackCompositionCoherence
  HasRationalPullbackIdentityCoherence

/-- The specified realization comparisons commute with composition of scheme morphisms. -/
theorem rationalPullbackCompositionCoherence (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX) :
    (HasRationalPullbackCompositionCoherence l E g h sX sY sZ ag ah ac) := by
  unfold HasRationalPullbackCompositionCoherence
  have hc := LocalizedOrdinary.localizedOrdinaryCoefficientCoherence l E g h
  obtain ⟨hcoefficient, moduleComp, hmodule, ambientComp, hderived⟩ :=
    rationalOrdinaryPullbackComposition l E g h sX sY sZ ag ah ac
  refine ⟨hc.finite_comp, hc.completed_comp, ?_, hcoefficient,
    moduleComp, ?_, ambientComp, hderived, ?_⟩
  · intro n
    have hp : completedCoefficientMap (h ≫ g) (pbcIntegralDatum l E) ≫
        pbcAdicProjection Z (pbcIntegralDatum l E) n =
          completedCoefficientComponent (h ≫ g) (pbcIntegralDatum l E) n :=
      limit.lift_π _ (op n)
    rw [hc.completed_comp] at hp
    simpa only [Category.assoc] using hp
  · simpa only [rationalCoherenceUnit, rationalCoherenceScalar, rationalCoherenceSmul]
      using hmodule
  · exact rationalCompletedPullbackComposition l E g h sX sY sZ ag ah ac
      hcoefficient moduleComp hmodule ambientComp hderived

end AlgebraicGeometry.Scheme
