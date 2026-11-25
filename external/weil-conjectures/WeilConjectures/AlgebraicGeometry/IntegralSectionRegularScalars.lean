/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
public import WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalarsScalar
import all WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation

/-! # The scalar-compatible rank-one section comparison

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralSectionScalars
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule continuousScalarFunctor

/-- The specified continuous-scalar, point-pullback and section-action composite.
Source: Bhatt--Scholze, Proposition 6.8.11(3), integral scalar models
(auxiliary; not a blueprint node). -/
@[irreducible] def sectionRealization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Scheme.pbcModules X (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)) :=
  (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
   continuousScalarFunctor (Padic.coefficientExtensionIntegers l E)) ⋙
    (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
    integralSectionFunctor l E X ⋙
    SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom

/-- The specified completed-constant realization with the recorded scalar universe change.
Source: Bhatt--Scholze, Proposition 6.8.11(3), integral scalar models
(auxiliary; not a blueprint node). -/
@[irreducible] def completedRealization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Scheme.pbcModules X (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)) :=
  ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
      Padic.coefficientExtensionIntegers l E).toRingHom ⋙
    Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)

/-- Both realizations preserve finite colimits.
Source: Bhatt--Scholze, Proposition 6.8.11(3); scalar extension and inverse image are
left adjoints and section action and coefficient restriction are equivalences
(auxiliary; not a blueprint node). -/
private theorem finiteColimits (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    PreservesFiniteColimits (sectionRealization l E X) ∧
      PreservesFiniteColimits (completedRealization l E X) := by
  have hrestriction : PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom) :=
    (Scheme.integralDetailedCoefficientRestriction_exact X l E).2
  have hconstant :=
    (Scheme.integralConstantModule_exact X (Scheme.pbcIntegralDatum l E)).2
  have hc : PreservesFiniteColimits
      (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
       continuousScalarFunctor (Padic.coefficientExtensionIntegers l E)) := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    exact ContinuousScalarPresentation.continuous_colimits _
  have hr' : (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom).IsLeftAdjoint :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E)).toAdjunction.isLeftAdjoint
  have hp : (upperStarFromPoint X).IsLeftAdjoint := by
    unfold upperStarFromPoint
    exact (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have hpc : PreservesFiniteColimits (upperStarFromPoint X) := inferInstance
  have hpm : PreservesFiniteColimits
      ((upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)) := by
    infer_instance
  have hsc : PreservesFiniteColimits (integralSectionFunctor l E X) := by
    infer_instance
  have hsr := @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ hsc hrestriction
  have hpsr := @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ hpm hsr
  constructor
  · unfold sectionRealization
    exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ hc hpsr
  · unfold completedRealization
    infer_instance

private def scalarEndomorphism (A : Type u) [CommRing A] (a : A) :
    ModuleCat.of A (ULift.{u + 1} A) ⟶ ModuleCat.of A (ULift.{u + 1} A) :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := A) (M := A)).symm.toLinearMap.comp
    ((LinearMap.mulLeft A a).comp (ULift.moduleEquiv (R := A) (M := A)).toLinearMap))

private lemma endomorphism_eq_scalar (A : Type u) [CommRing A]
    (f : ModuleCat.of A (ULift.{u + 1} A) ⟶ ModuleCat.of A (ULift.{u + 1} A)) :
    f = scalarEndomorphism A (f.hom (ULift.up 1)).down := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  cases x with
  | up x =>
    change f.hom (ULift.up x) = ULift.up ((f.hom (ULift.up 1)).down * x)
    have hx : (ULift.up x : ULift.{u + 1} A) = x • (ULift.up 1) := by
      apply ULift.ext
      simp
    rw [hx, map_smul]
    change x • f.hom (ULift.up 1) = _
    apply ULift.ext
    simp [smul_eq_mul, mul_comm]

/-- The two fixed scalar realizations agree on the lifted regular module, compatibly
with every scalar endomorphism. This is a rank-one coefficient calculation; no finite
presentation, cokernel or arbitrary module is involved.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), the regular scalar
calculation in the integral constructibility bridge
(auxiliary; not a blueprint node).

Proof: constant sheafification sends the regular scalar module to the regular constant
coefficient module. Scalar extension sends it to the regular continuous coefficient
module by its adjunction, and point inverse image sends it to the regular pulled-back
coefficient module. Section action identifies this with the unit section module;
restriction along the prescribed ring isomorphisms identifies it with the completed
coefficient unit. On the completed-constant side, sheafification and scalar extension
likewise identify the lifted regular module with that same unit. These give the desired
isomorphism. A linear endomorphism of the lifted regular module is multiplication by
its value on the lifted element 1. On each positive uniformizer quotient the normalized
section-ring comparison and the normalized detailed comparison send this element to
its constant section. The constant completion map has the identical quotient formula.
The completion projections are jointly monic, so these scalar sections agree before
reduction. Naturality of scalar extension's unit and the point-pullback unit then
identifies the two endomorphisms of the unit module. This proves the displayed square.
The zero scalar and the empty scheme require no exception. -/
theorem regularComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ e : (sectionRealization l E X).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      (completedRealization l E X).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))),
      ∀ f : ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)),
        (sectionRealization l E X).map f ≫ e.hom =
          e.hom ≫ (completedRealization l E X).map f := by
  unfold sectionRealization completedRealization
  obtain ⟨e, he⟩ := scalarComparison l E X
  refine ⟨e, ?_⟩
  intro f
  let a := (f.hom (ULift.up 1)).down
  have hfa : f = scalarEndomorphism _ a := endomorphism_eq_scalar _ f
  rw [hfa]
  exact he a

end AlgebraicGeometry.ProEtale.IntegralSectionScalars
