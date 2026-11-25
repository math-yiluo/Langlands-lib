/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemModels

/-! # Normalized evaluation of coefficient-system comparisons

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-system-evaluation).

All arrows below live in the ordinary derived category of the ringed sequence site.
The recorded section-preserving equivalence identifies this with the original strict
tower category. Index n denotes positive exponent n+1. The structures package the
specified constructions and their laws as conclusions, rather than assuming the
comparison or choosing a lift of its finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u a b a' b' vA vB vA' vB'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] coefficientMap HasDerivedCategory.standard

/-- Exact evaluation of coefficient restriction, fixed on all section carriers.
Source: blueprint (2), evaluation of simultaneous scalar models
(blueprint: def-sp-field-shriek-system-evaluation). -/
structure RestrictionEvaluation (D : Models P) {E F : Index P} (h : E ≤ F)
    (T : Scheme.{u}) (n : ℕ) where
  ordinary : SemilinearSections.res (coefficientMap P (D.coefficients E F h) T) ⋙
      SpTowerShriek.ev P.coefficients.l E.val T n ≅
    SpTowerShriek.ev P.coefficients.l F.val T n ⋙
      proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := T) ((D.coefficients E F h).quotient n))
  sections : ∀ (M : SpTowerShriek.S P.coefficients.l F.val T) (U : T.ProEtᵒᵖ)
    (x : ((SemilinearSections.res (coefficientMap P (D.coefficients E F h) T) ⋙
      SpTowerShriek.ev P.coefficients.l E.val T n).obj M).val.obj U),
    HEq (((ordinary.hom.app M).val.app U) x) x

/-- Exact localization of the uniquely section-normalized restriction comparison.
Source: blueprint (2), simultaneous evaluation
(blueprint: def-sp-field-shriek-system-evaluation). -/
def restrictionEvaluation (D : Models P) {E F : Index P} (h : E ≤ F)
    (T : Scheme.{u}) (n : ℕ) (r : RestrictionEvaluation P D h T n) :
    SemilinearSections.resD (coefficientMap P (D.coefficients E F h) T) ⋙
        SpTowerShriek.Ev P.coefficients.l E.val T n ≅
      SpTowerShriek.Ev P.coefficients.l F.val T n ⋙
        scalarRestriction ((D.coefficients E F h).quotient n) T :=
  Functor.mapDerivedCategorySquareIso r.ordinary

attribute [local irreducible] restrictionEvaluation

/-- Evaluation compatibility of two actual adjunctions is equality of the right mate
with the given restriction square. This is the adjunction-transpose equation, before
any claim of conservativity. Source: blueprint (2), scalar evaluation normalization
(blueprint: def-sp-field-shriek-system-evaluation). -/
@[irreducible] def AdjunctionEvaluationNormalized
    {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    {U : A ⥤ A'} {V : B ⥤ B'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (left : L ⋙ V ≅ U ⋙ L') (right : R ⋙ U ≅ V ⋙ R') : Prop :=
  (mateEquiv adj adj' left.inv) = right.hom

/-- The specified finite scalar adjunction with its functors made explicit.
Source: blueprint (2), finite scalar normalization
(blueprint: def-sp-field-shriek-system-evaluation). -/
@[irreducible] def finiteScalarAdjunction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarExtensionFunctor φ T ⊣ scalarRestriction φ T :=
  proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)

/-- Derived scalar evaluation, normalized by the actual two scalar adjunctions.
The transpose equation fixes the comparison on all derived morphisms.
Source: blueprint (2), evaluation of C_T
(blueprint: def-sp-field-shriek-system-evaluation). -/
structure ScalarEvaluation (D : Models P) {E F : Index P} (h : E ≤ F)
    (T : Scheme.{u}) (n : ℕ) where
  restriction : RestrictionEvaluation P D h T n
  iso : (D.scalars E F h T).T ⋙ SpTowerShriek.Ev P.coefficients.l F.val T n ≅
    SpTowerShriek.Ev P.coefficients.l E.val T n ⋙
      scalarExtensionFunctor ((D.coefficients E F h).quotient n) T
  transpose : AdjunctionEvaluationNormalized (D.scalars E F h T).adjunction
    (finiteScalarAdjunction ((D.coefficients E F h).quotient n) T) iso
    (restrictionEvaluation P D h T n restriction)


end AlgebraicGeometry.ProEtale.FieldShriekSystem
