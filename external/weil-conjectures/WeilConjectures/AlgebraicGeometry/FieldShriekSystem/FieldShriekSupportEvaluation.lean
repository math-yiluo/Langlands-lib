/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemModels

/-! # Normalized compact-support evaluation

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-support-evaluation).

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

/-- Finite compact-support evaluation in the recorded direct-image coordinates.
The ordinary pushforward change is the identity on sections.
Source: blueprint (2), finite b (blueprint: def-sp-field-shriek-support-evaluation). -/
structure FiniteCoordinates (E : Index P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) where
  push : proEtaleConstantRingPushforward (SpTowerShriek.R P.coefficients.l E.val n) c.g ≅
    proEtaleRingModuleDirectImage c.g
      (proEtaleConstantRing Y (SpTowerShriek.R P.coefficients.l E.val n))
      (proEtaleConstantRing c.Z (SpTowerShriek.R P.coefficients.l E.val n))
      (proEtaleConstantRingComparison c.g (SpTowerShriek.R P.coefficients.l E.val n))
  sections : ∀ (M : proEtaleRingModules c.Z
      (proEtaleConstantRing c.Z (SpTowerShriek.R P.coefficients.l E.val n)))
    (U : Y.ProEtᵒᵖ)
    (x : ((proEtaleConstantRingPushforward
      (SpTowerShriek.R P.coefficients.l E.val n) c.g).obj M).val.obj U),
    HEq (((push.hom.app M).val.app U) x) x

/-- Finite support comparison, using the specified termwise open comparison and
right-derived section-identity proper comparison.
Source: blueprint (2), finite support evaluation
(blueprint: def-sp-field-shriek-support-evaluation). -/
def supportEvaluation (D : Models P) (E : Index P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (z : FiniteCoordinates P E c n) :
    SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c ⋙
        SpTowerShriek.Ev P.coefficients.l E.val Y n ≅
      SpTowerShriek.Ev P.coefficients.l E.val X n ⋙
        reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g :=
  SpTowerShriek.Fcomparison P.coefficients.l E.val (D.base E) (D.operations E) c n ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso z.push))


end AlgebraicGeometry.ProEtale.FieldShriekSystem
