/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarFiniteBoundary
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralChernNormalization
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.TowerFiniteChernAssembly

/-! # Finite evaluation of an already normalized Chern construction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Normalization of the three adjunction comparisons fixes every finite Chern arrow.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2);
`SmoothPurityTowerClasses`, expanded proof steps 5--8.
(blueprint: lem-sfb-normalized-chern-finite-boundary).

Proof: write the first Chern arrow as the scalar extension of the reduced
lineBundleClass, with the stated unit inverse and target comparison. Apply the
reduction adjunction's Hom bijection. Naturality with respect to lineBundleClass
and sourceNormalization replace its precomposition with the integer generator
by the positive Kummer connecting morphism specified by targetNormalization.
For scalar extension, apply transpose_model on a K-flat representative and use
the universal counit naturality to pass to the original object. Together with
unitNormalization this identifies the second adjunct with that same arrow
followed by the root map z mapping to 1 tensor z. This does not assume that an
arbitrary root module in degree zero is K-flat.
The universal scalar counit supplies lineComparison, so this computation uses
the actual firstChern definition, including its shift comparison. Evaluate at
n and forget scalars; these exact functors preserve the single and shift
comparisons and the Kummer boundary. Their integer map agrees with
finiteQuotient by its unique values k mapping to k times one on constant
sections. Their root map agrees with finiteRootMap by its unique formula
z mapping to 1 tensor z. The pure-tensor equation defining lineEvaluation
identifies the finite target comparison. Substitute these equalities to get
the equality of composites in finiteBoundaryEquality, using the endpoint
transports of the two exact single comparisons for its HEq witnesses. This
proves the equation separately for every L and n without using any assertion
that evaluations detect equality of arbitrary derived arrows. The construction
is natural in L; trivial L and the empty scheme need no separate choices. -/
theorem finiteChernNormalization_of_normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (hc : c.Normalized l E) :
    FiniteChernNormalization l E c := by
  apply finiteChernNormalization_of_arrowComparisons l E c
  · intro L
    exact integralArrow_of_normalized l
      (Rrings l T) (Arings l E T) (coefficientSystemMap l E T) c
      (scalarGenerator l E T) hc (lineBundleClass T L)
  · intro f n
    exact scalarFiniteBoundary l E c hc.2.2 f n

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
