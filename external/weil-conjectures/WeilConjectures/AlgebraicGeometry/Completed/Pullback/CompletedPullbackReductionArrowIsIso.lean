/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReducedUnit
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackFiniteMate

/-! Split result for the finite reduction of completed pullback.
(blueprint: definition-completed-inverse-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- Every projection-induced arrow in the completed reduction tower is invertible.

Source: Stacks Tag 099N (5), completed-pullback reduction, finite projection clause
(blueprint: lem-weil-pbc-completed-pullback-reduction-arrow-isIso).

Proof: first, finite scalar extension of the ordinary-to-completed pullback
comparison is invertible (lem-weil-pbc-completed-pullback-reduced-unit): through
the constant/completed coefficient equivalences and the Koszul presentation it is
the finite reduction of the completion unit, which is invertible because the ideal
acts nilpotently on finite quotients, the completion reflector gives Hom bijections
into restricted finite objects, and scalar adjunction with coyoneda detects the
isomorphism. Second, the composite of this finite comparison with the
projection-induced arrow is the finite scalar mate of the pulled quotient
augmentation (lem-weil-pbc-completed-pullback-finite-mate); on a flat-term K-flat
representative the finite evaluation normalization identifies it with the
invertible ordinary tensor/pullback mate, and naturality extends this to every
object. Cancelling the first isomorphism gives the claim. No completeness of the
output and no coherence clause is needed. The argument
allows the zero ring, empty scheme, and empty generating tuple. -/
theorem completedPullbackReductionArrow_isIso
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r f hf K C e) :
    ∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n) := by
  intro n
  have := completedPullbackComparison_reduction_isIso g d r f hf K C e _hK n
  have := completedPullbackComparison_finiteMate_isIso g d K n
  exact IsIso.of_isIso_comp_left
    ((reductionDerivedChange X (completedReductionProjection X d n)).map
      (completedPullbackComparison g d K)) (completedPullbackReductionArrow g d K n)

end AlgebraicGeometry.Scheme
