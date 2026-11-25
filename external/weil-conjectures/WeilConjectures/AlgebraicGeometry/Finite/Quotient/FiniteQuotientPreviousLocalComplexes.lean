/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientPreviousLocalComplexesAux

/-! # Local algebraic complexes for a coefficient-filtration outer term
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-previous-local-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The previous perfect complex gives finite local complexes over the successor ring.

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-previous-local-complexes).

Proof: Let E=A/I^(n+1) and B=A/I^(n+2). On a chart of the supplied previous
model, regard its finite-projective E-complex as a B-complex by the quotient
B -> E. Its terms remain finite over B because the quotient is surjective, and
its support remains [a,b]. The compatibility square for φ identifies restriction
of its constant E-realization with its constant B-realization. Restriction of
scalars, slice restriction, and realization along the coefficient isomorphisms
are exact, so the localization comparison identifies the homology of the actual
previous object with constant realization of the algebraic B-complex homology.
The comparison for the canonical representative follows from the localization
unit isomorphism. Pull back the model cover along every W -> V. No residue model,
coefficient-layer tensor calculation, or cohomology of the successor is used;
empty charts and the zero ring are included. -/
theorem finiteQuotient_previous_local_complexes
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b) (n : ℕ)
    (hprevious : FinitePerfectModelsOn X d φ M n V a b) :
    FiniteCoefficientLocalHomologyModels X (A ⧸ d.ideal ^ (n + 1 + 1))
      (φ (n + 1)) (finiteQuotientPreviousObject X d M n) V a b := by
  intro W g
  obtain ⟨T, hT, hmodels⟩ := hprevious
  refine ⟨T.pullback g, X.smallEtaleTopology.pullback_stable g hT, ?_⟩
  intro Z f hf
  obtain ⟨P, haP, hbP, hfiniteP, ⟨e⟩⟩ := hmodels Z (f ≫ g) hf
  obtain ⟨Q, hQa, hQb, hQfinite, hQe⟩ :=
    finiteQuotient_previous_local_complexes_chart X d φ hφ hcompat M V W Z g f
      a b hab n P haP hbP hfiniteP ⟨e⟩
  refine ⟨Q, ?_, hQfinite, hQe⟩
  intro q hq
  rcases hq with hq | hq
  · exact Q.isZero_of_isStrictlyGE a q hq
  · exact Q.isZero_of_isStrictlyLE b q hq

end AlgebraicGeometry.Scheme
