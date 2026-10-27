# Independence of closure inflation from the chosen isomorphism

Author: Worker 272.

This module states one proposition,
`ClosureInflationTransportIndependence.{u,v}`. It defines no data and proves
nothing.

## Objects

- `K : Type u` is any field. `AlgebraicClosure K` is Mathlib's algebraic
  closure.
- `E₁ E₂ : IntermediateField K (AlgebraicClosure K)` are finite-dimensional and
  normal over `K`. For such a subfield `E`, `closureInflation K E 2`
  (`FiniteComparison`) is the published map from ordinary relative cohomology
  `H²(Gal(E/K), E^×)` to continuous absolute cohomology
  `H²(Gal(K̄/K), K̄^×)`. It is the inverse finite comparison followed by
  continuous inflation.
- `L : Type v` is any field with a `K`-algebra structure, in a universe
  independent of `K`.
- `e₁ : L ≃ₐ[K] E₁` and `e₂ : L ≃ₐ[K] E₂` are two `K`-algebra isomorphisms.
  `relativeH2Equiv eᵢ` (`RelativeH2Transport`) is the published additive
  equivalence from `H²(Gal(L/K), L^×)` to `H²(Gal(Eᵢ/K), Eᵢ^×)`. It sends the
  class of a cocycle `z` to the class of `(s, t) ↦ eᵢ(z(eᵢ⁻¹ s eᵢ, eᵢ⁻¹ t eᵢ))`.

## Proposition

`ClosureInflationTransportIndependence` asserts that for all such data and every
class `x` in `H²(Gal(L/K), L^×)`:

`closureInflation K E₂ 2 (relativeH2Equiv e₂ x) =
closureInflation K E₁ 2 (relativeH2Equiv e₁ x)`.

So the absolute class of a relative class does not depend on how `L` is
identified with a normal finite subfield of the algebraic closure. The
proposition is used to show that a relative invariant defined through one
chosen embedding agrees with the absolute invariant, whichever embedding was
chosen.

## Provenance

Two `K`-isomorphic normal subfields of `K̄` are equal, so `e₂ ∘ e₁⁻¹` is a
`K`-automorphism `τ` of `E = E₁ = E₂`. Transport along `e₂` is transport along
`e₁` followed by transport along `τ`. Transport along `τ` is the map that
Serre's compatible pair `s ↦ t s t⁻¹`, `a ↦ t⁻¹ a`, with `t = τ⁻¹`, induces on
`H²(Gal(E/K), E^×)`. Serre, *Local Fields* (GTM 67, 1979), Chapter VII, §5,
Proposition 3 (printed page 116, PDF page 122) shows that these automorphisms
are the identity. The proposition is therefore a derived formulation of that
result, phrased with the published closure-inflation and transport maps. It is
an internal lemma for building local invariants. It is not a separately stated
theorem in the literature.
