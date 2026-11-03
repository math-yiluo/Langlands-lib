# Finite chamber Cartan charts modulo the full center

`Langlands.FiniteChamberCartanCoverStatement` is an internal geometric reduction
for a lattice Cartan cover. The label, lattice-group and ambient-group universes
are independent. The ambient group is any topological group, and `K` is a
compact set; it need not be a subgroup.

Let `e` map an additive commutative group `X`, written multiplicatively, into
the ambient group `G`. Let a finite family of integral additive pairings on
`X` admit standard vectors: for every subset of labels there is a vector with
zero pairings on that subset and positive pairings off it. Assume that vectors
in the common pairing kernel map into the full group center. A finite set
`F₀` and an integer `B` supply a cover

`g = k₁ * e(x) * f * k₂`,

with `k₁,k₂ ∈ K`, `f ∈ F₀`, and every pairing of `x` at least `-B`.

There are diagonal generators `gen α`, positive in their own pairing and zero
in every other pairing, and a finite set `T ⊆ G` such that every element is

`g = k₁ * e(∑ α, n α • gen α) * t * k₂ * z`,

where `n : Δ → ℕ`, `k₁,k₂ ∈ K`, `t ∈ T`, and `z` belongs to the full center
`Subgroup.center G`. Thus their images form finitely many natural-lattice
charts covering the actual full central quotient. The conclusion also states
that this quotient is compact if the label type is empty.

The internal derivation uses the finite orthant decomposition of integral
pairings. Its finite remainder representatives combine with `F₀` to give `T`.
The common-kernel term commutes past the remaining factors and lies in the
full center. For empty labels the generator sum is zero, so the compact set
`K * T * K` meets every central coset; continuity of the quotient map gives
compactness.

This assertion isolates an algebraic and topological consequence of a Cartan
cover. It does not construct such a cover, an actual lattice model or the
central-kernel comparison for a reductive group. In particular, actual
empty-root compactness still requires those inputs. No Haar measure, cell
volume, coefficient estimate or square-integrability claim is included.
