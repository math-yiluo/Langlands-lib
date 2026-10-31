# Proof of small realizations of irreducible smooth p-adic representations

Author: Worker 273.

This module proves the published closed proposition
`Langlands.PadicIrreducibleSmoothSmallRealizationStatement.{uF,uW,uV}` from
[SmallRealizationStatement.md](SmallRealizationStatement.md). The closing
theorem is `Langlands.padicIrreducibleSmoothSmallRealization`. Its universe
parameters `uF`, `uW` and `uV` stay independent, and `uV = 0` is allowed.
Rank zero is included. The proof adds no hypothesis: it uses no admissibility,
positive rank, finite or countable dimension, assumed second countability,
cardinal bound, supplied carrier, or resizing equivalence. The topology on the
field is exactly `T.topology`, and the topology on the general linear group is
the one the statement uses, `T.generalLinearTopology n`. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The route is the one suggested in the statement's Markdown, except for the
field topology step: that step reuses a published theorem instead of using
`T.moduleTopology` directly.

## Transport along a linear equivalence

`transportRepresentation ρ e` conjugates a representation `ρ` on `V` by a
linear equivalence `e : V ≃ₗ[k] W`: the element `g` acts on `W` by
`e ∘ ρ g ∘ e⁻¹`. `transportRepresentationEquiv ρ e` packages `e` as an
actual `Representation.Equiv` from `ρ` to the transported representation. The
group is only a monoid here, and `k` is any commutative ring.

## Orbits of smooth vectors

The algebraic lemma `span_range_orbit_eq_top` is imported from
[`OrbitSpan`](../OrbitSpan.md). It states that the orbit of a nonzero vector
spans an irreducible representation. The declaration and proof were moved
there unchanged so other algebraic arguments can reuse them.

`countable_range_orbit` assumes `G` is a separable topological group. It
shows that the orbit of a smooth vector `v` is countable. Smoothness gives an
open subgroup `K` that fixes `v`. The published `mem_fixedVectors_iff`
unfolds that condition. Fix a countable dense set `D`
(`TopologicalSpace.exists_countable_dense`). For each `g`, the left coset
`g K`, written as the preimage of `K` under `h ↦ g⁻¹ h`, is open and contains
`g`. So it contains some `d ∈ D`. Then `ρ d v = ρ g (ρ (g⁻¹ d) v) = ρ g v`.
Thus the orbit is the image of `D`, which is countable.

## Realization in an arbitrary universe

`exists_irreducible_smoothRep_equiv_of_separable` assumes `G` is a separable
topological group in universe `uG`. For an irreducible
`π : SmoothRep.{0,uG,uW} ℂ G`, it builds an irreducible
`σ : SmoothRep.{0,uG,uV} ℂ G` and an actual equivalence of representations.
The proof runs as follows:

1. Irreducibility gives `⊥ ≠ ⊤` on subrepresentations, so `π` has a nonzero
   vector `v`.
2. The orbit `S` of `v` is countable (`countable_range_orbit`, using that
   every vector of `π` is smooth). It spans `π` (`span_range_orbit_eq_top`).
3. Mathlib's `exists_linearIndependent` gives a linearly independent subset
   `b ⊆ S` with the same span. Hence `b` is countable, and `Module.Basis.mk`
   makes `b` a basis of `π`.
4. `Countable b` gives `Small.{uV} b`. The basis representation, followed by
   `Finsupp.domLCongr (equivShrink.{uV} b)`, is a complex-linear equivalence
   `e : π ≃ₗ[ℂ] (Shrink.{uV} b →₀ ℂ)`. The target carrier lies in `Type uV`.
5. Let `σ` be the transport of `π.representation` along `e`. Smoothness
   passes to `σ` by the published `isSmooth_of_surjective`, applied to the
   intertwining map of the equivalence. Irreducibility passes by the
   published `isIrreducible_iff_of_equiv`.

Countability is only used for the spanning orbit and the basis inside it,
never for the complex scalars or the set of all vectors.

## Second countability of the p-adic general linear group

`PadicField.TopologicalData.generalLinearSecondCountableTopology T n` proves
that `GeneralLinear n F.Carrier` with `T.generalLinearTopology n` is second
countable. The published `PadicField.TopologicalData.secondCountableTopology`
gives second countability of the field with `T.topology`. Matrices are finite
products of the field, so they are second countable. So is their
multiplicative opposite (`MulOpposite.opHomeomorph`). Units carry the topology
induced by `Units.embedProduct` into matrices times the opposite. So
`Units.isInducing_embedProduct.secondCountableTopology` concludes. This
includes `n = 0`.

## Closing theorem

`padicIrreducibleSmoothSmallRealization` introduces `p`, `F`, `T` and `n`,
and fixes `T.topology`. It installs the published topological-group instance
`T.generalLinearTopologicalGroup n` and the second-countability result above.
A second-countable space is separable, so
`exists_irreducible_smoothRep_equiv_of_separable` at universes
`{uF, uW, uV}` gives the required irreducible `σ` and equivalence.

## Provenance

The target is internal, derived mathematics written by Workers 195 and 82.
It is not a transcription of a literature theorem about Lean universes. The
implementation follows the route recorded in the statement's Markdown: a
countable orbit of a smooth vector, spanning by irreducibility, a countable
basis, and reindexing into a small carrier.
