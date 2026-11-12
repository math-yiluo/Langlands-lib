# Renard IV.3.2: admissibility of essentially square-integrable representations

Author: Worker 89.

`Langlands.Renard.CompactRepresentation.essentiallySquareIntegrableAdmissible`
proves the exact published `EssentiallySquareIntegrableAdmissibleStatement`,
with independent group and carrier universes. Source: David Renard,
*Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, IV.3.2 Proposition, printed p.100 / PDF p.106, and the twist
Lemma of III.1.14, printed p.67 / PDF p.73. Source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Exact hypotheses and proof route

The original representation is a smooth complex representation of a locally
compact Hausdorff totally disconnected group. The given Borel Haar measure
on the actual quotient by its center is also right invariant. Irreducibility,
an open-kernel character twist, a unitary central character for that twist,
and square integrability of all its smooth coefficients are the target's
only representation hypotheses. In particular, admissibility is concluded,
never assumed; the predicate `IsSquareIntegrableModCenter`, which builds
admissibility into its definition, is not used as a premise.

The implementation follows Renard's averaged-orbit argument, replacing his
explicit sequence of disjoint double cosets by a uniform coefficient bound.
The bound follows directly from integrability and right Haar invariance;
it avoids a separate enumeration of the double cosets. Published compact
averaging and fixed-functional extension results from
`CompactCoefficient.FixedVectorsFiniteDimensional` provide the algebraic
projection and smooth extensions, without assuming compact coefficients.

## The analytic bound

`bounded_sq_of_left_invariant` works for any Borel Haar measure `μ` that is
also right invariant, a compact open subgroup `H`, and a real L2 function
`f` invariant under left multiplication by `H`. For each `q`, integrate
`f(zq)^2` over `H`. This is the constant `f(q)^2` multiplied by `μ.real H`.
Nonnegativity bounds that integral by the integral over the whole group,
and right invariance identifies the latter with the original L2-square
integral. The subgroup has positive finite measure because it is nonempty,
open and compact. Dividing gives a uniform bound on `f(q)^2`.
No countability, regularity or inversion invariance is used.

`fixed_coefficient_bounded` applies this to the descended coefficient norm.
For a compact open subgroup `K` of the original group and any algebraic
functional `Φ` on the `K`-fixed space, the published `fixedExtension`
constructs a smooth functional `Λ` agreeing everywhere with `Φ ∘ P_K`.
Its `K`-invariance makes the coefficient norm left invariant under the
image `H` of `K` in the central quotient. This image is compact by continuity
and open by the open quotient map. The L2 hypothesis therefore bounds
`‖Λ(ρ(g)x)‖²` uniformly in `g`.

## Finite fixed spaces

`finite_fixedVectors_of_squareIntegrable` treats a compact open `K`. If its
fixed space is zero it is finite. Otherwise choose a nonzero fixed vector
`ξ`. Irreducibility makes its orbit span the carrier. The fixed projection
is surjective, so the averaged vectors `u(g) = P_K(ρ(g)ξ)` span the fixed
space. Select a basis within this averaged orbit using
`exists_linearIndependent` and `Module.Basis.mk`.

If the basis index type were infinite, `Infinite.natEmbedding` would select
distinct basis elements indexed by the natural numbers. Extend the prescribed
basis values `n : ℂ` to all basis elements with `Function.extend`, then use
`Basis.constr` to obtain an algebraic functional `Φ`. Each selected basis
vector is `u(g)` for some `g`, so its smooth extension satisfies
`Λ(ρ(g)ξ) = n`. The analytic bound would imply `n² ≤ C` for every natural
number. Choosing `n > max C 1` contradicts this. Thus the basis is finite
and `Module.Finite.of_basis` proves finite dimension.

The auxiliary Haar measure `ν` on the original group is used only for the
published compact fixed projection and extension. It is chosen internally
as Mathlib's `Measure.haar` after installing the Borel measurable structure
on the given locally compact group. It is not an added target premise, and
all square-integrability estimates still use the target's specified `μ`.

## Twists and all open subgroups

Van Dantzig's theorem gives a compact open subgroup inside each open subgroup
of the target group. Apply the finite-fixed-space result to the specified
twist; published twist irreducibility supplies its irreducibility. Finiteness
passes to the fixed vectors of every larger open subgroup by
`finite_fixedVectors_of_le`. This proves admissibility of the twist. The
published `SmoothRep.isAdmissible_twist_iff` then gives admissibility of the
original representation.

Every structural and analytic input is derived under the unchanged target
hypotheses. The uniform-bound step and the prescribed unbounded basis
functional are internal variants of Renard's proof. No finite length,
unitarity of the original representation, global finite dimension or
topology on its carrier is assumed.
