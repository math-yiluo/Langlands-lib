# Irreducible square-integrable representations and left Haar measure

This module proves the derived helper
`Langlands.HarishChandraSchwartz.isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar`.
For a topological group `G`, a normal subgroup `A` contained in its center, a Borel
structure and left Haar measure `μ` on `G ⧸ A`, and cofinal compact open subgroups
of `G`, an irreducible representation that satisfies the published predicate
`IsSquareIntegrableModCentralSubgroup A hA ρ μ` is unitarizable.
The carrier has no topology, and its universe is independent of that of `G`.

## Provenance and relation to published mathematics

The proof implements the positive form on the smooth dual used in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, Lemma III.1.3, printed p. 264
(PDF p. 30), registered as `waldspurger-2003-plancherel`.
This is a derived, abstract-group helper for the irreducible case of that lemma.
It does not establish the topological or algebraic-group hypotheses for any
particular reductive group.

The Library module `SquareIntegrableSemisimplicity` already proves the more
general conclusion for square-integrable admissible representations with an
inversion-invariant quotient Haar measure. Here only left Haar invariance is
assumed. The construction integrates the original coefficients directly on
the smooth dual, without asserting that the smooth contragredient is square
integrable for the same measure.

## Construction and implemented proof

For a unitary central character `c`, a fixed vector `x`, and smooth functionals,
`LeftHaarDualForm.integrand A hA c x ℓ₁ ℓ₂` descends the function

`g ↦ ℓ₁(ρ(g)x) conj(ℓ₂(ρ(g)x))`

to `G ⧸ A`. The unitary character of the full center cancels in the product,
which proves descent. Smoothness of `ρ` makes the coefficients locally constant
and hence the integrand continuous. Its absolute value is the product of the
two coefficient norms, so the published square-integrability predicate and
the product estimate for two `L²` functions give integrability.

`LeftHaarDualForm.form` integrates that function. It is linear in its first
functional and conjugate symmetric. Acting on both functionals by `h` changes
the integrand by the left translation `g ↦ h⁻¹g`. Consequently
`form_invariant` needs only left invariance of `μ`.

The diagonal is real and nonnegative. If `ℓ(ρ(g)x)` is nonzero at any point,
its continuous diagonal integrand has nonempty open support, which has positive
Haar measure. The resulting diagonal integral is strictly positive.
`LeftHaarDualForm.positiveForm` swaps the arguments to match Mathlib's
conjugate-linear-first convention. It assumes that the orbit of `x` spans
the carrier. A functional whose values on that orbit all vanish has full kernel,
so the integrated form is definite.

For irreducible `ρ`, choose a nonzero `x`; the published
`span_range_orbit_eq_top` supplies the spanning hypothesis. This makes the
smooth contragredient unitarizable. Its admissibility follows from the original
admissibility and compact-open cofinality. The published
`isUnitarizable_smoothContragredient_of_admissible` then makes the double smooth
contragredient unitarizable. Pulling that form back along the injective canonical
`smoothBidual` proves the stated unitarity of `ρ`.
