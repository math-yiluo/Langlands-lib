# Xi coefficient bounds on the literal standard Levi

This module is an internal adapter of the published rational square-integrable
coefficient-decay proof and group/measure transport constructions. Its finite
central-quotient step is `CentralFiniteIndexCoefficientBound`. It makes no new
original-literature assertion. All declarations are in
`Langlands.HarishChandraSchwartz`.

The ambient data are an arbitrary nonarchimedean local field, a connected
reductive group `G`, its maximal split torus and a generic cocharacter, and a
standard index `I`. Write `L` for the actual standard Levi group scheme and
`M_I(F)` for its literal subgroup of `G(F)`. The representation `π` is the
original irreducible admissible complex representation of that literal subgroup.
The field and representation-carrier universes remain independent. The result
uses the given split component `s` of `L`, the explicit finite-index premise
on its actual split valuation image, and square integrability of `π` modulo
`rationalLeviSplitCenter I s` for the displayed quotient Haar measure `mu`.
Both quotient normality instances and the Borel structure on the displayed
literal quotient are explicit.

Let `K` be the given compact open ambient subgroup. The result retains an
explicit Levi Iwasawa pair for `(P₀(F) ∩ M_I(F), K ∩ M_I(F))`, which defines
the actual `rationalLeviXi`. It also retains a compact subgroup `K0L` of the
intrinsic `L(F)` with `SimultaneousStandardBasisAt` and `FiniteCartanCovering`
for the inherited maximal split torus and generic cocharacter of `L`.
These are intermediate structural inputs, not analytic output assumptions.
A matrix representation `ρ` of `G` on a nonempty `Fin N` supplies its
restriction to `L` for the rapid-decay proof. It need not be a closed immersion.

`hasXiBoundedCoefficients_standardLeviSquareIntegrable` derives
`HasXiBoundedCoefficients (rationalLeviXi hKc hMK) π.obj.representation`.
Thus, for every vector `v` and smooth functional `ell`, there is one positive
real constant bounding `norm (ell(π(m)v))` by that constant times the actual
Levi Xi function at every literal Levi point `m`. A coefficient bound is a
conclusion of the adapter, not an assumed premise.

The implementation uses the following published identifications.

1. `leviSchemeRepresentation` pulls the original representation back along the
   canonical continuous multiplicative equivalence `L(F) ≃ M_I(F)`, on the
   same carrier.
2. `standardLeviIntrinsicQuotientHaar` is the pullback of the given `mu` along
   the actual central-quotient homeomorphism. Its Haar instance and
   `map_standardLeviIntrinsicQuotientHaar` give the exact pushforward equality.
   `isSquareIntegrableModCentralSubgroup_comp_iff` therefore transports the
   displayed square integrability to the intrinsic Levi without a scale change.
3. The published connected-reductive, maximal-split and generic-cocharacter
   lemmas supply the intrinsic Levi geometry. `leviSchemeCompact` is the
   preimage of `K`, with the published open/compact and Iwasawa properties.
4. `hasXiBoundedCoefficients_of_rationalSquareIntegrable` applies the published
   rapid-decay helper to these data and then extends its order-zero norm-kernel
   bound across the finite central quotient. This consumes the original
   finite-index valuation premise and obtains a bound on all of `L(F)`.
5. `hasXiBoundedCoefficients_leviSchemeRepresentation_iff` transports that bound
   to the original representation, using the published equality of the
   intrinsic and literal Levi Xi functions for the matching compact subgroup.

`standardLeviSquareIntegrableCoefficientConstant` selects the resulting
constant for each original vector and smooth functional.
`standardLeviSquareIntegrableCoefficientConstant_spec` proves its positivity
and coefficient inequality on every literal Levi point.

The structural basis and Cartan existence problem is not solved here, and the
Levi Iwasawa pair is not derived from an arbitrary ambient Iwasawa pair. The
module proves no full-height wave-packet estimate or Schwartz-valued synthesis.
It does not modify or complete the exact source-normalized VI.3.1 targets.
