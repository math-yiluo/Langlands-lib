# Rational continuation on the actual normalized induction spaces

This module is a derived adapter for Waldspurger, *La formule de Plancherel
pour les groupes p-adiques*, IV.1, printed pp.276–277 (PDF pp.42–43).
It constructs a continuation on the actual canonical normalized induction
spaces from a supplied rationality witness for an original family. The
construction proves equivariance using polynomiality of the actual varying
actions. Analytic rationality of the standard intertwining integral remains
a separate obligation.

## Objects and hypotheses

The compact transport part uses a locally compact nonarchimedean topological
group `G`, two semidirect decompositions `Pᵢ = M Uᵢ` with the same literal
Levi subgroup `M`, closed `Pᵢ` and `Uᵢ`, and the existing
`IsUnimodularModulus Uᵢ hUᵢ` hypotheses. A compact open subgroup `K` satisfies
`G = Pᵢ K` for both parabolics, and both Levi projections are continuous.
The inducing representation is canonical `Langlands.SmoothRep ℂ M`.
A family of continuous norm characters defines the unramified parameters.
There is no admissibility, finite-dimensionality, irreducibility or
finite-length hypothesis on the inducing representation.

The polynomial transport part additionally uses a topological group `L`
and a topological group isomorphism `e : L ≃ₜ* M`. It transports the norm
characters by `e.symm`. The actual continuation part specializes `L` to
the rational points of a connected reductive group scheme over an arbitrary
nonarchimedean local field `F`. Its parameters are the unramified characters
defined from the actual rational norm characters. A topology on these
rational points, continuity `hp` of `rationalValuationImageProjection L`,
and continuity `hν` of each rational norm character are explicit premises.
The isomorphism `e` identifies those points with the common literal Levi.
This module supplies no realization of these subgroup or topology premises
for an arbitrary reductive ambient rational-point group.

The field, ambient group and inducing-carrier universes are independent.
The generic transport parts also permit an independent norm-index universe
and an independent group universe for `L`. No restriction on the
characteristic or splitness of the reductive group scheme is imposed.

Let `Ω` be the original parameter region. Continuation and uniqueness use
an explicitly supplied nonempty ambient open set `D` contained in `Ω`.
Thus `Ω` need not itself be open. Rationality means the imported
`IsRationalOperatorOn`: one regular denominator, nonzero everywhere on `Ω`,
clears the entire operator family; for each fixed input vector its cleared
values have a finite expansion in fixed output vectors with regular
coefficient functions. This is an explicit hypothesis about the original
family, not an external structural fact or a proof of standard-integral
rationality.

## Transport of the actual intertwiner spaces

Write `Rᵢ,χ` for the imported full equivariant restriction/extension
identification `unramifiedCompactRepresentationEquiv`. For every parameter,
`compactInductionIntertwinerEquiv` constructs the linear equivalence

`J ↦ R₁,χ ∘ J ∘ R₀,χ⁻¹`

between the full ambient intertwiner spaces of the actual normalized
inductions and their fixed compact carriers. Its inverse is
`B ↦ R₁,χ⁻¹ ∘ B ∘ R₀,χ`. These are full `G` intertwiner spaces.
The proof of each inverse identity uses the actual equivalence cancellation
laws; addition and scalar multiplication use linearity of `R₁,χ`.
`compactInductionIntertwinerEquiv_toLinearMap` identifies the underlying
forward map definitionally with the published `compactIntertwiningOperator`.

`unramifiedCompactRepresentation_transport_polynomial` transports the
published polynomiality of every fixed group action operator through `e`.
It keeps the finite output-vector family and transports the regular
coefficients through `unramifiedRegularFunctionsEquiv`. Its inverse
coefficient-evaluation identity gives the required expansion for all
original parameters. This proves the polynomial-action premises needed by
the continuation theorem for both actual compact representations.

## Constructed continuation and its identities

The input `J` assigns an actual ambient intertwiner of the two normalized
unramified inductions to each parameter in `Ω`. The definition
`compactInductionIntertwinerFamily` applies the constructed full Hom-space
equivalence. Its underlying linear map is exactly the original compact
conjugation, as recorded by its `_toLinearMap` theorem.

`compactInductionContinuationData` takes the rationality witness for this
compact conjugation together with `hp`, connected reductivity and the
nonempty open subset `D`. It invokes `rationalOperatorContinuation` to
construct a global polynomial operator numerator and a single regular
denominator clearing the original family. If `p` is such continuation
data, its `regularRegion` is precisely the full nonzero locus of that
denominator. On this region `p.continuedOperator` is the reciprocal
denominator times the polynomial numerator.

`continuedInductionIntertwiner` first uses `continuedIntertwiner` on the
actual compact representations and then applies the inverse constructed
Hom-space equivalence. The two polynomial-action proofs are supplied by
`unramifiedCompactRepresentation_transport_polynomial`; they are not
extra assumptions on `J`. The imported equivariance proof propagates the
original intertwining equation through polynomial uniqueness on `D`, so
the result is an actual ambient `G` intertwiner at each regular parameter.

The module proves the following consequences:

- `continuedInductionIntertwiner_compact` identifies its compact conjugation
  with exactly `p.continuedOperator`. The proof projects the forward/inverse
  Hom-equivalence cancellation to underlying linear maps.
- `continuedInductionIntertwiner_rational` uses this identity and the
  rationality of `p.continuedOperator`. The asserted rationality is on fixed
  compact carriers, as in the source; no single common ambient induced
  carrier is silently used for the varying parameters.
- `continuedInductionIntertwiner_agrees` recovers every original actual
  intertwiner on `Ω`. It transports the imported compact recovery identity
  through the inverse Hom equivalence and cancels inverse/forward transport.
- `continuedInductionIntertwiner_unique` proves equality of actual ambient
  intertwiners from any two continuation data at every common regular
  parameter. It applies the inverse Hom equivalence to the imported
  uniqueness identity. The denominators and their zero sets need not agree.

All restriction and extension maps in these identities are the existing
normalized induction maps. The construction introduces no rescaling of
operators or Haar measures.

## Source correspondence and remaining obligations

On printed p.276 Waldspurger identifies normalized unramified induction
with a parameter-independent compact section carrier. On p.277 he uses
this conjugation to define operator polynomiality and rationality, with a
single clearing denominator for all input vectors, and continues to its
nonzero locus. This module implements a derived representative-level
construction of that passage, using the already constructed norm-character
and regular-algebra transport and polynomial uniqueness for actual rational
characters. Its proof route and the absence of an admissibility premise
are derived content, rather than an assertion that the source itself
states that more general result.

The source also requires compatibility under every isomorphism between
inducing representatives and formulates the family on representation
orbits. This module takes one fixed inducing representation and works over
its character parameters. It does not assert that its family descends to
an orbit. Comparison with algebraic `B`-families, isomorphism-natural orbit
descent, convergence and rationality of the standard integral, composition
and normalizations of standard intertwiners, generic irreducibility,
global `j` and `mu`, and the main Plancherel results remain obligations of
the larger program. The supplied local rationality witness and explicit
geometric/topological premises must be discharged by consumers claiming
those results.
