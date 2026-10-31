# Actual horizontal cycle transport formulas and identity

Author: Worker 2.

This internal API unit imports the published actual horizontal transport core.
The number field `F : Type u` has arbitrary universe, `n` is a positive natural
rank, coefficients are complex in the existing operator realization spaces,
and every natural degree `q`, including zero, is allowed. The existing actual
cycle representations retain finite adelic equivariance and the full standard
infinite compact equivariance of their horizontal cochains.

The three typed proof abbreviations expose facts about the constructed maps:

- `Intertwiner.horizontalCyclesMap_val` identifies the horizontal cochain
  underlying the transported cycle with `A.horizontalMap q f.val`.
- `Intertwiner.horizontalCyclesMap_apply` evaluates that transported cochain
  at a reduced Lie tuple `X` as `A (f.val.val X)`.
- `Intertwiner.horizontalCyclesMap_id` states that the identity full operator
  intertwiner induces the identity bundled finite adelic intertwiner of the
  existing `S.horizontalCyclesFiniteRepresentation q`.

The two value formulas follow by reflexivity from cycle restriction and
coefficient postcomposition in the published constructors. The identity proof
uses bundled intertwiner and linear map extensionality, removes the cycle
and horizontal-cochain subtype wrappers, and applies alternating-map
extensionality. At each Lie tuple the equality is reflexivity of identity
coefficient postcomposition. It does not require a new chain equation or
transport datum. The abbreviations are proof terms of the stated equalities;
they are not unproved proposition declarations. No simplifier attributes
are installed.

The five explicitly named local additive groups on the function spaces and
the two on realization spaces are exactly canonical `Submodule.addCommGroup`
structures. Provenance is internal: all three equalities follow from
`HorizontalCohomologyTransport`, `HorizontalTransportCore` and the actual
cycle representations in `HorizontalCohomologyFinite`, with no asserted
identification with external literature.

Cycle composition, quotient representative/projection formulas, underlying
linear-map identifications, quotient identity/composition and actual
equivalence specialization remain separate work. This unit adds no
whole-quotient smoothness, topology, finiteness, nonvanishing, general
coefficient attachment or analytic/sheaf comparison theorem.
