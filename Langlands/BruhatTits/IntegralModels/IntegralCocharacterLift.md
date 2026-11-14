# Integral cocharacters and canonical specialization pairings

Worker 248. Internal supporting construction at arbitrary universe `u`.

Let `R` be a commutative local domain with specified fraction field `K`.
Let `D` be supplied relative-component model data for a generic group `G`,
and let `T` be supplied integral-torus data for a commutative generic group
`S` with map `i` into `G`. Assume that `T.torus` is split. Every actual
cocharacter of `S` lifts to a cocharacter of `T.torus` such that:

- Base-changing its composite with the integral inclusion and then using
  the neutral model's specified generic identification gives exactly the
  original cocharacter composed with `i`.
- Pairing its residue-base change with the canonical specialization of
  any generic character gives the original integer pairing.

The proof transports the generic cocharacter through `T.genericIso`,
then uses bijectivity of cocharacter base change for the split integral
torus. The exact ambient equality follows from `T.generic_comm`.
For a generic character, the inverse of `T.genericCharacterEquiv` supplies
its integral character. The definition of canonical specialization and
`latticePairing_baseChange` compare its generic and special pairings;
composition through the specified generic isomorphism gives the desired
pairing in `S`.

`IntegralTorusData.compatibleIntegralCocharacter` selects one such lift
and retains both equalities in its subtype. This construction is an
internal consequence of the imported actual split-torus base-change and
pairing APIs. It assumes neither a special-fibre maximality assertion nor
closedness of the integral inclusion, and asserts no root-depth criterion.
