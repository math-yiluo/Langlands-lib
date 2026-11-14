# NYLL and FLT ramification comparison

This module contains internal lemmas for the exact M327.009 proof in
`RestrictionProof`. All declarations live in
`Langlands.NYLL.PortInternal.FltBridge`; none is a new source theorem target.
They are derived by Worker 296 from published NYLL and FLT definitions and
published `Langlands.Ramification.HerbrandBridge` transport lemmas.

The parameters are fields `K : Type u` and `L : Type w` with a K-algebra
structure, DVFs `base` and `target` with value groups in independent universes
v and x, a supplied valuation-extension instance, and
`huniq : DVF.HasUniqueValuationExtension.{u,v,w,x,x} base target`.
Finiteness of L/K is required only in the upper-group and real-interval lemmas.

## Constructed action and lower groups

`valuationAutHom` is the monoid homomorphism taking a K-automorphism to the
published `valuationSubringAutOfUniqueExtension huniq`. Its multiplication
laws are checked on the underlying field elements. `valuationAction` is the
corresponding semiring action on the target valuation ring; it is installed
only locally. `action_faithful` uses the fraction-field property of that ring
and `IsFractionRing.ringHom_ext`.

For every natural n, `lower_nat_eq` identifies the NYLL lower group at real n
with `IsLocalRing.lowerRamificationGroup` at n by the published
`mem_lowerRamificationGroup_nat_iff`. For a nonnegative real s,
`lower_real_eq` identifies the NYLL lower group with the FLT natural group
at `ceil(s)`. It rewrites NYLL's exponent `Int.toNat (ceil(s+1))` as
`Nat.ceil s + 1`; the ideal membership conditions are then identical.

## Herbrand functions and upper groups

`herbrand_rat` identifies the NYLL real Herbrand function at every rational q
with the real cast of FLT's rational `IsLocalRing.herbrandPhi`. At q <= 0
both functions are the identity. At positive q, the two floor formulas agree:
the natural lower-group cardinalities agree by `lower_nat_eq`, and the
published `HerbrandBridge.sum_Icc_one_eq_sum_range` converts the sum indexing.
The same module's `natFloor_ratCast` handles casts of the natural floor.

For finite L/K and q >= 0, `upper_rat_eq` identifies the NYLL upper group at
real q with FLT's rational upper group at q. Strict monotonicity of the NYLL
Herbrand function and the two inverse identities identify the NYLL inverse
value with the real cast of FLT's `herbrandPsi`. The nonnegative lower-group
comparison and `upperRamificationGroup_eq_ceil_herbrandPsi` then give the
result. `Int.ceil_toNat` and `Rat.ceil_cast` identify the ceiling indices.

`phi_zero` and `psi_nonneg` record zero preservation and nonnegativity of the
NYLL inverse. `upper_eq_lower_ceil` expresses the real upper group at t >= 0
as the NYLL lower group at `Nat.ceil (psi t)`.

`exists_rat_upper_const` chooses n = `Nat.ceil (psi t)` and
q = `IsLocalRing.herbrandPhi ... n`. The rational comparison shows that the
NYLL Herbrand value at n is q. Monotonicity gives q >= 0 and t <= q.
For t <= s <= q, monotonicity of psi and the ceiling bound imply
`Nat.ceil (psi s) = n`, so every upper group on that closed interval equals
the group at t. This also covers t = 0 without any density argument.

## Equivariant ring and group transport

The final section takes local commutative rings A, B, groups G, G', their
semiring actions, a ring equivalence e, a group equivalence f, and an explicit
equivariance identity. `phi_of_equivariant` substitutes the published
`HerbrandBridge.lowerRamificationCard_of_equivariant` into the rational
Herbrand formula (and uses the identity formula at nonpositive indices).
For finite G and G', `psi_of_equivariant` follows by injectivity of phi;
`upper_of_equivariant` follows from the natural-ceiling description of the
upper groups and the published equivariant lower-group image theorem.
No characteristic, completeness, residue-field or faithfulness premise is
needed for these generic transport lemmas.

## Source correspondence and modifications

The exact target ultimately served is NYLL M327.009,
`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean:610–733`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its underlying lower and
Herbrand definitions are the published adaptations of M304 and M305 from
`HilbertRamification/RealLowerGroups.lean` and `HerbrandFunction.lean`.
The Herbrand evaluation and inverse facts are reused from
`Herbrand.Function.EvaluationProof` and `HilbertRamification.HerbrandFunction.LawsProof`.
These helpers replace the original M326 quotient-proof route by comparisons
to the already published FLT ring-action theory.

`Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`, particularly its
`Transport` and `Phi` sections, supplies the named generic transport, sum and
floor lemmas. Its p-adic-specific theorems are not applied. The present
comparison uses NYLL's actual arbitrary local-field groups instead of the
`PadicField` interface. FLT's rational phi, psi and upper group, and their
identities, are imported from the published
`Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`
and `...UpperRamificationGroupPsi` modules. The FLT source is pinned at
`6e837e75355538c7f80bab5b956861e86c4eacc2`; its Apache-2.0 notices are retained
under `licenses/Anthropic-FLT/`. NYLL's attribution and notices are retained
under `licenses/NYLL/`. No new axiom or global instance is introduced.
