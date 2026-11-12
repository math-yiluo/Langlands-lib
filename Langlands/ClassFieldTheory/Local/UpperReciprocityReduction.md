# Finite upper reciprocity: elementary reduction

The construction `finiteUpperReciprocityRealEquiv` retains universe `u` and every
quantifier of the published five-clause `FiniteUpperReciprocityTheorems`.
Its forward map extracts `FiniteReciprocityRealUnitImages`; its inverse is the
implemented elementary reduction from that clause to all five clauses.
Proof irrelevance supplies both inverse laws. The arithmetic real image
hypothesis remains an unproved input; the file does not supply an unconditional
proof of the target.

The integer formula is specialization at a natural number, whose natural ceiling
is itself. For the unconditional norm-level clause the proof chooses the geometric
profinite map supplied by `profiniteReciprocityExistenceUniqueness`. Its finite
kernel is the actual norm subgroup. The image of a subgroup is trivial exactly
when that subgroup is contained in the kernel, giving the required equivalence
without quantifying a candidate map in the conclusion.

The conductor comparison uses the published equivalence between a conductor bound
and containment of `unitFiltration` in the kernel. Under the real image equality,
a finite character kills the upper group exactly when its composite kills this
unit level. A successor conductor is larger than `n` exactly when the character
is nontrivial at level `n`; any real `v > n` has natural ceiling at least `n + 1`.
Conversely, triviality at every later real level includes `n + 1`, which bounds
the conductor above and hence gives the exact successor value. This includes
`n = 0`, so the tame endpoint is retained.

The provenance is an internal logical consequence of the published statements and
the unconditional existence and conductor comparison theorems. The conductor
argument follows the same elementary ceiling calculation as the Library's
`AbsoluteReciprocityConductorProof`, applied to finite characters.
