# Actual supercuspidal strata

Worker 30 restricts the class-invariant predicates to Worker 23's genuine
`GeneralLinear.SupercuspidalClass` through its actual injective map into
`SmoothDualClass`. The underlying objects are irreducible admissible smooth
complex representations whose actual Jacquet coinvariants vanish for every
proper ordered block parabolic and every conjugate radical. The imported
construction proves its isomorphism invariance. This module does not replace
that condition by a supplied predicate or assume a local correspondence.

`HasCentralCharacter` prescribes scalar action of a character of the full
center, and `HasFixedVector` prescribes nonzero invariants of an actual
subgroup. Their evaluation on an actual representative's `isoClass` is
proved definitionally. `centralFixedStratum` is their intersection in the
genuine supercuspidal class space. Its carrier universe remains explicit.

For positive rank `n + 1` and a specified valuation, `firstFixedLevel`
restricts the total class-level function from the companion `ClassLevel`.
It still permits infinity. `centralLevelStratum` fixes center action and
bounds this value by a natural number. `centralLevelStratum_eq` proves that
this is exactly the corresponding fixed-space stratum for the published
last-row subgroup at the bound, using monotonicity and minimality already
proved in `ClassLevel`.

The internal definitions provide the actual sets needed for
Bernstein--Zelevinsky (1976), Corollary 4.15, page 41, together with the
fixed-level convention of JPSS (1981), Section 5.1, page 211.
Source IDs and retained hashes are
`bernstein-zelevinsky-1976-representations-gln`,
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`,
and `jpss-1981-conductor`,
`986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
The relevant original passages are recorded in the companion construction
documentation and the task's source audit.

No finiteness, supercuspidal genericity, finite-level existence or equality
with an epsilon exponent is a field or assumption of these constructions.
The latter representation-theoretic assertions remain separate obligations.
The local finiteness statements are given in the companion statement module.
The larger field/topology domain of these definitions asserts no
classification theorem there.

The imports `Langlands.Representation.Classification.Supercuspidal` and
`Langlands.Representation.Conductor.ClassLevel`, including
`Category.ClassInvariants`, are independently published in Library commit
`fc2adf231e015f979345e06d0d80283856c43c7f`. Their checked Lean SHA256 values are:

- `Classification.Supercuspidal`:
  `c13ba8ffad11de2c3b2861c4afc385be2663b3e76963d5e89807ba92c753f9f1`.
- `Conductor.ClassLevel`:
  `20a57100f00c2b844447acd1f62fcf6a1c28c05df4ee2eeb9401fa3dcc2697f1`.
- `Category.ClassInvariants`:
  `4f65d38d130993b4310a63e60060651c60bf8178ab60000c37e0e237f7991a82`.

The complete constructions were read and their published sources agree
with the workspace. Their authors retain their authorship; these imports
are not republished as part of this module. A character on the field's
unit group must be related explicitly to the character on the actual
center used here. No such identification is silently imposed.
