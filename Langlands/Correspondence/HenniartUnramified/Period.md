# Torsion numbers, breaks and Swan exponents through inertia types

## Twist algebra

For characters `χ, ψ : G → ℂˣ`:

- `twistCommEquiv`: twisting by `χ` and then `ψ` is equivalent to the other order,
  via the identity map.
- `twistInvEquiv`: twisting by `χ` and then `χ⁻¹` gives back the original
  representation.

`twist_stab_iff` uses these. If the `χ`-twist of `ρ` is equivalent to `ρ'`, then `ρ`
and `ρ'` have the same twist stabilizer: `ψ ⊗ ρ ≅ ρ` exactly when `ψ ⊗ ρ' ≅ ρ'`.

## Weil classes from representatives

`WeilObj F` is the type of continuous irreducible representations of `W_F`.
`weilClassOf F A h` is the class of such an `A` in
`IrreducibleWeilClass F (k + 1)`, given `rank A = k + 1`. Every class arises this way
(`weilClassOf_surjective`). On representatives:

- `weilUnramifiedTwist_weilClassOf`: the published `weilUnramifiedTwist` fixes the
  class exactly when the corresponding twist of `A` is equivalent to `A`.
- `weilClassOf_eq_iff`: two classes are equal exactly when the representatives are
  equivalent.
- `weilOrbit_eq_iff`: two unramified-twist orbit classes are equal exactly when some
  unramified twist of one representative is equivalent to the other. This follows
  from the published `weilOrbitClass_eq_iff`.
- `hasWeilSwan_weilClassOf`: `HasWeilSwan F σ s` holds exactly when
  `s = (k + 1) · lastBreak F A`, by `hasWeilSwan_iff_rank_mul_lastBreak` from
  `HenniartUnramified/Swan`.

## Torsion number equals period

`weilTorsionNumber_eq_period` relates the torsion number of a class to its occurring
types. Suppose an inertia type `B` occurs in `A`, meaning there is a nonzero
intertwiner from the inertia restriction of `A` to `B`. Suppose further that the class
of `B` has minimal period `m + 1` under Frobenius conjugation. Then the published
`weilTorsionNumber` of the class of `A` is `m + 1`.

The proof uses the stage `weilStage F φ hφ m`. By `twist_equiv_typeCoind`, some
unramified twist of `A` is equivalent to `typeCoind`. By `twist_stab_iff` and
`typeCoind_twist_iff`, the twist stabilizer is the set of `(m + 1)`st roots of unity,
whose cardinality is `m + 1` (`Complex.card_rootsOfUnity`).

## Breaks

- `lastBreak_typeCoind`: the last break of `typeCoind` is the break of its type, by
  `typeCoind_trivial_iff` applied to the normal upper groups.
- `lastBreak_twist`: unramified twists do not change the last break, since they are
  trivial on inertia.
- `lastBreak_stage`: for a representation `τ` of the unramified stage
  `W_L`, the last break over `L` equals the break over `F` of its first block
  `τ ∘ κ`. The proof uses `unramifiedStage_mem_upperGroup`, which identifies
  upper groups of nonnegative index along the stage map, and injectivity of `ι`.

These results give the rank, Swan and torsion bookkeeping of Henniart (1988),
Proposition 2.2.
