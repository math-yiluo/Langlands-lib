# Existence of levels

Module `Langlands.BaseChange.TwistedVanDijk.LevelExistence`. It proves that every test function
on `GL_n(E)` has a level in the sense of `Langlands.BaseChange.TwistedVanDijk.Operator`.

## Contents

- `integerRingEquiv σ` is the restriction of the `F`-automorphism `σ` of `E` to the valuation
  ring `𝒪_E`, a ring automorphism (`algEquiv_mem_integer_iff`).
- `integerRingEquiv_mem_maximalIdeal_pow`: it preserves every power `𝔭^a` of the maximal ideal
  (a ring automorphism of a local ring maps the maximal ideal into itself, and `Ideal.map`
  commutes with powers).
- `entrywiseAut_mem_principalLevelSubgroup`: the principal congruence subgroups
  `Conductor.principalLevelSubgroup E n a = {g : g ≡ 1, g⁻¹ ≡ 1 mod 𝔭^a}` of
  `GL_{n+1}(𝒪_E)` are stable under the entrywise action of `σ`: the entries of `g − 1` and of
  `g⁻¹ − 1` stay in `𝔭^a`, and `σ` fixes the entries of the identity matrix.
- `exists_level σ φ`: every test function `φ` on `GL_n(E)` has a level.

## Proof of `exists_level`

For `n = 0` the group is trivial and the whole group is a level. For rank `n + 1`, the
Library's `Hecke.TestFunction.commonCompactOpenBiInvariance` gives a compact open subgroup
`K''` under which `φ` is invariant on both sides, and `Conductor.principalLevelCofinal` a
principal congruence subgroup contained in `K''`. That subgroup is the level: it is open, it
lies in `GL_{n+1}(𝒪_E)` (the congruence subgroup of level `0`,
`Conductor.principalLevelSubgroup_zero`, and antitonicity), and it is stable under `σ` and under
`σ⁻¹` by `entrywiseAut_mem_principalLevelSubgroup`.
