# The modular character of a group with a compact open subgroup

Module `Langlands.BaseChange.TwistedLocalDescent.ModularCharacter`. Let `H` be a second countable
locally compact group and `μ` a left Haar measure; `modularCharacter` is Mathlib's modular
character.

- `map_mul_right_eq_modularCharacter_smul`: `μ.map (· * q) = Δ(q) • μ` (uniqueness of Haar
  measure in a second countable group, `isMulLeftInvariant_eq_smul`, and
  `modularCharacterFun_eq_haarScalarFactor`).
- `Langlands.ModularCompactAverage.modularCharacter_eq_one_of_mem`: `Δ` is trivial on a compact open subgroup `K` (evaluate the
  previous identity on `K`, whose measure is finite and positive).
- `continuous_modularCharacter`: with a compact open subgroup, `Δ` is locally constant, hence
  continuous.
- `modularCharacter_map_eq`: if `H` has a compact open subgroup and `θ` is a measurable
  endomorphism with `μ.map θ = μ`, then `Δ(θ h) = Δ(h)`.
