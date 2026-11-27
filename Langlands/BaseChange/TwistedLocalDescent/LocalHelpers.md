# Group-theoretic inputs for the local mass identity over a local field

Module `Langlands.BaseChange.TwistedLocalDescent.LocalHelpers`.

- `eq_one_of_mem_compact`: a continuous homomorphism to `ℝ≥0` is trivial on a compact subgroup
  (otherwise its powers would be unbounded on it).
- `isMulRightInvariant_generalLinear`: every Haar measure on `GL_n(E)`, `E` a nonarchimedean local
  field, is right invariant. Its modular character is trivial on scalars (they are central) and
  hence everywhere by the Library's `RankinSelberg.GeneralLinearUnimodularity.character_eq_one`.
- `parabolicHalfModulusNNReal B`: `p ↦ δ_P(p)^{1/2}` on the standard parabolic, i.e. the square
  root of the Library's `leviModulus` of the Levi part, as a homomorphism to `ℝ≥0`; continuous
  (`continuous_parabolicHalfModulusNNReal`: `leviModulus` has open kernel).
- `parabolicContinuousAut B σ`: the entrywise action of `σ` on `P` as a topological group
  automorphism; `parabolicHalfModulusNNReal_aut` (`δ_P` is `σ`-invariant, `leviModulus_leviAut`)
  and `map_parabolicContinuousAut_eq` (it preserves every Haar measure on `P`: it preserves the
  compact open set `P ∩ GL_n(𝒪_E)`).
