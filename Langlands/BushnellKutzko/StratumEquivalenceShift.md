# Lattice shifts of a normalizing field

Helper module for the proof of `Langlands.BushnellKutzko.StratumEquivalenceStatement`
(Bushnell–Kutzko 1993, (2.1.4)(iii), printed p. 50). The setting is a field `E` acting on the
`F`-space `V` compatibly with `F`, with `E^×` normalizing an `𝔬_F`-lattice chain
`𝓛 = (L_i)` (hypothesis `hE`). The module is internal to that proof; BK93 uses the same facts
implicitly (the valuation of `E` read off from the chain).

**Exact depth and shift (any base field).**
- `ExactDepth 𝓛 v i`: `v ∈ L_i` and `v ∉ L_{i+1}`. `ExactDepth.le` and `ExactDepth.unique`:
  the exact depth is the largest `j` with `v ∈ L_j`, hence unique.
- `shift 𝓛 hE a`: for `a ≠ 0`, the integer `d` given by the published
  `LatticeChain.fieldShift` (so `a L_i = L_{i+d}`); by convention `shift 0 = 0`.
- `smul_mem_shift_iff`: for `a ≠ 0`, `a v ∈ L_{i + shift a}` iff `v ∈ L_i` (published
  `mem_lattice_fieldShift`). Consequences, also for `a ≠ 0`: `ExactDepth.smul`
  (multiplication by `a` adds `shift a` to the exact depth) and `smul_mem_of_shift_le`
  (`j ≤ i + shift a` and `v ∈ L_i` give `a v ∈ L_j`). The hypothesis `a ≠ 0` is needed:
  for `a = 0` the left side always holds, and `0 · v = 0` has no exact depth.
- `shift_mul`, `shift_one`, `shift_inv`, `shift_pow`: `shift` is a homomorphism on `E^×`
  (since `fieldShift` is a group homomorphism); each lemma assumes its arguments nonzero.
- `shift_eq_of`: if `a ≠ 0` and `a v ∈ L_d ⟺ v ∈ L_0` for all `v`, then `shift a = d`
  (injectivity of the chain).

**Local-field part** (`F` a nonarchimedean local field, `𝔬 = 𝔬_E`).
- `isScalarTower_integer`: the instance `IsScalarTower 𝒪[F] E V`.
- `shift_nonneg_of_mem` (published `fieldShift_nonneg_of_integral` for nonzero elements; the
  convention `shift 0 = 0` covers `0`) and `shift_unit`: integral elements have shift `≥ 0`,
  units of `𝔬_E` have shift `0`.
From here on `[E : F] < ∞` is assumed (so `𝔬_E` is a discrete valuation ring) and `ϖ` is a
uniformizer of `𝔬_E`.
- `exists_unit_pow`: for `[E : F] < ∞` and a uniformizer `ϖ`, every `a ≠ 0` satisfies
  `a = u ϖ^n` or `a⁻¹ = u ϖ^n` with `u ∈ 𝔬_E^×` (`𝔬_E` is a discrete valuation ring with
  fraction field `E`).
- `shift_unit_mul_pow`: `shift(u ϖ^n) = n · shift ϖ`.
- `ramificationIndex_mul_shift`: `e(E|F) · shift ϖ = e(𝓛)`. Indeed a uniformizer `π` of `F`
  factors as `u ϖ^{e(E|F)}` (published `baseUniformizer_factorization`), and `π` shifts the
  chain by its period (`uniformizer_lattice_mem_iff`), so `shift_eq_of` applies.
- `shift_uniformizer_pos`: `e' := shift ϖ > 0` (it is `≥ 0`, and `e' = 0` would make the
  positive period zero).
- `shift_uniformizer_dvd`: the shift of every nonzero `a` is a multiple of `e'`.
- `mem_integers_iff`: a nonzero `a ∈ E` lies in `𝔬_E` iff `shift a ≥ 0` (if `a⁻¹ = u ϖ^n`
  with `n ≥ 1`, the shift of `a` is `-n e' < 0`).
- `mem_maximalIdeal_iff`: a nonzero `x ∈ 𝔬_E` lies in `𝔭_E` iff `shift x ≥ 1` (write
  `x = u ϖ^n`; `x` is a nonunit iff `n ≥ 1`).

In short, on `E^×` we have `shift = e' · v_E` with `e' > 0` and `e(E|F) · e' = e(𝓛)`. The
convention `shift 0 = 0` does not follow this pattern: `0 ∈ 𝔭_E` but `shift 0 < 1`. This is
why `mem_integers_iff` and `mem_maximalIdeal_iff` assume a nonzero element.
