# Residue degree from `𝔅 + 𝔓`

Helper module for the proof of `Langlands.BushnellKutzko.StratumEquivalenceStatement`,
covering the residue-degree half of Bushnell–Kutzko 1993, (2.1.4)(iii), printed p. 50. The
setting is that of `StratumEquivalenceResidue`: a finite field extension `E/F` acting on `V`
with `E^×` normalizing the `𝔬_F`-lattice chain `𝓛 = (L_i)`, `𝔄 = 𝔓^0`, and
`𝔅_E = fieldOrder 𝓛 E = 𝔄 ∩ End_E(V)`. The published residue degree
`subfieldResidueDegree F E` is the `𝔬_F`-length of `𝔬_E/𝔭_E`.

**Definitions (depending only on `𝓛` and an `𝔬_F`-submodule `M` of `End_F(V)`).**
- `residueCommutant 𝓛 M = Z(M) = {x ∈ 𝔄 : (x m - m x) L_0 ⊆ L_1 for all m ∈ M}`.
- `layerKernel 𝓛 = K = {x : x L_0 ⊆ L_1}`.
- `residueQuotient 𝓛 M = Z(M)/(Z(M) ∩ K)`, an `𝔬_F`-module.

**Lemmas.**
- `apply_mem_of_mem_endFiltration_zero`: elements of `𝔄` preserve each `L_i`.
- `smul_mem_of_shift_nonneg`: elements of `E` with nonnegative shift preserve each `L_i`.
- `subfieldEmbedding_mem_residueCommutant`: for `a ∈ 𝔬_E`, the action of `a` lies in
  `Z(𝔅_E + 𝔓)`. It lies in `𝔄` since its shift is `≥ 0`; for `m = b + p` with `b ∈ 𝔅_E`,
  `p ∈ 𝔓`, `a` commutes with `b`, and `(a p - p a) L_0 ⊆ L_1`.
- `integerMap 𝓛 hE : 𝔬_E →ₗ[𝔬_F] Z(𝔅_E + 𝔓)`, the action map.

**Main results** (`F` a nonarchimedean local field, `[E : F] < ∞`, `dim_F V < ∞`).
- `integerMap_mem_layerKernel_iff`: the action of `a ∈ 𝔬_E` lies in `K` iff `a ∈ 𝔭_E`.
  For `a = 0` both sides hold: the zero map lies in `K` and `0 ∈ 𝔭_E`. (The shift
  criterion below does not apply to `a = 0`, since `shift 0 = 0`.) For `a ≠ 0`,
  `mem_maximalIdeal_iff` of `StratumEquivalenceShift` reduces `a ∈ 𝔭_E` to `shift a ≥ 1`.
  If `a L_0 ⊆ L_1`, apply `a` to a vector `u` of exact depth `0`
  (`exists_basis_depth_zero`): `a u` has exact depth `shift a` (`ExactDepth.smul`, using
  `a ≠ 0`) and lies in `L_1`, so `shift a ≥ 1`. Conversely `shift a ≥ 1` gives
  `a L_0 ⊆ L_1` (`smul_mem_of_shift_le`).
- `exists_integer_sub_mem_layerKernel`: every `x ∈ Z(𝔅_E + 𝔓)` is congruent modulo `K` to
  the action of some `a ∈ 𝔬_E`. Take a splitting basis `w` and `u = c w_k` of exact depth `0`
  (so `c ≠ 0`). Put `t = w_k^*(x u)` and `a = t c⁻¹`, so `a u = t w_k`. If `a = 0`, then
  `a ∈ 𝔬_E` trivially. If `a ≠ 0`: since `x u ∈ L_0`, the splitting property gives
  `a u = t w_k ∈ L_0`, and `a u` has exact depth `shift a`, hence `shift a ≥ 0`, i.e.
  `a ∈ 𝔬_E` (`mem_integers_iff`).
  The rank-one map `p : v ↦ w_k^*(v) c⁻¹ u` lies in `𝔅_E` (`rankOne_mem_fieldOrder`) and
  `(x p - p x) u = x u - a u`, so `x u - a u ∈ L_1`. For any `v ∈ L_0` the rank-one map
  `m_v : y ↦ w_k^*(y) c⁻¹ v` lies in `𝔅_E` and sends `u` to `v`. Hence
  `x v - a v = (x m_v - m_v x) u + m_v (x u - a u) ∈ L_1`, since `m_v` commutes with `a` and
  preserves `L_1`.
- `length_residueRing_eq`: `𝔬_E → Z(𝔅_E + 𝔓)/(Z ∩ K)` is surjective with kernel `𝔭_E`, so
  `𝔬_E/𝔭_E ≅ residueQuotient 𝓛 (𝔅_E + 𝔓)` as `𝔬_F`-modules, and the lengths agree.
- `residueDegree_eq_of_sup_eq`: two normalizing fields `E`, `E'` with the same `𝔅 + 𝔓` have
  the same residue degree, since both residue rings have the length of the same module.

The quotient `Z(M)/(Z(M) ∩ K)` is the commutant of `M` acting on `L_0/L_1`, made concrete
without forming that quotient. BK93 instead derives (2.1.4)(iii) from the Wedderburn
structure of `𝔅/𝔔`; this module uses the direct description above.
