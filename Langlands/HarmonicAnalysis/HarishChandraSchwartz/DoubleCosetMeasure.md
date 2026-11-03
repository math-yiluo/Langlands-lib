# Measures of double cosets (Waldspurger I.1 (5))

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published module `Translations`,
from which it uses `conjSubgroup g H = {x | g^{-1} x g ∈ H} = g H g^{-1}` and
`mem_conjSubgroup`, and Mathlib (`MeasureTheory.Group.Measure`, `GroupTheory.DoubleCoset`,
`GroupTheory.Index`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. I.1 (5) and its proof, printed pp. 241–242 (PDF pp. 7–8):

- (5): there are `C_1, C_2 > 0` with `C_1 δ_0(m)^{-1} ≤ mes(K m K) ≤ C_2 δ_0(m)^{-1}` for all
  `m ∈ M̄_0^+`, where `δ_0 = δ_{P_0}`.
- Proof: for a compact open `H ⊆ K` with the factorization of the preceding proof,
  `mes(HmH) ≤ mes(KmK) ≤ [K : H]^2 mes(HmH)`;
  `mes(HmH) = mes(H) [H : mHm^{-1} ∩ H] = mes(H) c_{U_0}(m) c_{M_0}(m) c_{Ū_0}(m)` with
  `c_V(m) = [H ∩ V : m(H ∩ V)m^{-1} ∩ H]`; and
  `c_{U_0}(m) = mes(m^{-1}(H ∩ U_0)m) mes(H ∩ U_0)^{-1} c'_{U_0}(m) = δ_0(m)^{-1} c'_{U_0}(m)`
  with `c'_{U_0}(m) = [H ∩ U_0 : H ∩ m^{-1}(H ∩ U_0)m]`; the integers `c'_{U_0}(m)`,
  `c_{M_0}(m)`, `c_{Ū_0}(m)` are bounded on `M̄_0^+`.

## Scope: abstract data and explicit hypotheses

`G` is a group with a measurable multiplication and a left invariant measure `μ` (no Haar
property and no finiteness is assumed). Subgroups are arbitrary; measurability and
finiteness of indices are explicit hypotheses of each result. Indices are Mathlib's
`Subgroup.relIndex` (`Z.relIndex Y = [Y : Z ∩ Y]`), which is `0` when the index is infinite,
so the `≠ 0` hypotheses state finiteness.
The modulus result is stated for a group `U` with a left invariant measure `ν` and an
automorphism `φ`; the scaling `ν(φ(S)) = c ν(S)` is an explicit hypothesis. For
Waldspurger's `U_0` and `φ = (u ↦ m u m^{-1})` it is the modulus relation of `δ_0`
(the published `IsConjModulus`, which is not used or proved here).

## Definitions

- `doubleCosetIndex H g = (conjSubgroup g H).relIndex H = [H : H ∩ g H g^{-1}]`, the number
  of left cosets of `H` in `H g H` (Waldspurger's `[H : mHm^{-1} ∩ H]`).

## Results

Group theory:

- `conjSubgroup_mono`: `H ≤ K` implies `g H g^{-1} ≤ g K g^{-1}`.
- `pairwise_disjoint_smul_of_injective`: distinct left translates `a_i Z` of a subgroup
  `Z` are pairwise disjoint.
- `translate_smul_eq_iff`: for `h_1, h_2 ∈ H`, `(h_1 g)H = (h_2 g)H` iff `h_1` and `h_2` have the
  same class in `H / (H ∩ g H g^{-1})`.
- `doubleCoset_eq_iUnion`: `H g H = ⋃_q (q g) H`, over representatives `q` of
  `H / (H ∩ g H g^{-1})`.
- `coe_eq_iUnion_smul` (for `Z ≤ Y`): `Y = ⋃_q q Z`, over representatives of `Y / Z`;
  `leftCoset_eq_iff_mk`: `y_1 Z = y_2 Z` iff `y_1`, `y_2` have the same class in `Y / Z`.
- `doubleCoset_mono`: `H ≤ K` implies `H g H ⊆ K g K`.
- `doubleCosetIndex_le`: for `H ≤ K` with `[H : H ∩ g H g^{-1}]` and `[K : H]` finite,
  `[K : K ∩ g K g^{-1}]` is finite and at most `[H : H ∩ g H g^{-1}] [K : H]`.

Measures (for `μ` left invariant and `G` with measurable multiplication):

- `measure_iUnion_smul`: for a measurable subgroup `Z` and a finite family `a` whose
  translates `a_i Z` are pairwise distinct, `μ(⋃ a_i Z) = (number of indices) μ(Z)`.
- `measure_eq_relIndex_mul`: for measurable `Z ≤ Y` with `[Y : Z]` finite,
  `μ(Y) = [Y : Z] μ(Z)`.
- `measure_doubleCoset`: for measurable `H` with `[H : H ∩ g H g^{-1}]` finite,
  `μ(H g H) = [H : H ∩ g H g^{-1}] μ(H)` (Waldspurger's `mes(HmH) = mes(H)[H : mHm^{-1} ∩ H]`).
- `measure_doubleCoset_bounds`: for measurable `H ≤ K` with `[K : H]` and
  `[H : H ∩ g H g^{-1}]` finite,
  `[H : H ∩ g H g^{-1}] μ(H) ≤ μ(K g K) ≤ [H : H ∩ g H g^{-1}] [K : H] μ(K)`.
- `measure_doubleCoset_le_of_doubleCosetIndex` (I.1 (5) for abstract data): for measurable
  `H ≤ K` with `[K : H]` finite, a set `T ⊆ G`, `e : G → ℝ≥0∞` and constants `c_1, c_2`, if
  for all `m ∈ T` the index `[H : H ∩ m H m^{-1}]` is finite (`hfin`) and
  `c_1 e(m) ≤ [H : H ∩ m H m^{-1}] ≤ c_2 e(m)` (`hlow`, `hup`), then
  `c_1 μ(H) e(m) ≤ μ(K m K) ≤ c_2 [K : H] μ(K) e(m)` for `m ∈ T`. For Waldspurger's data
  `e = δ_0^{-1}` and `T = M̄_0^+`.
- `relIndex_mul_modulus`: for an automorphism `φ` of `U` with `ν(φ(S)) = c ν(S)` for all
  measurable `S` (`hφ`), a measurable subgroup `Y` with `0 < ν(Y) < ∞` (`hY`, `hY0`,
  `hYtop`), and a measurable subgroup `Z` of `Y` and of `φ(Y)` (`hZY`, `hZφY`, `hZ`) of finite
  index in both (`h₁`, `h₂`): `[Y : Z] c = [φ(Y) : Z]`. With `φ = (u ↦ m u m^{-1})`,
  `c = δ_0(m)`, `Y = H ∩ U_0` and `Z = Y ∩ m Y m^{-1}`, the left index is
  `c_{U_0}(m)` and the right one is `c'_{U_0}(m)` after conjugation by `m^{-1}`, which gives
  Waldspurger's `c_{U_0}(m) = δ_0(m)^{-1} c'_{U_0}(m)`.

## Proof notes

A double coset `H g H` is the union of the left cosets `(h g) H`, `h ∈ H` (Mathlib's
`DoubleCoset.doubleCoset_union_leftCoset`), and two of them agree exactly when the
`h`'s agree modulo `H ∩ g H g^{-1}`; distinct left cosets are disjoint and each has measure
`μ(H)` by left invariance, so the measure is the number of classes times `μ(H)`. The upper
comparison differs from Waldspurger's route through `[K : H]^2` and right translations: it
uses `μ(K g K) = [K : K ∩ g K g^{-1}] μ(K)` and the index inequality
`[K : K ∩ g K g^{-1}] ≤ [K : H ∩ g H g^{-1}] = [H : H ∩ g H g^{-1}] [K : H]`, which needs no
right invariance. The modulus identity compares
`ν(Y) = [Y : Z] ν(Z)` and `c ν(Y) = ν(φ(Y)) = [φ(Y) : Z] ν(Z)` and cancels `ν(Z)`, which is
nonzero and finite because `ν(Y)` is.

## Open obligations

For Waldspurger's data: the existence of `H` with the factorization
`H = (H ∩ U_0)(H ∩ M_0)(H ∩ Ū_0)`, the factorization
`[H : mHm^{-1} ∩ H] = c_{U_0}(m) c_{M_0}(m) c_{Ū_0}(m)`, the boundedness of
`c'_{U_0}`, `c_{M_0}`, `c_{Ū_0}` on `M̄_0^+` (together these give the hypotheses `hlow` and
`hup` with `e = δ_0^{-1}`), the Haar measures and the modulus relation for `δ_0` are not
proved here.
