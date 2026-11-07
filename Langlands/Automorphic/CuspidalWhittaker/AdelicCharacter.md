# A standard additive character of `𝔸_K / K`

Author: Worker 1709.

This is internal infrastructure for the proof of
`Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement`. It constructs the
standard additive character of the adeles of a number field `K` explicitly and proves what the
Whittaker argument needs. The character follows the classical pattern: the trace at the infinite
places, corrected by a rational number that makes the finite part integral. No source is cited
for these Lean definitions, and their properties are proved directly here. All results are proved, and no
hypothesis is assumed.

## The exponential and the infinite trace

- `unitExp t = Circle.exp (2πt)` is `e(t) = exp(2πit)`. It is additive and continuous, and
  `unitExp t = 1` exactly when `t ∈ ℤ` (`unitExp_eq_one_iff`).
- `mixedTrace` is the `ℝ`-linear map on `mixedEmbedding.mixedSpace K` that sends the lattice
  basis vector `mixedEmbedding (integralBasis K i)` to `Tr_{K/ℚ}(integralBasis K i)`. By
  `mixedTrace_mixedEmbedding` it extends the trace: `mixedTrace (mixedEmbedding x) = Tr x`.
- `infiniteTrace : InfiniteAdeleRing K →+ ℝ` is `mixedTrace` composed with Mathlib's
  `InfiniteAdeleRing.ringEquiv_mixedSpace`. It is continuous, and on `K` it is the trace
  (`infiniteTrace_algebraMap`).
- `exists_int_trace_of_mem`: if `x ∈ K` is integral at every finite place, then `x ∈ 𝒪_K`, so
  `Tr x ∈ ℤ`.

## The global character

The Library lemma `exists_sub_mem_integralFiniteAdeles` writes every finite adele as `r + c`
with `r ∈ K` and `c` integral. `finiteShift a` chooses such an `r`.

- `adelicCharacterFun x = e(Tr_∞(x_∞ − r))` with `r = finiteShift x_f`.
- `adelicCharacterFun_eq` shows that every `r ∈ K` with `x_f − r` integral gives the same
  value. Two such `r` differ by an element of `K` integral at every finite place, and that
  element has integral trace.
- `adelicCharacter : AddChar (Adeles K) Circle` is the resulting character `ψ`. Additivity uses
  `finiteShift x_f + finiteShift y_f` as the shift for `x + y`.
- `adelicCharacter_algebraMap` says `ψ` is trivial on `K`.
- `adelicCharacter_of_integral` says `ψ(x) = e(Tr_∞ x_∞)` when `x_f` is integral.
- `continuous_adelicCharacter`: on the open neighbourhood `x_f + Ô` of `x`, a single shift
  works, so `ψ` is continuous there.

## Local components

- `finiteSingle K v : FiniteCompletion K v →+ FiniteAdeles K` places an element at `v` and
  zeros elsewhere.
- `finiteToAdeles` is the inclusion of the finite adeles with zero infinite component.
- `localCharacter K v = ψ ∘ finiteToAdeles ∘ finiteSingle K v` is the local component
  `χ_v`.
- `localCharacter_eq_one`: `χ_v` is trivial on `v.adicCompletionIntegers K`, because the
  inserted element is an integral finite adele and the shift `0` applies.
- `exists_localCharacter_ne_one`: `χ_v` is nontrivial. Let `b_i` be the integral basis.
  `traceDualBasis` is the `ℚ`-basis dual to `b_i` for the trace form, and
  `exists_dual_denominator` gives a nonzero `N ∈ 𝒪_K` with `N x ∈ 𝒪_K` whenever `Tr(x b) ∈ ℤ`
  for all `b ∈ 𝒪_K`. Choose a nonzero `π ∈ v`, put `t = 1/(Nπ)` at `v`, and take `r ∈ K` with
  `finiteSingle t − r` integral. If `χ_v ≡ 1`, then `Tr(r b) ∈ ℤ` for every `b ∈ 𝒪_K`, so
  `N r ∈ 𝒪_K`. Since `t − r` is integral at `v`, this makes `π⁻¹ = N(t − r) + N r` integral at
  `v`, which contradicts `v(π) < 1`.

## Self-duality of `K`

`exists_eq_algebraMap_of_orthogonal`: if `ψ(a y) = 1` for every `a ∈ K`, then `y ∈ K`. The proof
has three steps.

1. Shift `y` by `finiteShift y_f`, so that `y_f` becomes integral.
2. For `b ∈ 𝒪_K`, `ψ(b y) = e(Tr_∞(b y_∞))`, so all these traces are integers.
   `mixedTracePairing Y = (mixedTrace(b_j Y))_j` is injective: it is a surjective linear map
   between real spaces of equal dimension, with explicit preimages built from the dual basis.
   Hence `y_∞ = δ` for an explicit `δ = Σ m_k · traceDualBasis k ∈ K`
   (`exists_eq_algebraMap_of_infiniteTrace`).
3. The remaining finite adele `w = y_f − δ` is orthogonal to `K`. If `w_p ≠ 0`, take a nonzero
   `d ∈ 𝒪_K` with `d w` integral (Library `exists_integer_mul_mem_adicCompletionIntegers`) and
   a `t_0` with `χ_p(t_0) ≠ 1`. Choose `s ∈ K` with `finiteSingle (t_0/(d w_p)) − s` integral.
   Then `(d s) w − finiteSingle t_0` is integral, so `1 = ψ((d s) w) = χ_p(t_0)`, a
   contradiction (`finiteAdele_eq_zero_of_orthogonal`).

`exists_adelicCharacter_ne_one` says `ψ` is not identically one: at the infinite places,
`x = 1/(2[K : ℚ])` gives `ψ(x) = e(1/2) = −1`. The nonvanishing step in `Columns` uses this.
