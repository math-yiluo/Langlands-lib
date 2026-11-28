# The kernel flag nilradical in the range of the commutator map

The module `Langlands.HarmonicAnalysis.UnitConjugation.KernelFlagCommutator` proves, for an
element `x` of a finite-dimensional semisimple algebra `A` over a field `F` of characteristic
zero, that the range of `y ↦ x y - y x` contains the nilradical of the flag of left ideals
`J_k = {v | v x ^ k = 0}` split by orthogonal idempotents. It also constructs such a splitting
inside any subring that contains idempotent generators of all left ideals. All declarations are
in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`.

## The trace form

The module uses the Library's regular trace `Langlands.Algebra.regularTrace F A`,
`a ↦ Tr_F(L_a)` with `L_a(b) = a b` (module `Langlands.Algebra.RegularTrace`), its cyclicity
`Langlands.Algebra.regularTrace_mul_comm` and the bilinear form
`Langlands.Algebra.regularTraceForm F A`, `(a, b) ↦ Tr_F(L_{a b})`.

- `eq_zero_of_forall_regularTrace_mul_eq_zero` (`[CharZero F] [FiniteDimensional F A]
  [IsSemisimpleRing A]`): if `Tr_F(L_{y z}) = 0` for every `z`, then `y = 0`. Proof: the set `I`
  of such `y` is a left ideal (`Tr(L_{a y z}) = Tr(L_{y z a})`). Since `A` is a semisimple
  ring, `I` has a complement `C` as a left ideal; writing `1 = e + f` with `e ∈ I`, `f ∈ C`,
  every `y ∈ I` satisfies `y = y e` (because `y f ∈ I ∩ C = 0`), so `e` is idempotent and
  generates `I`. Then `L_e` is an idempotent endomorphism with `Tr(L_e) = Tr(L_{e · 1}) = 0`;
  in characteristic zero Mathlib's `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero` gives
  `L_e = 0`, so `e = 0` and `I = 0`.
- `regularTraceForm_nondegenerate_of_isSemisimpleRing`: hence `regularTraceForm F A` is
  nondegenerate (both separations follow by cyclicity). The Library's
  `Langlands.Algebra.regularTraceForm_nondegenerate` is the case of a simple algebra.
- `exists_commutator_eq_of_regularTrace` (same hypotheses): if `Tr_F(L_{w z}) = 0` for every
  `z` with `x z = z x`, then `w = x y - y x` for some `y`. Proof: the range of
  `D = (y ↦ x y - y x)` lies in the trace-orthogonal of `ker D` (the centralizer of `x`), by
  `Tr(L_{z (x y - y x)}) = Tr(L_{x z y}) - Tr(L_{z y x}) = 0` for `z` in the centralizer. By
  rank–nullity and Mathlib's `LinearMap.BilinForm.finrank_orthogonal` for the nondegenerate
  trace form, both spaces have dimension `dim A - dim ker D`, so they are equal.

## Kernel flags

- `mul_sum_range_of_lt`, `mul_sum_range_of_le`, `sum_range_mul_of_lt`, `sum_range_mul_of_le`:
  for orthogonal idempotents `e i` (`e i * e i = e i`, `e i * e j = 0` for `i ≠ j`),
  `e i * (e 0 + ⋯ + e (k - 1))` and `(e 0 + ⋯ + e (k - 1)) * e i` equal `e i` if `i < k` and `0`
  otherwise (the `_lt` forms need idempotence, the `_le` forms only orthogonality).
- `IsKernelFlagSplitting x m e` (a structure, for `x : A`, `m : ℕ`, `e : ℕ → A` in any ring `A`):
  the `e i` are idempotent and pairwise orthogonal, `e 0 + ⋯ + e (m - 1) = 1`, and for every
  `k` and `v`, `v * x ^ k = 0 ↔ v * (e 0 + ⋯ + e (k - 1)) = v`; that is, the left ideal
  `J_k = {v | v x ^ k = 0}` is `A (e 0 + ⋯ + e (k - 1))`.
- `IsKernelFlagSplitting.mul_pow_succ_eq_zero`: `e i * x ^ (i + 1) = 0`.
- `IsKernelFlagSplitting.mul_mul_eq_zero_of_commute`: if `x z = z x` and `j < i`, then
  `e j * z * e i = 0` (the centralizer preserves the flag: `(e j z) x ^ (j+1) = e j x ^ (j+1) z = 0`).
- `IsKernelFlagSplitting.mul_mul_eq_zero_self`: `e i * x * e j = 0` for `i ≤ j` (since
  `e i x ∈ J_i`).
- `IsKernelFlagSplitting.regularTrace_eq_sum`: `Tr(L_W) = ∑_{i < m} Tr(L_{e i W e i})`, by
  cyclicity.
- `IsKernelFlagSplitting.exists_commutator_eq` (`[CharZero F] [FiniteDimensional F A]
  [IsSemisimpleRing A]`): every `w` with `e i * w * e j = 0` for all `i ≤ j` is `x y - y x` for
  some `y`. Proof: for `z` in the centralizer, `e i (w z) e i = ∑_j (e i w e j)(e j z e i)`, where
  the first factor vanishes for `j ≥ i` and the second for `j < i`; so `Tr(L_{w z}) = 0` by
  `regularTrace_eq_sum`, and `exists_commutator_eq_of_regularTrace` applies.

## Splitting the flag in a subring

- `mem_span_singleton_iff_mul_eq`: for an idempotent `f`, `v ∈ A f ↔ v f = v`.
- `leftAnnihilatorPow x k`: the left ideal `{v | v * x ^ k = 0}`, with `mem_leftAnnihilatorPow`.
- `exists_isKernelFlagSplitting`: let `R` be a subring of a ring `B` such that every left ideal
  of `B` is `B e` for an idempotent `e ∈ R`, and let `x ^ m = 0`. Then there is `e : ℕ → B` with
  values in `R` and `IsKernelFlagSplitting x m e`. Proof: choose idempotent generators
  `f k ∈ R` of `J_k`; define `p 0 = 0` and `p (k + 1) = f (k + 1) + p k - f (k + 1) p k`. By
  induction `p k ∈ R` is an idempotent generator of `J_k` (using `p k f (k + 1) = p k`, since
  `J_k ⊆ J_{k+1}`), and `p k p l = p l p k = p k` for `k ≤ l`. Then `e i = p (i + 1) - p i`
  are orthogonal idempotents of `R` with `e 0 + ⋯ + e (k - 1) = p k`, and `p m = 1` because
  `J_m = B`.

## Provenance

This is the associative-algebra form of Harish-Chandra's Lemma 13.2 and Corollary 13.3
(*Admissible invariant distributions on reductive p-adic groups*, notes by DeBacker and Sally,
1999, source ID `harish-chandra-1999-admissible-invariant-distributions`, Part II, §13.1,
printed p. 64): for a nilpotent `X₀` and the parabolic attached to it, the nilradical lies in
`[X₀, g]`. Harish-Chandra obtains this from the representation theory of a Jacobson–Morozov
triple; here the parabolic is the stabilizer of the kernel flag of `X₀` and the inclusion comes
from the duality between the range of `ad x` and the centralizer under the nondegenerate trace
form, so no `sl₂`-triple is used. The kernel-flag argument and the construction of compatible
idempotents are internal to the Library.
