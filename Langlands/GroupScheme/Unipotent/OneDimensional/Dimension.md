# Consequences of Krull dimension at most one for a finitely generated domain

Worker 716. Standard commutative-algebra facts, used in the proof of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement` to supply
the finiteness and dependence hypotheses of the algebraic core (`Core`). No
registered source was used. The proofs are the implemented ones. Throughout,
`B` is a domain that is a finitely generated algebra over a field `k`, in the
same universe as `k`.

## Results

- `finite_quotient_span_singleton`: if `ringKrullDim B ≤ 1` and `z ≠ 0`, then
  `B/(z)` is a finite-dimensional `k`-vector space.
- `trdeg_le_one`: if `ringKrullDim B ≤ 1`, then `Algebra.trdeg k B ≤ 1`.
- `exists_ev2_eq_zero`: in any `k`-algebra of transcendence degree at most one
  (no domain or finiteness hypothesis), two elements `y, t` satisfy
  `c(y, t) = 0` for some nonzero `c : k[X][X]`.

## Implemented arguments

**Finite quotients.** `B` is noetherian, and Mathlib's
`ringKrullDim_quotient_succ_le_of_nonZeroDivisor` gives
`dim B/(z) + 1 ≤ dim B ≤ 1`, since `z` is a nonzerodivisor in the domain `B`.
So `B/(z)` has dimension zero. A noetherian ring of dimension zero is
Artinian (`isArtinianRing_iff_krullDimLE_zero`), and an Artinian finitely
generated `k`-algebra is finite-dimensional (`Module.finite_of_isArtinianRing`).

**Transcendence degree.** Noether normalization in the form
`Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType`
(Library, `AnthropicFLT`) gives an algebraically independent family `z` of
size `d`. Every element of `B` becomes integral over `k[z]` after
multiplication by a power of some `r ≠ 0`. The Library lemma
`Ideal.natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent`,
applied to the zero ideal (a minimal prime of the domain `B`), gives
`d ≤ dim B ≤ 1`. Since `r` is a nonzero element of `k`, `B` is integral, hence
algebraic, over `k[z]`. Then `Algebra.IsAlgebraic.trdeg_le_cardinalMk` bounds
the transcendence degree by `d ≤ 1`.

**Dependence.** If no nonzero `c` vanished at `(y, t)`, the evaluation
`ev2 y t : k[X][X] → B` would be injective. Then
`trdeg k k[X][X] ≤ trdeg k B ≤ 1` (`trdeg_le_of_injective`). But
`trdeg_add_le` and `Polynomial.trdeg_of_isDomain` give
`2 = 1 + 1 ≤ trdeg k k[X][X]`, a contradiction.
