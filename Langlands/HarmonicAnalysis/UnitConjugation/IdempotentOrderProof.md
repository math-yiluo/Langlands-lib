# A compact open order containing idempotent generators of all left ideals: proof

The module `Langlands.HarmonicAnalysis.UnitConjugation.IdempotentOrderProof` proves
`Langlands.HarmonicAnalysis.UnitConjugation.SemisimpleIdempotentOrderStatement.{u, v}`
(module `IdempotentOrderStatement`) as the theorem
`Langlands.HarmonicAnalysis.UnitConjugation.semisimpleIdempotentOrder`: for every nonarchimedean
local field `F` (any characteristic) and every finite-dimensional semisimple `F`-algebra `A` with
its module topology, there is a compact open subring `R` of `A`, stable under the integers of `F`,
such that every left ideal `J` of `A` is `A e` for an idempotent `e ∈ R`.

## Proof

1. **Wedderburn–Artin.** Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`
   gives an `F`-algebra isomorphism `φ : A ≃ₐ[F] ∏_{i < n} M_{d_i}(D_i)` with finite-dimensional
   division algebras `D_i` over `F`. Each `D_i` is given its module topology.
2. **The order.** `R` is the subring of `x ∈ A` all of whose matrix entries `φ(x)_i(a, b)` lie in
   the integer ring `divisionIntegers (D i)` (module `DivisionIntegers`); it is a subring because
   `φ` is a ring isomorphism and matrix multiplication only adds and multiplies entries.
3. **Topology.** Each coordinate `x ↦ φ(x)_i(a, b)` is `F`-linear, hence continuous, so `R`, a
   finite intersection of preimages of the open sets `divisionIntegers (D i)`
   (`isOpen_divisionIntegers`), is open. `R` is the image of the compact product of the
   `divisionIntegers (D i)` (`isCompact_divisionIntegers`) under the linear, hence continuous,
   map `M ↦ φ⁻¹(M)` from `∏_i (Fin d_i → Fin d_i → D_i)` with its module topology, so `R` is
   compact. Stability under the integers of `F` follows from `smul_mem_divisionIntegers`.
4. **Idempotents.** For a left ideal `J` of `A`, the set `J' = {y | φ⁻¹(y) ∈ J}` is a left ideal
   of the product. By `exists_idempotent_pi` together with `exists_integral_idempotent_matrix`
   (module `MatrixIdempotentOrder`) for the valuations `divisionNormValuation (D i)`, it has an
   idempotent generator `e'` with integral entries. Then `e = φ⁻¹(e')` lies in `R`, is
   idempotent, and `x ∈ J ↔ φ(x) e' = φ(x) ↔ x e = x ↔ x ∈ A e`
   (`mem_span_singleton_iff_mul_eq`, module `KernelFlagCommutator`).

## Source

André Weil, *Basic Number Theory*, second edition, Springer, 1973, source ID
`weil-1973-basic-number-theory`: Chapter I, §4, Theorem 6, printed pp. 12–13 (the maximal compact
subring of a `p`-field) and Chapter II, §2, Theorem 1, printed p. 29 (lattice bases adapted to a
flag), combined with the Wedderburn–Artin theorem, as described in the Markdown of
`IdempotentOrderStatement`. The implementation follows that outline, with the integral Gaussian
elimination of `MatrixIdempotentOrder` in place of Weil's Theorem 1.
