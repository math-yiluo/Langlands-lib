# A compact open order containing idempotent generators of all left ideals

The module `Langlands.HarmonicAnalysis.UnitConjugation.IdempotentOrderStatement` states, as the
proposition `Langlands.HarmonicAnalysis.UnitConjugation.SemisimpleIdempotentOrderStatement.{u, v}`,
that a finite-dimensional semisimple algebra over a nonarchimedean local field has a compact
open order in which every left ideal has an idempotent generator. The statement is **not**
proved here.

## Statement

`SemisimpleIdempotentOrderStatement.{u, v}` quantifies over

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`: a nonarchimedean local field, of any characteristic;
- `A : Type v` with `[Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A]`: a finite-dimensional semisimple `F`-algebra
  with its module topology.

It asserts the existence of a subring `R : Subring A` such that

1. `R` is compact and open in `A`;
2. `R` is stable under the integers of `F`: `c • x ∈ R` whenever `valuation F c ≤ 1` and
   `x ∈ R` (`valuation F` is the valuation of the given valuative relation);
3. for every left ideal `J : Submodule A A` there is `e ∈ R` with `IsIdempotentElem e` and
   `J = Submodule.span A {e}`, that is, `J = A e`.

Conditions 1 and 2 say that `R` is an order of `A`: a compact open subring that is a module
over the integers of `F`. Condition 3 is equivalent to: for every left ideal `J`, the left
`R`-module `J ∩ R` is a direct summand of `R` (if `J = A e` with `e ∈ R` idempotent, then
`J ∩ R = R e` and `R = R e ⊕ R (1 - e)`).

## Source and why the statement holds

André Weil, *Basic Number Theory*, second edition, Grundlehren der mathematischen
Wissenschaften 144, Springer, 1973, source ID `weil-1973-basic-number-theory`:

- Chapter I, §4, Theorem 6, printed pp. 12–13 (PDF pp. 29–30): for a `p`-field `K` (a
  non-discrete locally compact division ring with `mod_K(p · 1) < 1`, commutative or not), the
  set `R = {x | mod_K(x) ≤ 1}` is the unique maximal compact subring, `K` is ultrametric,
  `R^×` is the set where `mod_K = 1`, and the maximal ideal is `P = πR = Rπ`.
- Chapter II, §2, Theorem 1, printed p. 29 (PDF p. 46): "Let `L` be a `K`-lattice in a left
  vector-space `V` of dimension `n` over `K`. Then there is a basis `{v_1, …, v_n}` of `V` such
  that `L = Σ R v_i`. Moreover, if `W_1 = V, W_2, …, W_n` is any sequence of subspaces of `V`
  such that `W_i` is a subspace of `W_{i−1}` of codimension 1 for `2 ≤ i ≤ n`, the `v_i` may be
  so chosen that, for each `i`, `{v_i, …, v_n}` is a basis of `W_i`."

The statement combines these with the Wedderburn–Artin theorem (Mathlib's
`IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`): `A ≅ ∏_i M_{d_i}(D_i)` with
finite-dimensional division algebras `D_i` over `F`, each a `p`-field in Weil's sense for the
module topology. Take `R` to correspond to `∏_i M_{d_i}(R_i)`, with `R_i` the maximal compact
subring of `D_i`. A left ideal of `M_d(D)` consists of the matrices whose rows lie in a fixed
left `D`-subspace `U` of `D^d`. Weil's Theorem 1, applied to the lattice `R_i^d` and a flag
through `U`, gives a basis of `R_i^d` over `R_i` containing a basis of `U`; the projection
onto `U` along the span of the remaining basis vectors is right multiplication by an idempotent
matrix `e` with entries in `R_i`, and the left ideal is `M_d(D) e`. Left ideals of a finite
product are products of left ideals of the factors.

## Role

The statement supplies Harish-Chandra's well adapted lattices in the proof of Howe's finiteness
theorem for the Lie algebra of `Aˣ` (Harish-Chandra, *Admissible invariant distributions on
reductive p-adic groups*, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions`, Definition 10.6 and Remark 10.7,
printed p. 58, and §13.1, printed pp. 63–64): a lattice `ϖ^s R` is a two-sided `R`-module, so it
decomposes along every grading of `A` defined by orthogonal idempotents of `R`, and by
condition 3 such idempotents split the flag of left ideals attached to any element of `A`.
