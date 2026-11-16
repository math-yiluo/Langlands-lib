# Intertwiners to the reversed standard module of a strictly ordered character list

Lean module: `Langlands.Representation.Archimedean.RealStrictCharacterReverseKernel`.

Worker 5 wrote this module for Task 7069 (`79f2a631-6cbb-4805-97c7-163e69df5de3`), the proof of
`RealStandardIrreducibleCriterionStatement`. It proves the statement
`RealReverseIntertwinerKernelStatement` (Rev, Library module
`RealStandardIrreducibleCriterionReduction`) in one special case: every block is a character of
`GL_1(ℝ)` and the real parts of the exponents strictly decrease. The statement is
`Langlands.Archimedean.RealStrictCharacterReverseKernel.RealStrictCharacterReverseKernelStatement`,
proved as
`Langlands.Archimedean.RealStrictCharacterReverseKernel.realStrictCharacterReverseKernel`.
The general Rev also allows equal exponents (ties) and induced `GL_2` blocks; it is not proved
here.

Declarations without a prefix are in the namespace
`Langlands.Archimedean.RealStrictCharacterReverseKernel`.

## The statement

`RealStrictCharacterReverseKernelStatement`. Let `n : ℕ` and `ds : List RealBlock`. Write `I(ds)`
for `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the `O(n)`-finite
functions of the standard module of `ds`. Let

* `T : I(ds) →ₗ[ℂ] I(ds.reverse)` be a `ℂ`-linear map, and
* `W` a `ℂ`-submodule of `I(ds)`.

Assume:

* `realRank ds = n`;
* every block is a character: `IsCharacterList ds`, that is, `∀ b ∈ ds, ∃ c, b = .character c`;
* the real parts of the exponents strictly decrease: `IsStrictlyOrdered ds`, that is,
  `ds.Pairwise fun x y => realBlockExponent y < realBlockExponent x`;
* `T` is an intertwiner:
  `IsRealStandardIntertwiner n (realStandardRep n ds.reverse) (realStandardLie n ds.reverse) ds T`;
* `W` is a `(𝔤, K)`-submodule: `IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W`;
* `W ≠ ⊤`.

Then `W ≤ LinearMap.ker T`.

This is the conclusion of `RealReverseIntertwinerKernelStatement`, word for word. The only
change is that the hypothesis `IsRealLanglandsOrdered ds` (non-strict order) is replaced by
`IsCharacterList ds` and `IsStrictlyOrdered ds`, which together imply it. (`IsCharacterList` and
`IsStrictlyOrdered` are the Library definitions of the module `RealStrictCharacterLanglandsQuotient`.)

Provenance. Derived from the Library statement `RealReverseIntertwinerKernelStatement` by
restricting to character blocks in strict order. Its source, as recorded in
`RealStandardIrreducibleCriterionReduction.md`, is Langlands' theorem in the form of Mœglin's
Theorem 4 (C. Mœglin, Representations of GL(n) over the real field, Proc. Sympos. Pure Math. 61
(1997), printed p. 159; `bailey-knapp-1997-pspm61`, PDF page = printed page + 9): for a positive
character `χ` of the diagonal torus, the principal series `I(χ)` has a unique irreducible
quotient `J(χ)`, the principal series `I(w₀χ)` has a unique irreducible submodule, isomorphic to
`J(χ)`, and `J(χ)` occurs with multiplicity one in `I(χ)`. See also Knapp 1986, Theorem 8.54
(printed p. 267) and Proposition 8.61 (printed p. 274) (Library source
`provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855`, PDF page = printed
page + 14). For a strictly ordered character list, `I(ds)` is the principal series of the position
characters, and `I(ds.reverse)` is the principal series of the reversed characters, Mœglin's
`I(w₀χ)`. The derivation of Rev from Langlands' theorem is in
`RealStandardIrreducibleCriterionReduction.md`. The proof below does not use Langlands' theorem.
It is internal: it combines the Library's Jacquet-integral results with a minimal `O(n)`-type
argument.

## Notation

`GL_n = Langlands.GeneralLinear n ℝ`, and `O(n) = unitaryCompact ℝ n`, with its normalized Haar
measure `dκ = haarK n` (Library, `RealPrincipalSeriesDuality`). For finite sets
`A, B ⊆ {0, …, n−1}`, `det X_{A,B}` is `MatrixMinor.minor X A B`: the determinant of the submatrix
with rows `A` and columns `B`, both in increasing order, and `0` when `|A| ≠ |B|`. `R(k)` is right
translation, `R(k) f(g) = f(g k)`. `PS(χ)` is `principalSeries ℝ n χ`, and `X(χ)` its
`O(n)`-finite functions. `dualChar χ` is the family of inverse characters `χ_l(y)⁻¹`. `Λ_n` is the
Jacquet integral `JacquetDual.jacquet n` of the Library. `φ_{A,B} = JacquetMinor.minorVector n e A B`
is the vector of `PS(χ)` whose restriction to `O(n)` is `κ ↦ det κ_{A,B}` (module
`JacquetMinorNonvanishing`). "The sign condition for `I`" means `χ_l(−1) = −1` for `l ∈ I` and
`χ_l(−1) = 1` for `l ∉ I`, for `l < n`.

## Auxiliary results

1. `exists_interpolation`. Let `S` be a finite-dimensional space of functions `X → ℂ`. Then there
   are finitely many points `p_i ∈ X` and functions `u_i ∈ S` with `s = ∑_i s(p_i) u_i` for every
   `s ∈ S`. Proof: the evaluations at points separate `S`, so each coordinate functional of a
   basis of `S` is a finite combination of evaluations (the Library's `exists_sum_of_separating`,
   applied to an extension of the coordinate functional to all functions). Expanding `s` in the
   basis gives the formula, with the index type `Σ j, Fin (m j)`.
2. `minorK n A B κ = det κ_{A,B}` as a complex function on `O(n)`; `continuous_minorK`.
3. `proj n A B f g = ∫_{O(n)} det κ_{A,B} · f(g κ) dκ`, the projection `P_{A,B} f`.
   `integrable_minorK_mul`: the integrand is integrable when `f` is continuous.
4. `exists_proj_mem`. Let `f` be continuous and let `V` be a finite-dimensional space of functions
   on `GL_n` that contains every `R(κ) f`, `κ ∈ O(n)`. Then `P_{A,B} f ∈ V`, and every linear
   functional `Λ` on `V` satisfies `Λ(P_{A,B} f) = ∫_{O(n)} det κ_{A,B} · Λ(R(κ) f) dκ`. Proof:
   interpolation (1) in `V` gives `f(g κ) = ∑_i f(p_i κ) u_i(g)`, so
   `P_{A,B} f = ∑_i P_{A,B} f(p_i) · u_i ∈ V`. Both sides of the formula for `Λ` then equal
   `∑_i (∫ det κ_{A,B} f(p_i κ) dκ) Λ(u_i)`.
5. `val_inv_eq_transpose`: the inverse of `κ ∈ O(n)` is its transpose.
6. `proj_apply_of_mem`. If `f` is continuous, `|B| = |A|` and `k ∈ O(n)`, then
   `P_{A,B} f(k) = ∑_{|C| = |A|} det k_{C,A} · P_{C,B} f(1)`. Proof: substitute `κ ↦ k κ` (left
   invariance of the Haar measure, `integral_mul_left_eq_self`). This turns `P_{A,B} f(k)` into
   `∫ det (kᵀ κ)_{A,B} f(κ) dκ`. Then expand `det (kᵀ κ)_{A,B}` by Cauchy–Binet
   (`MatrixMinor.minor_mul`) and use `det (kᵀ)_{A,C} = det k_{C,A}` (`MatrixMinor.minor_transpose`).
7. `proj_one_eq_zero` (`M`-orthogonality). Let `χ_l(1) = 1` for all `l`, let `χ` satisfy the sign
   condition for `I`, and let `f ∈ PS(χ)`. Then `P_{C,B} f(1) = 0` for every `C ≠ I` and every
   `B`. Proof: choose `j` in exactly one of `C` and `I`, and let `t` be the diagonal matrix with
   `−1` at `j` and `1` elsewhere; it lies in `O(n)`. Substitute `κ ↦ t κ`. Then
   `det (t κ)_{C,B} = ± det κ_{C,B}` with sign `−1` iff `j ∈ C` (`minor_diagonal_mul`), and
   `f(t κ) = χ_j(−1) f(κ)` with sign `−1` iff `j ∈ I` (`principalSeriesCharacter_single`). The
   product of the two signs is `−1`. So the integral equals its own negative.
8. `isStrictlyDominant_neg`: if `ds` is a character list whose exponents have strictly
   *increasing* real parts, then the negated position exponents `l ↦ −(realPositionExponent ds l)`
   are strictly dominant, `IsStrictlyDominant _ (realRank ds − 1)`. Induction on the list, as in
   the Library's `isStrictlyDominant`.
9. `sign_filter`: if every `χ_l(−1)` is `±1`, then `χ` satisfies the sign condition for
   `{l | χ_l(−1) = −1}`. `dualChar_neg_one`: the values `±1` at `−1` pass to `dualChar χ`.

## Proof of the main theorem

`realStrictCharacterReverseKernel`. Fix `n`, `ds`, `T`, `W` with the hypotheses.

1. **Characters.** Let `χ = realPositionCharacter ds`, a signed power with exponents
   `e = realPositionExponent ds`, strictly dominant (Library `isSignedPower`,
   `isStrictlyDominant`, with `realRank ds = n`). Let `χ_r = realPositionCharacter ds.reverse` and
   `χ' = dualChar χ_r`. It is a signed power with exponents `e' = −e_r` (`IsSignedPower.dual`).
   The list `ds.reverse` is a character list with strictly increasing exponents and rank `n`
   (`realRank_perm`), so `e'` is strictly dominant (8). By `realStandardModule_eq`,
   `I(ds) = X(χ)` and `I(ds.reverse) = X(χ_r) = X(dualChar χ')`, since `dualChar` is an
   involution. Let `I = {l | χ_l(−1) = −1}` and `I' = {l | χ'_l(−1) = −1}`; by (9) `χ` and `χ'`
   satisfy the sign conditions for `I` and `I'`.
2. **`W` lies in the kernel of `Λ_n`.** As functions on `GL_n`, the elements of `W` form an
   `O(n)`- and `𝔤`-stable subspace `W'` of `X(χ)` (from `IsGKSubmodule`, `realStandardRep_apply_coe`
   and `realStandardLie_one_tmul_apply_coe`). Since `W ≠ ⊤`, some `g ∈ X(χ)` is not in `W'`. The
   Library's `JacquetKernel.jacquet_eq_zero_of_proper` gives `Λ_n(w) = 0` for all `w ∈ W'`.
3. **Suppose `T` does not vanish on `W`.** Then `U = T(W)`, as functions on `GL_n`, is a nonzero
   subspace of `X(dualChar χ')`. It is `O(n)`- and `𝔤`-stable, because `T` is an intertwiner.
4. **A vector of `W` that pairs nontrivially.** By `JacquetMinor.minorVector_mem`, `φ'_{I',I'}`
   (built with `e'`) lies in `X(χ')`. By `JacquetMinor.jacquet_minorVector_ne_zero` for `χ'`,
   `Λ_n(φ'_{I',I'}) ≠ 0`. The Library's duality result `JacquetDual.jacquet_eq_zero`, applied to
   `χ'`, `U` and `h = φ'_{I',I'}`, then gives some `u ∈ U` with
   `∫_{O(n)} u(κ) φ'_{I',I'}(κ) dκ ≠ 0`. Write `u = T w` with `w ∈ W`. Since
   `φ'_{I',I'}(κ) = det κ_{I',I'}` on `O(n)`, this says `∫ det κ_{I',I'} · (T w)(κ) dκ ≠ 0`.
5. **The projection of `w`.** Let `V` be the span of the right translates `R(κ) w`, `κ ∈ O(n)`.
   It is finite-dimensional because `w` is `O(n)`-finite, and `V ⊆ W'` by `O(n)`-stability. Let
   `Λ(v) = (T v)(1)` on `V`. Since `T` is an intertwiner, `Λ(R(κ) w) = (T w)(κ)`. By (4),
   `P_{I',I'} w ∈ V` and `Λ(P_{I',I'} w) = ∫ det κ_{I',I'} (T w)(κ) dκ ≠ 0`, so
   `P_{I',I'} w ≠ 0`.
6. **`P_{I,I'} w(1) ≠ 0`.** `P_{I',I'} w ∈ V ⊆ X(χ)` is nonzero, so it does not vanish at some
   `k ∈ O(n)` (`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`). By (6),
   `P_{I',I'} w(k) = ∑_{|C| = |I'|} det k_{C,I'} · P_{C,I'} w(1)`. By (7) every term with
   `C ≠ I` vanishes. Hence `|I| = |I'|` and `P_{I,I'} w(1) ≠ 0`.
7. **`φ_{I,I} ∈ W'`.** By (4), `P_{I,I'} w ∈ V ⊆ W' ⊆ X(χ)`. On `O(n)`, (6) and (7) give
   `P_{I,I'} w(k) = det k_{I,I} · P_{I,I'} w(1)`. So `P_{I,I'} w` and
   `P_{I,I'} w(1) · φ_{I,I}` are two elements of `PS(χ)` that agree on `O(n)`. They are equal
   (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`), and `φ_{I,I} ∈ W'`.
8. **Contradiction.** By step 2, `Λ_n(φ_{I,I}) = 0`. But
   `JacquetMinor.jacquet_minorVector_ne_zero` for `χ` gives `Λ_n(φ_{I,I}) ≠ 0`.

Axioms of `realStrictCharacterReverseKernel`: `propext`, `Classical.choice`, `Quot.sound`.

## Dependencies

Besides the Library, the proof uses three new modules written for Task 7069:

* `JacquetMinorNonvanishing` (namespace `JacquetMinor`): the minor vectors `φ_{A,B}` and
  `jacquet_minorVector_ne_zero`;
* `ChartIwasawaPower` and `PartialSqIntegral`, used by `JacquetMinorNonvanishing`;

and the module `Langlands.LinearAlgebra.MatrixMinor` (minors, Cauchy–Binet). From the Library it
uses `JacquetDual.jacquet_eq_zero`, `JacquetKernel.jacquet_eq_zero_of_proper`,
`RealStrictCharacterLanglandsQuotient` (`realStandardModule_eq`, `isSignedPower`,
`isStrictlyDominant`, `realPositionCharacter_neg_one`), `realRank_perm`
(`RealStandardIrreducibleCriterionReduction`), `exists_sum_of_separating`
(`PrincipalSeriesGKModule`), and the Haar measure `haarK` on `O(n)`.
