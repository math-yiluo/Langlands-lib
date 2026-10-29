# Product-Levi dual-opposite square-integrability sufficiency

Author: Worker 728.

This module proves the consumer statement of
[`ProductLeviSquareIntegrableSufficiencyStatement`](ProductLeviSquareIntegrableSufficiencyStatement.md):

```text
theorem Langlands.glProductLeviDualOppositeSquareIntegrableSufficiency :
    GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement.{uF, uV}
```

The field universe `uF` and the representation universe `uV` stay
independent. The statement is imported by its Lean name and is not modified.
The theorem has no hypotheses. It says the following. Let `S` be an
irreducible admissible representation of an actual positive-rank GL block Levi
`M_C = C.Levi F.Carrier`, whose block scalars act by a unitary character `ω`.
Suppose that every nonzero dual eigenfunctional of every normalized refined
opposite Jacquet quotient, with an open-kernel character `ψ` and real part
`s`, has nonpositive prefix sums of `s` inside each outer block, and strictly
negative proper prefix sums. Then `S` is square-integrable modulo the full
centre of `M_C`, for every Borel Haar measure on the actual central quotient.

The module has three declarations:

- `ProductLeviDualOpposite.sum_mul_neg_of_antitone`, a strict summation by
  parts;
- `glProductLeviDualOppositeSquareIntegrableSufficiency_of_core`: the core
  proposition `GLProductLeviSquareIntegrableExponentSufficiencyStatement`
  implies the consumer proposition, at the same universes;
- the final theorem, which applies the second declaration to the core proof
  `glProductLeviSquareIntegrableExponentSufficiency` of
  [`ProductLeviSquareIntegrableSufficiencyProof`](ProductLeviSquareIntegrableSufficiencyProof.md).

## Strict summation by parts

`sum_mul_neg_of_antitone e v hv hproper htot hne`: let `e, v : Fin L → ℝ`
with `v` antitone and not constant. Suppose every proper prefix sum
`P_i = ∑_(k ≤ i) e k` with `i + 1 < L` is strictly negative, and
`∑_k e k = 0`. Then `∑_k e k * v k < 0`.

Since `v` is not constant, `L ≥ 2`. Let `first = 0` and `last = L - 1`. The
proper prefixes form a nonempty finite family. Let `η < 0` be their maximum
(`Finset.exists_max_image`). Shift the residuals by `-η` at `first` and by
`+η` at `last`:

```text
e' k = e k − [k = first] η + [k = last] η.
```

Every proper prefix of `e'` is `P_i − η ≤ 0`, by the choice of `η`. The full
prefix is `0 − η + η = 0`, and so is the total of `e'`. The published weak
summation by parts `ParabolicConeUniqueness.sum_mul_nonpos_of_antitone`
(module [`ParabolicConeUniquenessProof`](ParabolicConeUniquenessProof.md))
then gives

```text
∑_k e' k v k = ∑_k e k v k − η v(first) + η v(last) ≤ 0,
```

so `∑_k e k v k ≤ η (v(first) − v(last))`. Since `v` is antitone, every value
lies between `v(last)` and `v(first)`. As `v` is not constant,
`v(last) < v(first)`, and the right side is strictly negative.

## From the core form to the consumer form

`glProductLeviDualOppositeSquareIntegrableSufficiency_of_core` follows the
published tempered adapter `glProductLeviDualOppositeTemperedSufficiency_of_core`
of [`ProductLeviDualOppositeAdapter`](ProductLeviDualOppositeAdapter.md) step
by step, and adds the strict conjunct. The notation is that of the adapter:
`e(j,i) = C.flattenBlockEquiv D ⟨j, i⟩`, `D' = reverseRefinement C D` is the
blockwise reversed refinement, and `e'(j,i)` are its flattened labels, with
`reverseLabel C D (e'(j,i)) = e(j, i.rev)`.

Fix the data of the consumer statement and its hypothesis `hdual`. The proof
applies the core hypothesis `h` to the same data. It remains to show: for a
refinement `D`, an open-kernel generalized eigencharacter `ψ` of the upper
action, and a tuple `a` with `|a(e(j,i))|` monotone in `i` for each `j`, where
`|·| = T.normalizedAbs`,

- `‖ψ(a)‖ ≤ 1`, and
- `‖ψ(a)‖ < 1` if `|a(e(j,i))| ≠ |a(e(j,i'))|` for some `j`, `i`, `i'`.

1. **Transport.** By the published `isGeneralizedEigencharacter_reverse`,
   `ψ' = ψ ∘ precomp (reverseLabel C D)⁻¹` is a generalized eigencharacter of
   the opposite action of `D'`.
2. **Eigenfunctional.** As in the adapter,
   `DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter`
   gives a nonzero `φ` on `RefinedOppositeJacquetModule C D' S.ρ` with
   eigencharacter `ψ'`. Its hypotheses are admissibility of the opposite
   quotient (`Parabolic.isAdmissible_normalizedRefinedOppositeJacquet` and
   `isAdmissible_comp_continuousMulEquiv`), cofinality of compact open
   subgroups (`T.leviCompactOpen`) and centrality of flattened block scalars.
3. **Real part.** `ψ'` has open kernel, since precomposition with a
   relabelling is continuous. `T.exists_isRealPartOf` gives `s` with
   `‖ψ'(c)‖ = ∏_b |c_b|^(s_b)`.
4. **Prefixes and totals.** `hdual` at `D'`, `ψ'`, `s` and `φ` gives, for
   every outer block `j`, nonpositive prefixes `∑_(k ≤ i) s(e'(j,k))` and
   strictly negative proper ones. Unitarity of `ω` gives
   `∑_i s(e'(j,i)) = 0` for every `j`, by the published
   `sum_fibre_eq_zero_of_unitary` and `sum_filter_flattenOuter`.
5. **Exponent.** `ψ(a) = ψ'(a ∘ reverseLabel C D)`, so

   ```text
   ‖ψ(a)‖ = exp( ∑_j ∑_i s(e'(j,i)) · log |a(e(j, i.rev))| ).
   ```

   For fixed `j`, `x_j(i) = log |a(e(j, i.rev))|` is antitone in `i`, because
   the absolute values are positive and monotone in the inner index of `D`,
   and `Fin.rev` reverses order.
6. **Weak bound.** The weak summation by parts, with the prefixes and zero
   totals of step 4, bounds each inner sum by `0`. So the exponent is
   nonpositive and `‖ψ(a)‖ ≤ 1` (`Real.exp_le_one_iff`).
7. **Strict bound.** Suppose `|a(e(j,i))| ≠ |a(e(j,i'))|`. Then
   `x_j(i.rev) ≠ x_j(i'.rev)` by injectivity of `log` on positive reals
   (`Real.log_injOn_pos`), so `x_j` is not constant. The strict summation by
   parts, with the strictly negative proper prefixes and the zero total of
   block `j`, makes the inner sum of block `j` strictly negative. The other
   inner sums are nonpositive by step 6, so the exponent is strictly negative
   (`Finset.sum_lt_sum`) and `‖ψ(a)‖ < 1` (`Real.exp_lt_one_iff`).

## Signs

The transport adds no sign beyond those of the published adapter. The
reversal in step 1 only reorders the real part: the opposite real part `s` of
`D'` and the upper real part `r` of `D` satisfy
`s(e'(j,i)) = r(e(j, i.rev))`. Within an outer block with `m` inner blocks
(indexed from `1`), `s_k = r_(m+1−k)`. So the opposite prefixes of `D'` are
the upper suffixes of `D`, which are the negatives of the complementary upper
prefixes because the block totals vanish. The test vector `x_j` in step 5 is
written in the reversed order, which is why it is antitone and why summation
by parts applies directly to the opposite prefixes of `D'`.

For `C = (2)` and `D = (1,1)`, the Steinberg representation has opposite real
part `(-1/2, 1/2)`. Its proper prefix `-1/2` is strictly negative and its
total is `0`, so it satisfies the consumer hypothesis. On a tuple with
`|a₁| < |a₂|` the exponent is `(1/2)(log|a₁| − log|a₂|) < 0`, matching the
strict upper bound of the statement's GL₂ sign check. The trivial
representation has opposite real part `(1/2, -1/2)` and fails the hypothesis.
These are explanatory checks, not Lean theorems.

## Provenance

The theorem is the sufficiency half of Casselman's criterion (Theorem 4.4.6
of the 1995 notes; Waldspurger 2003, Proposition III.1.1) in the project's
dual-opposite form for the product Levi `M_C`. The sources and the
product-Levi translation are recorded in the statement's Markdown. The
analytic content is in the core proof. The dual-opposite form and its
reduction to the core form are internal to the project: the reduction
implements the direction "core implies consumer" of the section "Relation
between the two forms" of the statement's Markdown, which describes that
relation without proving it. It is not a literal theorem about algebraic
duals in the sources. The strict summation by parts is an elementary
derivation.

## Imports

- `ProductLeviDualOppositeAdapter` (block reversal, transport of generalized
  eigencharacters, and through its imports dual eigenfunctional existence,
  zero block totals and the weak summation by parts);
- `ProductLeviSquareIntegrableSufficiencyProof` (the core proof, and through
  it the target statement).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
