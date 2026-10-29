# Proof of strict exponential Cartan coefficient decay

Author: Worker 879.

This module proves

```text
theorem Langlands.glStrictCartanCoefficientBound :
    GLStrictCartanCoefficientBoundStatement.{uF, uV}
```

The statement is imported from
`Langlands.Representation.Exponents.StrictCartanCoefficientBoundStatement`.
The theorem has exactly the type of the published proposition. It adds no
hypotheses, and the field universe `uF` and the carrier universe `uV` stay
independent. The proof covers every prime `p`, every `F` and `T`, every
positive rank `n` and every carrier `V`, including the zero carrier. It never
assumes irreducibility, finite length, a finite-dimensional carrier,
`Nontrivial V` or a globally finite exponent set. The only spectral sets it uses
are the finitely many eigenvalues of finitely many endomorphisms of one
finite-dimensional space of fixed vectors.

The constants are `d = 0`, a single `r` with `0 < r < 1`, and an explicit
positive `C`, all depending on `v` and `ℓ`. The case `d = 0` is permitted by
the statement, and with it the polynomial factor `height lam ^ 0` equals `1`.
No polynomial is needed because every relevant eigenvalue lies strictly below
the half modulus, so powers of each compressed operator grow no faster than any
strictly larger exponential.

The hypotheses on `ω` (the scalar action and its unitarity) are not used. A
normalized tuple has a zero coordinate, so it decomposes as a nonnegative
combination of the noncentral fundamental coweights
`diag(ϖ I_k, I_(n-k))`, `0 < k < n`, without any central component.

## Route and relation to the literature

The statement's Markdown records a possible proof route through Casselman's
asymptotic expansion (Corollary 4.3.4 and §4.4 of [C95]) and the
finite-character argument in Waldspurger [W03], proof of III.1.2. The
implemented proof is a different, project-internal route. It does not use
chamber strata, bounded offsets or a Jacquet-pairing asymptotic. Instead it
compresses the coefficient to the finite-dimensional space `V^K` of vectors
fixed by one small compact open subgroup `K`, through the published normalized
compact average. On `V^K` the Cartan representatives act multiplicatively, by
the published block compression theorem, which the Library itself describes as
a derived translation of the laws motivating Casselman III.5.1–III.5.3. The finite
spectral input is then the eigenvalues of `n - 1` endomorphisms of `V^K`.
Each nonzero eigenvalue is identified with the value of an actual
`T.IsJacquetExponent` character of a two-block parabolic. The proof therefore
uses neither III.1.1 or III.1.2 of [W03] nor Casselman's integrability
theorem 4.4.6, and no square-integrability notion appears in it. Every step
is a published Library result or an elementary lemma proved here, so the
implemented proof needs no reading of the original sources beyond the
statement's own documentation.

## 1. Eigenvalues of compressions (`StrictCartanBound` namespace)

`StrictExponentHypothesis T ρ` is a local `Prop` abbreviation of hypothesis 4
of the target, verbatim: for every block shape `B`, every `χ` with
`T.IsJacquetExponent B ρ χ`, and every block scalar `a` with monotone
normalized absolute values and two unequal values, `‖χ a‖ < 1`.

`norm_eigenvalue_lt_sqrt_leviModulus`: assume `ρ` admissible and satisfying
the hypothesis. Let `K` be compact open with the block Iwahori factorization
for `B`, let `a` be strictly contracting with two distinct absolute values,
and let `x ∈ V^K` be nonzero with `compressedAction (blockScalar a) x = μ • x`.
Then `‖μ‖ < sqrt (leviModulus B (blockScalarLevi a))`. The proof:

1. The case `μ = 0` is immediate, since the modulus is a positive unit.
2. For `μ ≠ 0`, `A^r x = μ^r x ≠ 0` for all `r`. So `x` is not in the
   supremum of the kernels of the powers of `A`. The kernels increase, and
   `Submodule.mem_iSup_of_directed` turns membership in the supremum into
   membership in one kernel. By the published
   `Jacquet.blockPowerKernel_eq_jacquetKernel` (strict contraction), that
   supremum is the kernel of the fixed Jacquet map. Hence the class of `x` in
   the coinvariants of `B.unipotentSubgroup` is nonzero.
3. The published `Jacquet.blockCompressedAction_mk` and `Jacquet.action_mk`
   give `mk (ρ(blockScalar a) x) = μ • mk x`. The published linear
   equivalence `B.jacquetModuleEquiv ρ` transfers this to `B.jacquetMk`,
   and `T.splitCentreJacquet_mk` shows that `y = B.jacquetMk ρ x ≠ 0` is an
   eigenvector of the normalized split-centre action of `a`, with eigenvalue
   `c = sqrt(δ(a))⁻¹ μ`.
4. By `Parabolic.isAdmissible_normalizedJacquet`, `y` is fixed by an open
   subgroup `L` of the Levi, and its fixed space is finite-dimensional. Its
   intersection `E` with the `c`-eigenspace of `a` contains `y`. It is stable
   under the whole split centre, by
   `Parabolic.splitCentreJacquet_mem_fixedVectors` and commutativity of the
   block scalars.
5. The published `EndomorphismBound.exists_common_eigenvector` gives a common
   eigenvector `w ∈ E`, and `EndomorphismBound.exists_character_of_forall_eigen`
   gives a character `χ` of `(F^×)^r` with eigenvector `w`. The split-centre
   action is smooth by `isSmooth_comp`, since `blockScalarLevi` is continuous
   (through `GeneralLinear.scalarContinuous`) and
   `T.isSmooth_normalizedJacquet` holds. So an open subgroup fixes `w` and
   lies in `ker χ`, making `ker χ` open. Together with
   `isGeneralizedEigencharacter_of_eigenvector`, this is exactly
   `T.IsJacquetExponent B ρ χ`.
6. `χ a = c` because `w` lies in the `c`-eigenspace. The monotonicity premise
   follows from strict contraction through the published
   `ProductLeviChamber.monotone_abs_of_isWeaklyContracting`. The strict
   hypothesis gives `‖c‖ < 1`, which is the claimed bound.

`norm_eigenvalue_fund_lt` specializes this to the published two-block shape
`ProductLeviChamber.twoBlock n k` and the scalars `twoScalars T = (ϖ, 1)`,
`0 < k < n`. The published lemmas `twoBlock_blockScalar`,
`twoBlock_isStrictlyContracting`, `twoBlock_leviModulus` and `delta_fund`
identify the block scalar with `representative T (fund n k)` and the modulus
with `delta T (fund n k) = q^(-k(n-k))`. `twoScalars_abs_ne` checks the
premise of unequal absolute values, `|ϖ| = q⁻¹ ≠ 1`. The result: every
eigenvalue of the compression of `diag(ϖ I_k, I_(n-k))` has norm
`< sqrt (delta T (fund n k))`.

## 2. Finite-dimensional choices

- `exists_eigenvalue_bound_lt`: if all eigenvalues of `f ∈ End(W)` have norm
  below `s > 0`, with `W` finite-dimensional, then some `0 ≤ r₀ < s` bounds
  them all. The eigenvalues form a finite set (Mathlib
  `Module.End.finite_hasEigenvalue`), and `r₀` is the supremum of their norms.
- `exists_common_radius`: finitely many strict inequalities `r₀ i < s i` give
  one `r ∈ (0, 1)` with `r₀ i < s i * r^(e i)` for all `i`. The proof is a
  limit argument in `𝓝[<] 1`, using `Filter.eventually_all`.
- `fund_gap_eigenvalue_lt`, `fund_gap_eigenvalue_bound`, `exists_fund_radius`
  and `exists_pow_constants` assemble these steps for `k = t + 1`,
  `t : Fin (n - 1)`. `exists_pow_constants` applies the published Gelfand-type
  bound `EndomorphismBound.exists_endNorm_pow_le` with
  `rad t = sqrt(delta(fund n (t+1))) * r^(t+1) > r₀ t`.
- `exists_radius_constants` therefore gives one `r ∈ (0, 1)` and constants
  `c t ≥ 0` with
  `endNorm (Q_t ^ j) ≤ c t * (sqrt(delta(fund n (t+1))) * r^(t+1))^j` for all
  `j`, where `Q_t` is the compression of `representative T (fund n (t+1))` and
  `endNorm` is the published submultiplicative matrix-norm size.

## 3. Multiplicativity and gap coordinates

- `borelTuple T lam` gives the uniformizer powers as singleton-block scalars,
  and `borelTuple_blockScalar` identifies its block scalar with
  `representative T lam`. An antitone `lam` gives a weakly contracting tuple
  (`borelTuple_isWeaklyContracting`). These lemmas adapt the corresponding
  product-Levi lemmas of `ProductLeviChamberBoundProof` (Worker 246) to
  `GL_n` itself.
- `compressedAction_representative_add` and `_nsmul`: by the published
  `Jacquet.blockCompressedAction_mul` for the singleton shape, compression is
  multiplicative on antitone tuples. For example,
  `compress(rep(m • f)) = compress(rep f)^m`.
- `gap lam t = (lam t - lam (t+1)).toNat`. `normalized_eq_sum` writes a
  normalized tuple as `∑_t gap lam t • fund n (t+1)`, using the published
  `normalized_eq_sum_fund`. `antitone_sum_fund` shows that every partial sum
  is antitone.
- `endNorm_sum_fund_le` is a finset induction:
  `endNorm(compress(rep(∑_{t∈S} g t • fund))) ≤ endNorm(compress(rep 0)) *
  ∏_{t∈S} (c t * rad t^(g t))`.
- Exact weights: `sqrt_delta_eq` gives
  `sqrt (delta lam) = ∏_t sqrt(delta(fund n (t+1)))^(gap lam t)`, from the
  published `delta_sum` and `delta_nsmul` and the identity
  `sqrt x = x^(1/2)`. `height_sub_one_eq` gives
  `height lam - 1 = ∑_t gap lam t * (t+1)`, because normalized coordinates are
  nonnegative and `∑_i fund n k i = k` (`sum_fund`). Then `rpow_height_eq`
  gives `Real.rpow r (height lam - 1) = ∏_t (r^(t+1))^(gap lam t)`.
- `endNorm_compressedAction_le` combines these: for every normalized `lam`,
  `endNorm(compress(rep lam)) ≤ E₀ * (sqrt(delta lam) * r^(height lam - 1))`
  with `E₀ = endNorm(compress(rep 0)) * ∏_t c t ≥ 0`.

## 4. Compact factors and the final assembly

- The imported `ProductLeviTempered.discreteValuation_integer`,
  `ProductLeviTempered.maximalCompact_eq` and the local
  `maximalCompact_eq_levelSubgroup` identify `CartanQuotient.maximalCompact`
  with the published level-zero subgroup `Conductor.levelSubgroup F m 0`.
  The first two are Worker 246's unchanged declarations, relocated to
  [CartanIntegralSubgroup](../../Group/GL/CartanIntegralSubgroup.md).
  `isOpen_maximalCompact` and `isCompact_maximalCompact` follow from
  `Conductor.levelOpenSubgroup` and `Conductor.isCompact_levelOpenSubgroup`
  in positive rank.
- `dual_apply_eq_compressedAction`: a `K`-fixed functional satisfies
  `φ(ρ(g) w) = φ(compress(g) w)`, by the published
  `Compact.dual_averageMap_eq_of_mem_fixedVectors`.
- `smoothDual_apply_mul`:
  `ℓ(ρ(k₁ g k₂) v) = (smoothContragredient ρ k₁⁻¹ ℓ)(ρ(g)(ρ(k₂) v))`.
- `glStrictCartanCoefficientBound`: let `K₀` be the open compact
  `maximalCompact T n`. By `Compact.finite_orbit_of_smooth`, applied to `ρ` and
  to `smoothContragredient ρ` (smooth by `isSmooth_smoothContragredient`),
  the orbits of `v` and `ℓ` under `K₀` are finite. The finite intersection of
  their stabilizers is a neighbourhood of `1`. The published
  `BlockShape.exists_compactOpenSubgroup_forall_hasBlockIwahoriFactorization`
  provides inside it one compact open `K` with the block Iwahori
  factorization for every block shape simultaneously. Each orbit vector lies in
  `V^K`, which is finite-dimensional by admissibility, and each orbit
  functional is `K`-fixed. For each of the finitely many pairs, the published
  `EndomorphismBound.exists_apply_le_endNorm` gives `‖φ(f w)‖ ≤ C(w,φ) *
  endNorm f`. With `M = ∑ C(w,φ)` and `C = M * E₀ + 1 > 0`, every
  `k₁, k₂ ∈ K₀` gives

  ```text
  ‖ℓ(ρ(k₁ * representative T lam * k₂) v)‖
    ≤ C * sqrt (delta T lam) * height lam ^ 0 * Real.rpow r (height lam - 1).
  ```

Degenerate cases need no separate argument. For `n = 1`, `Fin (n - 1)` is
empty: the only normalized tuple is `0`, every product above is empty and the
bound is a constant. For a zero carrier, all vectors vanish and the same
constants work.

## Dependencies and independence

Direct imports:

- `Langlands.Representation.Exponents.StrictCartanCoefficientBoundStatement`:
  the target, unchanged.
- `Langlands.Representation.Exponents.JacquetEigenvectorProof`:
  `Parabolic.isAdmissible_normalizedJacquet`,
  `Parabolic.splitCentreJacquet_mem_fixedVectors`.
- `Langlands.Representation.Jacquet.BlockPowerKernelProof`:
  `Jacquet.blockPowerKernel_eq_jacquetKernel`; through it,
  `BlockCompressionProof` for `blockCompressedAction_mul` and
  `blockCompressedAction_mk`.
- `Langlands.Representation.Classification.ProductLeviChamberBoundProof`:
  only its elementary `ProductLeviChamber` lemmas `twoBlock`, `twoScalars`,
  `twoBlock_blockScalar`, `twoBlock_isStrictlyContracting`,
  `twoBlock_leviModulus`, `fund`, `fund_antitone`, `delta_fund`,
  `normalized_eq_sum_fund`, `antitone_nsmul`, `delta_sum`, `delta_nsmul`,
  `representative_zero`, `blockScalar_val`, `uniformizer_abs`,
  `residueCardinality_gt_one_real` and
  `monotone_abs_of_isWeaklyContracting`. Through its imports it
  also supplies `EndomorphismBound` (`Langlands.Analysis.EndomorphismPowerBound`),
  `Compact.dual_averageMap_eq_of_mem_fixedVectors` and
  `exists_compactOpenSubgroup_forall_hasBlockIwahoriFactorization`
  (`CuspidalSupport.UniformBlockIwahoriBasis`). Its main theorem, the weak
  product-Levi chamber bound, is not used.
- `Langlands.Representation.Smooth.Contragredient.LawsProof`
  (`isSmooth_smoothContragredient`),
  `Langlands.Representation.Smooth.Transfer.PullbackProof` (`isSmooth_comp`),
  and Mathlib's `LinearAlgebra.Eigenspace.Minpoly`.

Audit, against Library commit `4021bb1d1ec99e65990e08addda3ade7caa73058`:
the transitive import closure of this module has 337 project modules. None of
them mentions `GLSquareIntegrableExponentCriterionStatement`, the
segment-analytic, multisegment-head, ordered-head, quotient-exhaustion,
tempered-block-uniqueness, square-integrable Langlands classification or
exhaustion, or regular-exhaustion targets. None of their proof modules exists
in the Library. The closure does contain the definition modules
`Classification.Tempered` and `Classification.Essential`, and the
statement-only modules `ProductLeviTemperedSufficiencyStatement`,
`TemperedSupportStatement` and similar, through the weak product-Levi
statement. No hypothesis or conclusion of those statements is used. The
theorem's axioms are `propext`, `Classical.choice` and `Quot.sound`. No
published statement, pending task or citation is treated as a proved input.
