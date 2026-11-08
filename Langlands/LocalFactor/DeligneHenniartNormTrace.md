# The quadratic norm–trace estimate and rank-one twists at a comparison element

Local-field lemmas for the dimension-one exact case of Deligne–Henniart 1981
(Lemma 4.7, printed pp. 110–111, PDF pp. 22–23). They are stated for
arbitrary p-adic fields and topological data; no Weil group or reciprocity
appears. Throughout, `F` and `E` are p-adic fields with
`[Algebra F.Carrier E.Carrier]`, the scalar tower from `Padic p`, and
`[FiniteDimensional F.Carrier E.Carrier]`. Absolute values are the published
canonical norms `F.canonicalNorm` and `E.canonicalNorm`, i.e. Mathlib's
spectral norms over `Padic p`. Orders `ord`, absolute ramification indices
`ramificationIndex` and residue degrees `residueDegree` are those of the
supplied topological data.

## The quadratic remainder

- `prod_one_add_sub_bound`: let `f` be a nonnegative, nonarchimedean,
  submultiplicative function on a commutative ring with `f 0 = 0`. Let
  `f (x i) ≤ ρ` for all `i ∈ s`, with `0 ≤ ρ ≤ 1`. Then
  `f (∑ x i) ≤ ρ` and `f (∏ (1 + x i) - 1 - ∑ x i) ≤ ρ ^ 2`. Proof: induction
  on `s`. With `S = ∑_s x i` and `P = ∏_s (1 + x i)`, one has
  `(1 + x j) P - 1 - (x j + S) = (P - 1 - S) + x j S + x j (P - 1 - S)`.
- `normTraceRemainder F E y` (definition):
  `Algebra.norm F.Carrier (1 + y) - 1 - Algebra.trace F.Carrier E.Carrier y`.
- `canonicalNorm_norm_one_add_sub_le`: if `|y| ≤ 1`, then
  `|normTraceRemainder F E y| ≤ |y| ^ 2` and `|Tr y| ≤ |y|`. This is the
  remark in DH81 3.3 (printed p. 103, PDF p. 15): `N(1 + x) = 1 + Tr(x) + R`,
  where `R` has valuation at least `2 v_L(x)/e`, by writing the norm as a
  product of conjugates. Proof: let `Ω` be an algebraic closure of
  `E.Carrier`. By Mathlib's `Algebra.norm_eq_prod_embeddings` and
  `trace_eq_sum_embeddings`, the norm and trace map into `Ω` as the product
  and the sum over the `F`-embeddings `σ : E → Ω`. The spectral norm of `Ω`
  over `Padic p` is nonarchimedean and submultiplicative, since `Ω` is
  algebraic over `Padic p`. It restricts to the canonical norms of `F` and
  `E`, since the minimal polynomial over `Padic p` is unchanged, and it
  satisfies `|σ y| = |y|` for every embedding. Then apply the previous lemma
  with `ρ = |y|`.

## Orders

- `canonicalNorm_pow_ef`: for `x ≠ 0`,
  `|x| ^ (e f) = p ^ (f · (-ord x))`. This comes from the published
  `normalizedAbs_eq_canonicalNorm_pow_ef`, `normalizedAbs_of_ne_zero` and
  `residueCardinality_eq_pow`.
- `discreteValuation_eq_exp_neg_ord`: for `x ≠ 0`, the discrete valuation is
  `exp (-ord x)`.
- `mem_additiveLattice_neg_of_le_ord`: if `x ≠ 0` and `m ≤ ord x`, then `x`
  lies in `additiveLattice (-m)`, the elements of order at least `m`.
- `ord_mul_le_of_canonicalNorm_le`: for `z ≠ 0` in `F` and `y ≠ 0` in `E`,
  `|z| ≤ |y| ^ k` implies `k · e_F · ord_E y ≤ e_E · ord_F z`, where `e_F`
  and `e_E` are the absolute ramification indices. Proof: raise both sides to
  the power `e_F f_F e_E f_E` and compare powers of `p`.

## Linearization through the norm

- `character_norm_one_add` (DH81 3.3 and the first step of 3.6, here with
  `1 + y` in place of the truncated exponential). The data:
  - `χ : F.Carrierˣ →* ℂˣ`, an additive character `ψ` of `F`, an element `c`
    of `F`, and `m, a > 0`;
  - `χ z = ψ (c (z - 1))` for every principal unit `z` of level `m`, and `χ`
    trivial on the principal units of level `a`;
  - `y ≠ 0` in `E` with `0 < ord_E y` and the two depth conditions
    `(a - 1) e_E < 2 e_F ord_E y` and `(m - 1) e_E < e_F ord_E y`;
  - a unit `u = 1 + y` of `E`.

  Then `χ (N_{E/F} u) = ψ (c · Tr y)`. Proof: the previous section puts
  `Tr y` in the lattice of order `≥ m` and `normTraceRemainder F E y` in the
  lattice of order `≥ a`, because orders are integers. Hence `w = 1 + Tr y` is
  a principal unit of level `m`, and `N(1 + y) w⁻¹ = 1 + R w⁻¹` is a principal
  unit of level `a`. So `χ (N u) = χ w = ψ (c Tr y)`.

## Rank-one twists at a comparison element

Here `T` is topological data of one p-adic field `G`.

- `mul_inv_mem_principalUnits_of_eq_on_lattice`: let `t < A`, and let
  `ord c' = -(n(ψ) + A)`. If `ψ (c x) = ψ (c' x)` for all `x` of order at least
  `t`, then `c c'⁻¹` is a principal unit of level `A - t`. Proof: the published
  `mem_additiveLattice_of_forall_complex_mul_eq_one` gives `c - c'` order at
  least `-n(ψ) - t`. Divide by `c'`.
- `abelianEpsilonExpression_mul_of_linearization`: let `χ` have conductor
  `a ≥ 2`, and let `d` have order `-(n(ψ) + a)` and linearize `χ` on the
  lattice of order `≥ a - ⌊a/2⌋` (the hypothesis `hlin` of the published
  `RankOneStability.gauss_integral_twist`). Then for every `η` with
  `2 a(η) ≤ a` and every Haar measure,
  `abelianEpsilonExpression (χ η) = η(d⁻¹) · abelianEpsilonExpression χ`.
  The proof repeats the `s = 0` case of the published `rankOneStability`: the
  conductor identity of `RankOneStability.conductor_and_L`,
  `gauss_integral_twist`, and `deligneConstant_eq_abelianEpsilonExpression`.
  This is DH81 Corollary 1.3(ii) (printed p. 94, PDF p. 6).
- `abelianEpsilonExpression_mul_of_comparison`: the same conclusion with
  `η(c⁻¹)`, for any unit `c` with `c d⁻¹` a principal unit of level `s` and
  `a(η) ≤ s`. In DH81 4.7 this is the step "le corollaire 3.7 nous assure
  l'égalité `η(a) = η(a')`": `c` is the base-field linearizer, `d` is the
  linearizer on the larger field, and the comparison lemma above supplies `s`.

## Scope

These lemmas do not use Herbrand functions. The application to DH81 4.7
must still supply the depth `t`, the conductors of the norm pullback and of
the test characters on the larger field, and the identity of the restricted
Weil character with the norm pullback. The deeper congruence DH81 3.8 /
3.12(i), with the truncated exponential, is not proved here.

The valuation/order identity reuses `PadicAbelian.gauss_valuation_eq_exp_neg_ord` from `Abelian/GaussShellVanishing`.
