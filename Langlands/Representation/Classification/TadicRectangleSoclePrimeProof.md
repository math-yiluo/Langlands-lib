# Tadić's Proposition 3.8: the classes `⟨a(n,d)^ρ⟩` are prime in `R`

Author: Worker 4021.

`Langlands.Classification.TadicRectanglePrime.tadicRectangleSoclePrime.{uF, uV}` proves
exactly the published proposition
`Langlands.Classification.TadicRectangleSoclePrime.{uF, uV} F T` of
`Langlands/Representation/Classification/TadicBlockReductionStatement.lean`. Its outer
telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`,
with `uF` and `uV` independent. It adds no premise. The statement asserts: in the ring
`R = Aubert.gradedInductionRing F T (Aubert.binaryProductExactness F T)
(Aubert.gradedInductionRingLaws F T _)`, for every cuspidal datum `ρ`, all `n, d` with
`hd : 0 < d` and `0 < n`, every `N`, every
`π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)` with
`(tadicMultisegment ρ n d hd).IsZelevinskySocle π`, and every finite-length witness `hπ`,
the class `Aubert.gradedInclusion F T N (finiteLengthClass N F.Carrier π hπ)` is `Prime`.
The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

The entry module `Langlands.Representation.Classification.TadicRectangleSoclePrimeProof`
uses three helper modules submitted with it:

- `TadicRectanglePrimeAlgebra`: a primality criterion for weighted homogeneous
  polynomials over `ℤ`;
- `TadicRectanglePrimeRing`: the ring `R` in the monomial coordinates
  `ℤ[segments] ≅ R`, Zelevinsky's Theorem 7.1 in those coordinates, and his
  Proposition 4.6 in `R`;
- `TadicRectanglePrimeCombinatorics`: the rectangle `a(n,d)` in positions, Tadić's
  Lemma 3.4 and the neighbours `a_{k,k+1}`.

All declarations are in namespace `Langlands.Classification.TadicRectanglePrime`.

## Source and route

M. Tadić, *Classification of unitary representations in irreducible representations of
general linear group (non-Archimedean case)*, Ann. Sci. ÉNS (4) 19 (1986), 335–382,
literature ID `tadic-1986-unitary`, §3.3–3.7 and Proposition 3.8 with its proof, printed
pp.353–356 (PDF pp.20–23). The inputs from A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II* (1980), literature ID `zelevinsky-1980-induced-ii`, are
Corollary 7.5 (`R` is a polynomial ring in the segment classes), Theorem 7.1 and
Proposition 4.6, all available in the Library.

Tadić's proof: in the polynomial ring `R = ℤ[⟨Δ⟩]`, inverting Theorem 7.1 gives
`⟨a₀⟩ = ζ(a₀) + ∑_k m_{a_{k,k+1}, a₀} ζ(a_{k,k+1}) + …` with nonzero coefficients at the
neighbours `a_{k,k+1}` (§3.5–3.7). A nontrivial factorization `⟨a₀⟩ = P₁ P₂` into
homogeneous factors splits the leading monomial, and the neighbour monomials yield a
contradiction through degrees and Lemma 3.4 (pp.354–356). Tadić first reduces to
`d, n ≥ 2` (§3.3 treats `d = 1` or `n = 1` via the involution).

The Lean proof follows the same strategy, with these differences:

- Zelevinsky's order is replaced by the Library's rank order `Multisegment.RankLE`, in
  which the Library proves Theorem 7.1. Lemma 3.4 and "nothing lies strictly between
  `a_{k,k+1}` and `a₀`" are proved for this order.
- The grading used is the weight `S ↦ S.length` on segment variables (the size of the
  cuspidal content), not the rank of `GL`.
- The final contradiction is the weight count of
  `TadicRectanglePrimeAlgebra.irreducible_of_adjacent`: the degree pattern of a factor
  in the variables `X_{Δ_j}` describes how both the leading monomial and the neighbour
  monomial split. No case distinction is needed: the argument covers `d = 1` and
  `n = 1` as well, without Tadić's reduction.
- The nonvanishing of the coefficient of `ζ(a_{k,k+1})` is proved by counting the labels
  of `a_{k,k+1}` in `ζ(a₀) - ⟨a₀⟩` (below), rather than through the explicit
  coefficient `m'_{b₀,a} = -m(b₀; a)` of §3.6.

## Implemented proof

### Socles and labels

- `isIrreducible_of_isZelevinskySocle`: a Zelevinsky socle is irreducible.
- `isLabel_of_isZelevinskySocle`: a Zelevinsky socle `π` of `a` on `GL_N` gives a label
  of `a` (Library `Aubert.SegmentPolynomialSurjectivity.IsLabel`): its class is that of an
  irreducible Zelevinsky subrepresentation of a product of segment socles with
  multisegment `a`.
- `exists_isLabel_of`: every multisegment `a` has a label in degree `a.degree`, from the
  published `multisegmentConstituentDataExistence` and
  `orderedMultisegmentSocleExistence`. (Worker 5121's staged, unpublished
  `TadicBlockRing` has a lemma of the same name; it is reproved here since it is not in
  the Library.)

### The neighbour `c_k = a_{k,k+1}`

Write `a₀ = rect σ n e` and `c_k = adj σ n k e` (`k + 1 < n`) as in
`TadicRectanglePrimeCombinatorics`.

- `zetaR_add`: `ζ(a + b) = ζ(a) ζ(b)` (Library `zeta_add`).
- `isEffective_zetaR_rect_sub_adj`: `ζ(a₀) - ζ(c_k)` is effective. By
  `exists_isEffective_zetaR_pair_sub` (Proposition 4.6) for `Δ_k` preceding `Δ_(k+1)`
  (`seg_precedes`), with `replacement_eq` identifying the replacement,
  `ζ({Δ_(k+1), Δ_k}) - ζ(seg σ k (e+1) ::ₘ capMs σ k e)` is effective. Multiply by the
  effective `ζ(rest σ n k e)` (`isEffective_mul`) and use `rect_eq_pair_add`,
  `adj_eq_add`.
- `coeff_poly_adj_ne_zero`: for a label `c` of `a₀`, the coefficient of `X^{c_k}` in
  `poly [c]` is nonzero. Put `Y = ζ(a₀) - [c]`, effective. Then
  `poly [c] = X^{a₀} - poly Y` (`poly_zetaR`), and `X^{a₀} ≠ X^{c_k}` (`adj_ne_rect`), so
  the coefficient is `-(poly Y).coeff c_k`. The functional "coefficient of `X^{c_k}`"
  agrees on `Y` with the Library's `weightedCount` for the indicator `labelWeight c_k` of
  the labels of `c_k`. By `apply_eq_of_coeff` it suffices to compare them on each basis
  class `c'` occurring in `Y`. Such `c'` is a label of some `b'` (exhaustion) with
  `b' ≼ a₀` and `b' ≠ a₀` (as in `poly_basisClass`). If `c'` is a label of `c_k`, both
  sides are `1` (`poly_basisClass`). Otherwise the right side is `0`; if the left side
  were nonzero, `poly_basisClass` for `b'` would give `c_k ≼ b'`, and
  `eq_adj_of_rankLE` would give `b' = c_k`, so `c'` would be a label of `c_k`. So the
  coefficient is minus the number of labels of `c_k` in `Y`. The labels of `c_k` are not
  labels of `a₀` (`eq_of_isLabel`), so this number equals that in `ζ(a₀)`, which is at
  least that in `ζ(c_k)` (effectivity of `ζ(a₀) - ζ(c_k)`, `weightedCount_nonneg`),
  which is at least `1` for a label `L` of `c_k` from `exists_isLabel_of`
  (`one_le_coeff_zeta_of_isLabel`, `coeff_mul_le_weightedCount`).

### Primality

- `prime_basisClass_rect`: for `n > 0` and a label `c` of `rect σ n e`, the basis class
  `[c]` is prime in `R`. Primality transfers along the ring isomorphism `segmentEquiv`
  (`MulEquiv.prime_iff`), so it suffices that `Q = poly [c]` is prime in
  `ℤ[segments]`. Apply `prime_of_adjacent` with variables `s j = Δ_j = seg σ j e`
  (injective by `seg_injective`), weight `S ↦ S.length` (positive), common weight
  `D = e + 1`, and total weight `W = card (cuspidalContent a₀)`:
  - weighted homogeneity: every monomial `μ` of `Q` has `toMultiset μ ≼ a₀`
    (`poly_basisClass`), hence the same cuspidal content, and its weight is the size of
    that content (`weight_toFinsupp`);
  - `h0`: the coefficient of `X^{a₀} = ∏_{j<n} X_{Δ_j}` (`toFinsupp_rect`) is `1`
    (`poly_basisClass`);
  - `h1`: every monomial has exponent at most `1` at each `X_{Δ_j}`, by Tadić's
    Lemma 3.4 (`count_le_one_of_rankLE`);
  - `h2`: for `k + 1 < n`, the monomial `X^{c_k}` occurs (`coeff_poly_adj_ne_zero`), has
    exponent `0` at `X_{Δ_k}`, `X_{Δ_(k+1)}` and `1` at the other `X_{Δ_j}`
    (`count_adj_left`, `count_adj_right`, `count_adj_of_ne`), and no submonomial free of
    the `X_{Δ_j}` has weight `e + 1` (`weight_ne_of_le_adj`).
- `tadicRectangleSoclePrime`: given `ρ, n, d, hd, 0 < n, N, π`, the socle hypothesis and
  `hπ`, the class of `π` is a label of `tadicMultisegment ρ n d hd`
  (`isLabel_of_isZelevinskySocle`), which equals
  `rect (ν^(-(n-1)/2-(d-1)/2) ρ) n (d-1)` (`tadicMultisegment_eq_rect`).
  `prime_basisClass_rect` makes its basis class prime, and the Library's
  `basisClass_irreducibleIsoClass` identifies that basis class with
  `gradedInclusion F T N (finiteLengthClass N F.Carrier π _)`. The finite-length
  witness there is the one derived from irreducibility; it agrees with the given `hπ`
  by proof irrelevance, so the final `rwa` closes the goal.

The proof uses neither unitarity of `ρ` nor any restriction on `n, d` beyond `n, d > 0`.
All representations, cuspidal data and segments are at universe `max uF uV`, as in the
statement.
