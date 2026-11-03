# Lemma II.3.1: `1 + σ(m u)` and `1 + sup(σ(m), σ(u))`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SigmaProduct`, namespace
`Langlands.HarishChandraSchwartz`. It imports the published modules `ConstantTermBound`
(`SigmaProductBound`, the second inequality of Lemma II.3.1 as a Prop) and `Height`
(`entryNorm`, `glNorm`, `height`, `height_nonneg`, `height_mul_le`, `height_inv`,
`glNorm_mul_le`, `one_le_glNorm`, `glNorm_pos`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- I.1 (printed p. 242, PDF p. 8): `τ : G → GL_n(F)` is an algebraic embedding, `‖g‖` is
  the largest absolute value of an entry of `τ(g)` or of `τ(g)^{-1}`, and `σ = log ‖·‖`
  (the module `Height`).
- Lemma II.3.1 (printed pp. 254–255, PDF pp. 20–21): for a semi-standard `P = M U` there
  are `C_1, C_2 > 0` with
  `C_1 (1 + σ(m u)) ≤ 1 + sup(σ(m), σ(u)) ≤ C_2 (1 + σ(m u))` for `m ∈ M`, `u ∈ U`.
  Proof: the first inequality follows from `σ(m u) ≤ σ(m) + σ(u)`. Fix `a ∈ A_M` with
  `|α(a)|_F < 1` for `α ∈ Δ(P)`; conjugating `τ` ("ce qui n'a pas d'incidence sur
  l'assertion"), `τ(a)` is diagonal with entries of increasing absolute value; for the
  corresponding block decomposition `n = n_1 + ⋯ + n_t` and the block upper triangular
  `P' = M' U'` of `GL_n`, `τ(M) ⊂ M'` (since `M` commutes with `a`) and `τ(U) ⊂ U'`
  (since `Ad(a)` contracts `U`). Then the nonzero entries of `τ(m)` are entries of
  `τ(m u)`, so `σ(m) ≤ σ(m u)`. If `σ(m) ≥ σ(u)/2`, `sup(σ(m), σ(u)) ≤ 2 σ(m u)`; if
  `σ(m) < σ(u)/2`, one uses `σ(u) ≤ σ(m^{-1}) + σ(m u)` and `σ(m) = σ(m^{-1})`.

## Scope: abstract data and explicit hypotheses

`G` is an arbitrary group, `M` and `U` are subgroups, and `σ : G → ℝ` is arbitrary in the
deduction part. In the last part `σ = height τ` for a homomorphism `τ : G →* GL ι F` over
a normed field `F` with an ultrametric absolute value, `ι` finite and nonempty. The block
form of `τ(M)` and `τ(U)` after conjugation by some `x ∈ GL ι F` is an explicit
hypothesis: the module does not construct `a`, does not diagonalize `τ(a)`, and does not
prove that `τ(M)` and `τ(U)` take that form for Waldspurger's `P = M U`.

## Definitions

- `IsBlockDiagonal b A : Prop`, for `b : ι → β` with `β` linearly ordered and
  `A : Matrix ι ι F`: `A i j = 0` whenever `b i ≠ b j` (block diagonal for the blocks
  `b^{-1}(β)`).
- `IsBlockUnipotent b A : Prop`: `A i j = δ_{ij}` whenever `b j ≤ b i` (the identity on
  the diagonal blocks and zero below them: block upper unitriangular for the order of
  the blocks).

## Results

- `IsBlockDiagonal.mul_apply`, `IsBlockDiagonal.mul_apply'`: for `A` block diagonal, `N`
  block unipotent and `b i = b j`, `(A N) i j = A i j` and `(N A) i j = A i j`.
- `IsBlockDiagonal.entryNorm_le_mul`, `IsBlockDiagonal.entryNorm_le_mul'`: hence
  `entryNorm A ≤ entryNorm (A N)` and `entryNorm A ≤ entryNorm (N A)`.
- `glNorm_le_glNorm_mul`: for `m, n ∈ GL ι F` with `m, m^{-1}` block diagonal and
  `n, n^{-1}` block unipotent, `‖m‖ ≤ ‖m n‖` (Waldspurger's "les coefficients non nuls de
  `τ(m)` sont des coefficients de `τ(mu)`", applied also to the inverses).
- `one_add_mul_le_two_mul` (first inequality): for `σ ≥ 0` subadditive,
  `1 + σ(m u) ≤ 2 (1 + sup(σ(m), σ(u)))`.
- `sigmaProductBound_of_le_mul` (second inequality): for `σ ≥ 0` subadditive with
  `σ(g^{-1}) = σ(g)` and `σ(m) ≤ σ(m u)` for `m ∈ M`, `u ∈ U`,
  `SigmaProductBound M U σ` with constant `1/2`.
- `SigmaProductBound.of_le_add`: if `σ ≤ σ' + c` and `σ' ≤ σ + c` with `c ≥ 0` and
  `σ, σ' ≥ 0`, then `SigmaProductBound M U σ'` implies `SigmaProductBound M U σ` (with
  constant `C/(1 + c)^2`). This is the precise form of "conjuguer le plongement `τ` n'a pas
  d'incidence".
- `height_conj_le`: `height (conj x ∘ τ) ≤ height τ + log(‖x‖ ‖x^{-1}‖)`.
- `sigmaProductBound_height` (Lemma II.3.1 for `σ = height τ`): if there are
  `x ∈ GL ι F` and an ordered block decomposition `b` with `x τ(m) x^{-1}` block diagonal
  for all `m ∈ M` and `x τ(u) x^{-1}` block unipotent for all `u ∈ U`, then
  `SigmaProductBound M U (height τ)`.

## Proof notes

The proofs follow Waldspurger's. For the matrix fact, in `(A N) i j = Σ_k A i k N k j` with
`b i = b j`, the terms with `b k ≠ b i` vanish because `A` is block diagonal, and for
`b k = b i` the factor `N k j` is `δ_{kj}`; similarly for `N A`. For the inverse,
`(m n)^{-1} = n^{-1} m^{-1}`, which is why the hypotheses include the inverses (for
`τ(M)`, `τ(U)` they follow from `M`, `U` being subgroups). The deduction is the two cases
of Waldspurger, written as `sup(σ(m), σ(u)) ≤ 2 σ(m u)`. For the conjugation, the bound
`‖x A x^{-1}‖ ≤ ‖x‖ ‖A‖ ‖x^{-1}‖` (`glNorm_mul_le`) is applied to `τ` and to
`conj x ∘ τ` with `x^{-1}`.

## Open obligations

For Waldspurger's `G` and semi-standard `P = M U`: the choice of `a ∈ A_M`, the
diagonalization of `τ(a)` (split torus), and the inclusions `τ(M) ⊂ M'`, `τ(U) ⊂ U'` in
the block form above are not proved here.
