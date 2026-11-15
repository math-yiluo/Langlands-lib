# Proof of `RealJacquetFiniteGenerationStatement`

Module: `Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof` (namespace
`Langlands.Archimedean.RealJacquetFiniteGeneration`).

Main theorem: `Langlands.Archimedean.RealJacquetFiniteGeneration.realJacquetFiniteGeneration :
Langlands.Archimedean.RealJacquetFiniteGenerationStatement.{uV}`. The theorem uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

The section `SkewStability` was written by Worker 725.

## What is proved

`RealJacquetFiniteGenerationStatement` is stated in
`Langlands.Representation.Archimedean.RealJacquetFiniteDimensional`. Let `(ρ, π)` be an
irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module on `V` (`IsRealGKModule n ρ π`,
`IsIrreducibleGKModule ρ π`, `IsAdmissibleGKModule ρ`). The statement asks for a
finite-dimensional subspace `F ⊆ V` such that every subspace `S ⊇ F` stable under `π(1 ⊗ X)`
for all strictly upper triangular real `X` is all of `V`, i.e. `V = U(𝔫) F`.

## Notation

- `Mat n` is the type of real `n × n` matrices, `E a b` the matrix unit `Matrix.single a b 1`,
  and `D i = E i i`.
- `op π X = π(1 ⊗ X)` for a real matrix `X`. `wordOp π [X₁, …, X_r]` is the operator
  `op π X₁ ∘ ⋯ ∘ op π X_r` (the empty word gives the identity).
- `hᵢ = op π (D i)`. These operators commute (`op_D_commute`), so the subalgebra of
  `End_ℂ V` they generate is commutative, and `diagEval π : ℂ[x₁, …, xₙ] → End_ℂ V` is the
  algebra map `xᵢ ↦ hᵢ` (`diagEval`, `diagEval_X`).
- `IsStrictUpper X` means `X i j = 0` whenever `j ≤ i`.
- `carry F S` is the subspace of operators `A` with `A f ∈ S` for every `f ∈ F`.

## The finite-dimensional subspace

Choose `v ≠ 0` (irreducibility includes `Nontrivial V`). Let `F₀` be the span of the
`O(n)`-orbit of `v` (`FiniteVectors.orbitSpan ρ v`). It is finite-dimensional because every
vector is `O(n)`-finite (first clause of `IsRealGKModule`). The subspace of the statement is

`F = boxSpace π F₀ = ∑_{β ∈ {0, …, n-1}ⁿ} h^β F₀`,

a finite sum of images of `F₀` (`boxSpace`; finite-dimensional by
`Submodule.finiteDimensional_iSup`). `le_boxSpace` gives `F₀ ⊆ F` (take `β = 0`), and
`mem_boxSpace` gives `h^α f ∈ F` for `f ∈ F₀` and every exponent with `αᵢ < n` for all `i`.

## Proof outline

Fix `S ⊇ F` stable under `op π X` for strictly upper triangular `X`. The core claim
(`wordOp_mem_carry`) is that every word maps `F₀` into `S`. Granting it, let `W` be the span of
all vectors `wordOp π w f` with `f ∈ F₀` (`wordSpan`). Then:

- `W ⊆ S` (`wordSpan_le`).
- `W` is stable under `π`: `op π M (wordOp π w f) = wordOp π (M :: w) f`, and a general element
  of `ℂ ⊗_ℝ Mat n` is a sum of `c ⊗ M`, with `π(c ⊗ M) = c · op π M` (`op_tmul`,
  `op_apply_mem_wordSpan`, `apply_mem_wordSpan`).
- `W` is stable under `ρ`: the last clause of `IsRealGKModule`,
  `ρ(k) π(1 ⊗ X) = π(1 ⊗ k X kᵀ) ρ(k)`, gives
  `ρ(k) wordOp π w = wordOp π (w.map (X ↦ k X kᵀ)) ρ(k)` (`rho_wordOp`), and `F₀` is
  `ρ`-stable (`rho_mem_wordSpan`).
- `v ∈ W` (the empty word applied to `v ∈ F₀`).

By irreducibility `W = ⊥` or `W = ⊤`. The first is impossible since `v ≠ 0`. So `⊤ = W ⊆ S`.

## Stability of `F₀` under antisymmetric letters (section `SkewStability`)

`apply_skew_mem_of_rho_stable`: a subspace `F` stable under every `ρ(k)` is stable under
`op π Y` for every real `Y` with `Yᵀ = -Y`. Suppose `op π Y f ∉ F` for some `f ∈ F`. Choose a
linear functional `ℓ` vanishing on `F` with `ℓ(op π Y f) ≠ 0`
(`Submodule.exists_le_ker_of_notMem`). The curve `t ↦ exp(tY)` lies in `O(n)` because the
exponential of a skew-adjoint matrix is unitary (`skewCurve`,
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`). It equals `1` at `0`, and its entries have
derivative `Y` at `0` (`skew_hasDerivAt_entry`, `skew_hasDerivAt_exp_smul_zero`). The derivative
clause of `IsRealGKModule` says that `t ↦ ℓ(ρ(exp tY) f)` has derivative `ℓ(op π Y f)` at `0`.
This function is identically `0` because `F` is `ρ`-stable. By uniqueness of derivatives,
`ℓ(op π Y f) = 0`, a contradiction. The section uses the operator-norm topology on matrices and
`set_option backward.isDefEq.respectTransparency false`, both scoped to the section.

## The core claim: every word carries `F₀` into `S`

The proof is strong induction on the word length `d` (`wordOp_mem_carry`). The induction
hypothesis `hyp` says that every word of length `< d` lies in `carry F₀ S`. The hypotheses used
throughout are `hS` (`S` is stable under strictly upper triangular letters) and `hF` (`F₀` is
stable under antisymmetric letters).

1. **Reordering** (`wordOp_perm_sub_mem`). If `l₁` is a permutation of `l₂` and
   `|u| + |l₁| = d`, then `wordOp π (u ++ l₁) - wordOp π (u ++ l₂)` is a combination of words of
   length `d - 1`. The proof is induction on `List.Perm`. For an adjacent swap,
   `op π X · op π Y - op π Y · op π X = op π (XY - YX)` (`op_commutator`, from the Lie bracket
   on `ℂ ⊗_ℝ Mat n`), and the resulting word is one letter shorter.
2. **A strictly upper triangular letter** (`wordOp_mem_carry_of_upper`). Move it to the front
   with step 1. The rest of the word maps `F₀` into `S` by `hyp`, and the letter preserves `S`.
3. **An antisymmetric letter** (`wordOp_mem_carry_of_skew`). Move it to the end with step 1.
   The letter maps `F₀` into `F₀` by `hF`, and the rest of the word maps `F₀` into `S`.
4. **A letter `Z` with zero diagonal** (`wordOp_mem_carry_of_zeroDiag`). Write `Z = U + (Z - U)`
   with `U = upperPart Z`, `U i j = Z i j + Z j i` for `i < j` and `0` otherwise. `U` is strictly
   upper triangular and `Z - U` is antisymmetric (`transpose_sub_upperPart`). Both pieces are
   handled by steps 2 and 3.
5. **Reduction to diagonal words** (`wordOp_mem_carry_of_diag_prefix`). Expand the letters of
   a word, from left to right, in matrix units: `op π X = ∑_{a,b} X a b · op π (E a b)`
   (`op_eq_sum`). A unit `E a b` with `a ≠ b` has zero diagonal, which is step 4. A unit `E a a`
   extends the prefix of diagonal letters. So it suffices that every word `[D i₁, …, D i_d]`
   lies in `carry F₀ S`.
6. **Diagonal words** (`wordOp_diag_mem_carry`). Such a word is `h^γ = diagEval π (x^γ)` with
   `|γ| = d` (`wordOp_map_D`, `exists_monomial_of_list`). If every `γᵢ < n`, then
   `h^γ F₀ ⊆ F ⊆ S` (`mem_boxSpace`). Otherwise some `γᵢ ≥ n`, and `x^γ` lies in the
   polynomial subspace `J_d` described below (`monomial_mem_powerSumSpan`). Step 7 handles
   `J_d`.
7. **The subspace `J_d`** (`diagEval_mem_carry_of_mem_powerSumSpan`). `J_d = powerSumSpan n d`
   is spanned by the products `x^γ' p_l` with `l ≥ 1` and `|γ'| + l = d`, where
   `p_l = ∑ᵢ xᵢ^l` is the `l`-th power sum. By the Gelfand step below,
   `diagEval π (p_l) = c · 1 - Z` with `c ∈ ℂ` and `Z` in `zdSpan π l`, the span of words of
   length `l` with a letter of zero diagonal (`diagEval_psum`). Hence
   `diagEval π (x^γ' p_l) = c · h^γ' - h^γ' Z`. Since `l ≥ 1`, `h^γ'` is a word of length `< d`
   (`exists_list_of_monomial`), so `hyp` applies. `h^γ' Z` is a combination of words of length
   `d` with a zero-diagonal letter (`wordOp_mul_mem_zdSpan`), which step 4 handles
   (`zdSpan_le_carry`).

## Polynomial facts (section `Poly`)

`J_d` is stable under multiplication by monomials, with the degree adding
(`monomial_mul_mem_powerSumSpan`). A homogeneous `p` of degree `k` gives `p · p_l ∈ J_{k+l}`
when `l ≥ 1` (`mul_psum_mem_powerSumSpan`).

- `esymm_mem_powerSumSpan`: the elementary symmetric polynomial `e_k` lies in `J_k` for
  `k ≥ 1`. Newton's identity (`MvPolynomial.mul_esymm_eq_sum`) writes `k · e_k` as a
  combination of `e_a p_b` with `a + b = k`, `b ≥ 1`. `e_a` is homogeneous of degree `a`
  (`esymm_isHomogeneous`). Divide by `k ≠ 0` in `ℂ`.
- `X_pow_mem_powerSumSpan`: `xᵢⁿ ∈ J_n`. Evaluate Vieta's formula
  `∏_j (t + x_j) = ∑_k e_k t^{n-k}` (`MvPolynomial.prod_C_add_X_eq_sum_esymm`) at `t = -xᵢ`.
  The product vanishes (factor `j = i`), so `(-xᵢ)ⁿ = -∑_{k ≥ 1} e_k (-xᵢ)^{n-k}`, and each
  term lies in `J_n` by the previous item.
- `monomial_mem_powerSumSpan`: if `αᵢ ≥ n`, then `x^α = x^{α - n eᵢ} xᵢⁿ ∈ J_{|α|}`.

## Gelfand's central elements (sections `Gelfand` and `ZeroDiag`)

- `commute_trace_pow`: let `𝔈` be a square matrix over a ring whose entries satisfy
  `[𝔈 a b, 𝔈 i j] = δ_{bi} 𝔈 a j - δ_{ja} 𝔈 i b`. Then every entry `𝔈 a b` commutes with
  `trace(𝔈^l)`. Proof: `T = 𝔈 a b · I - E b a` commutes with `𝔈`. This is exactly the relation,
  entrywise. Hence `T` commutes with `𝔈^l`. Take traces: `trace(E b a 𝔈^l)` and
  `trace(𝔈^l E b a)` both equal `(𝔈^l) a b`, which leaves
  `𝔈 a b · trace(𝔈^l) = trace(𝔈^l) · 𝔈 a b`.
- `trace_gen_pow_mem_center`: in the universal enveloping algebra `U(𝔤)` of
  `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`, the matrix `gen n = (ι(1 ⊗ E i j))` satisfies these relations
  (`op_E_commutator`). So `trace(gen n ^ l)` commutes with every generator `ι(c ⊗ M)` (a
  combination of the entries, `op_eq_sum`), hence lies in the center. The induction over
  `U(𝔤)` is the Library's `InfinitesimalCharacter.envInduction`.
- `envelopingAction_trace_gen_pow`: `π` sends `trace(gen n ^ l)` to `trace(opMat π ^ l)`, where
  `opMat π = (op π (E i j))`.
- `opMat_pow_sub_mem`: `(opMat π ^ l) i j - δ_{ij} hᵢ^l ∈ zdSpan π l`, by induction on `l`.
  Expand `(opMat^{l+1}) i j = ∑_k (opMat^l) i k · op π (E k j)`. The difference terms stay in
  `zdSpan` after appending a letter (`mul_op_mem_zdSpan`). The remaining term `hᵢ^l op π (E i j)`
  is `hᵢ^{l+1}` if `i = j`. If `i ≠ j`, it is the word `[D i, …, D i, E i j]`, whose last letter
  has zero diagonal.
- `diagEval_psum`: an irreducible admissible module has an infinitesimal character (the
  Library's `InfinitesimalCharacter.realGKModuleInfinitesimalCharacter`), so
  `trace(opMat π ^ l) = c · 1`. Summing the diagonal case of the previous item over `i` gives
  `diagEval π (p_l) = ∑ᵢ hᵢ^l = c · 1 - Z` with `Z ∈ zdSpan π l`.

## Relation to the literature

Finite generation over `U(𝔫)` gives the finite-dimensionality half of Casselman's theorem
(Wallach 1979, 4.14 (2) and 4.16; see `RealJacquetFiniteDimensional`). A standard argument writes
`V = U(𝔤) F₀`, uses the decomposition `U(𝔤) = U(𝔫) U(𝔞) U(𝔨)`, and uses that `U(𝔞)` is a
finite module over the image of the center of `U(𝔤)` under the Harish-Chandra map. The proof
above is an elementary substitute for `𝔤𝔩_n` and does not follow that route. Gelfand's central elements `trace(E^l)` play the role of the
center, and Newton's and Vieta's identities show that the monomials `h^β`, `β ∈ {0, …, n-1}ⁿ`,
generate `ℂ[h₁, …, hₙ]` over the power sums. The reordering lemma replaces PBW.
