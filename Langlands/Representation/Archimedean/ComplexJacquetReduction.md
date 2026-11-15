# Jacquet functionals of `(𝔤𝔩_n(ℂ), U(n))`-modules and the ordering of their exponents

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetReduction`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier).

## Setting

A `(𝔤𝔩_n(ℂ), U(n))`-module consists of a representation `ρ` of
`Matrix.unitaryGroup (Fin n) ℂ` on a complex vector space `V` and a complex Lie algebra map
`π : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ → End_ℂ V`, satisfying the Library's compatibility
predicate `IsComplexGKModule n ρ π`. The complexified Lie algebra of
`GL_n(ℂ)` (viewed as a real group) is `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`. `IsIrreducibleGKModule` and
`IsAdmissibleGKModule` are the Library's irreducibility and admissibility.

The minimal parabolic subgroup of `GL_n(ℂ)` is the upper triangular Borel subgroup
`B = M₀A₀N₀`. Here `M₀` is the diagonal unitary matrices, `A₀` the positive real diagonal
matrices and `N₀` the upper unipotent matrices. Its real Lie algebra `𝔫₀` is the strictly upper
triangular complex matrices, and its complexification is `ℂ ⊗_ℝ 𝔫₀`.

## Definitions

* `complexJacquetSubspace n π : Submodule ℂ V` is the complex span of the vectors
  `π(1 ⊗ X) v`, where `v ∈ V` and `X` is strictly upper triangular (`X i j = 0` whenever
  `j ≤ i`). The `1 ⊗ X` span `ℂ ⊗_ℝ 𝔫₀` over `ℂ` and `π` is `ℂ`-linear, so this subspace is
  `𝔫V` for the complexified nilradical `𝔫 = ℂ ⊗_ℝ 𝔫₀`. This is Wallach's `n₀V` (Wallach 1979,
  4.14 and 4.16), and `V/𝔫V` is the Jacquet module along the minimal parabolic.

* `IsComplexJacquetFunctional n π ℓ a b`, for `ℓ : V →ₗ[ℂ] ℂ` and `a b : Fin n → ℂ`, means:
  1. `ℓ(π(1 ⊗ X) v) = 0` for every strictly upper triangular `X` and every `v`, that is,
     `ℓ` vanishes on `𝔫V`;
  2. for every position `j` and every `v`, `ℓ(π(1 ⊗ E_jj) v) = a_j ℓ(v)` and
     `ℓ(π(1 ⊗ i E_jj) v) = b_j ℓ(v)`, where `E_jj = Matrix.single j j 1` and
     `i E_jj = Matrix.single j j Complex.I`.

  So `ℓ` is a linear form on `V/𝔫V` that is an eigenvector for the transposed action of the
  real diagonal Cartan subalgebra `𝔥₀ = 𝔞₀ ⊕ 𝔪₀`, where `𝔞₀` is spanned by the `E_jj` and
  `𝔪₀` by the `i E_jj`. The pair `(a, b)` is its weight.

**Normalization.** Take the principal series of the characters
`χ_j(z) = (z/|z|)^{l_j} |z|^{2 t_j}` (the Library's `ComplexCharacterData` with `weight` `l_j`
and `exponent` `t_j`). The Library's `principalSeriesCharacter` adds the shift
`|z|_ℂ^{(n-1)/2 - j} = |z|^{(n-1) - 2j}`, which is `δ_B^{1/2}`. So the function
`b ↦ ∏_j χ_j(b_jj) |b_jj|^{(n-1)-2j}` has derivative `a_j = 2 t_j + (n - 1) - 2j` along
`E_jj` and `b_j = i l_j` along `i E_jj`. These are the exponents of the Jacquet functional
`ℓ = ev₁ ∘ B` of an embedding `B` of `V` into that principal series. Under this
correspondence the condition `Re a_i + 2i ≤ Re a_j + 2j` is exactly `Re t_i ≤ Re t_j`.

## Statements

* `ComplexJacquetModuleFiniteStatement`: for every irreducible admissible
  `(𝔤𝔩_n(ℂ), U(n))`-module, `V ⧸ complexJacquetSubspace n π` is finite-dimensional and
  `complexJacquetSubspace n π ≠ ⊤`.

  Source: Wallach 1979, Theorem 4.14 (V ≠ 𝔫V; `V/𝔫V` is finitely generated over
  `(𝔪, K ∩ M)`) together with 4.15–4.16 (for the minimal parabolic this gives
  `1 ≤ dim V/𝔫₀V < ∞`), specialized to `G = GL_n(ℂ)`, `P₀ = B`.

* `ComplexJacquetRankOneStatement` (rank-one reordering). Let `ℓ ≠ 0` be a Jacquet functional
  with weight `(a, b)` on an irreducible admissible module, and let `j = i + 1` with
  `Re a_j + 2 < Re a_i`, which means `Re t_j < Re t_i`. Then there is a nonzero Jacquet
  functional `ℓ'` with weight `(a', b')` such that:
  - `a'_k = a_k` for `k ∉ {i, j}`;
  - `a'_i + a'_j = a_i + a_j`;
  - `Re a'_i ≤ Re a'_j + 2`, which means `Re t'_i ≤ Re t'_j`.

  Provenance: derived; it is not stated in this form in the literature. It is the rank-one
  case of the minimality argument in Wallach 1979, Lemma 5.13, for `GL_n(ℂ)`. Here is why it
  holds. Let `P` be the standard parabolic with Levi
  `GL_1^i × GL_2(ℂ) × GL_1^{n-i-2}`, the `GL_2` at positions `i, i+1`. Then
  `V/𝔫_P V` is an admissible finitely generated `(𝔪_P, K ∩ M_P)`-module (Wallach 4.14, 4.20),
  and `V/𝔫V = (V/𝔫_P V)/𝔫_{M}(V/𝔫_P V)` (Wallach 5.3). The functional `ℓ` lives on the
  generalized eigenspace of the center of `𝔪_P` with the eigenvalues of `ℓ`. That eigenspace
  has an irreducible quotient `W`, on which the center acts by the same scalars. The
  `GL_2(ℂ)` case of the ordered-functional statement below, applied to `W`, gives an ordered
  Jacquet functional of `W`. Pulled back to `V`, it is `ℓ'`. The hypothesis
  `Re a_j + 2 < Re a_i` is not needed for this argument. It only restricts the statement to the
  case the reduction uses.

* `ComplexOrderedJacquetFunctionalStatement` (J): every irreducible admissible
  `(𝔤𝔩_n(ℂ), U(n))`-module has a nonzero Jacquet functional `ℓ` with some weight `(a, b)`
  such that `Re a_i + 2i ≤ Re a_j + 2j` for all `i < j`, that is,
  `Re t_0 ≤ Re t_1 ≤ ⋯ ≤ Re t_{n-1}`.

  Source: this is the Jacquet-module form of the Langlands classification, subrepresentation
  form, for `GL_n(ℂ)`. Wallach 1979, 4.16–4.18 (Casselman's subrepresentation theorem via the
  map `C(v)(k) = μ(k⁻¹ v)`), Lemma 5.13 and Theorem 6.7. By Frobenius reciprocity, a nonzero
  functional of this kind is the same thing as a nonzero `(𝔤, K)`-map into the principal
  series with antidominant `Re t`. The formulation through functionals on `V/𝔫V` is ours.

* `ComplexOrderedJacquetReductionStatement`:
  `ComplexJacquetModuleFiniteStatement → ComplexJacquetRankOneStatement →
  ComplexOrderedJacquetFunctionalStatement`, all at universe `uV`. Provenance: derived; this
  is an intermediate reduction toward the Library's
  `ComplexLanglandsSubrepresentationStatement`. Only the reduction itself is proved here.
  The two antecedents remain open.

## Proof of the reduction (`complexOrderedJacquetReduction`)

The theorem `complexOrderedJacquetReduction : ComplexOrderedJacquetReductionStatement.{uV}`
is proved in the module as follows.

1. **The diagonal action on `V/𝔫V`.** For `D` diagonal and `X` strictly upper triangular, the
   commutator `[D, X] = DX − XD` is again strictly upper triangular
   (`single_mul_strict_sub_mem`). `π(1 ⊗ ·)` turns matrix commutators into operator
   commutators (`complex_map_commutator`, from `LieHom.map_lie` and
   `LieAlgebra.ExtendScalars.bracket_tmul`). Hence `π(1 ⊗ E_jj)` and `π(1 ⊗ i E_jj)` preserve
   `𝔫V` (`diag_mem_complexJacquetSubspace`) and induce endomorphisms `jacquetDiagOp` of
   `V/𝔫V`. They commute (`jacquetDiagOp_commute`) because diagonal matrices commute
   (`diagDirection_commute`). So do their transposes `jacquetDualOp` on the dual
   `(V/𝔫V)^*` (`jacquetDualOp_commute`).

2. **Jacquet functionals = common eigenvectors.** A common eigenvector `ℓ` of all
   `jacquetDualOp` gives the Jacquet functional `ℓ ∘ mkQ`
   (`isComplexJacquetFunctional_of_eigen`), which is nonzero when `ℓ` is
   (`comp_mkQ_ne_zero`). Conversely, every Jacquet functional factors as `ℓ' ∘ mkQ`. Its
   factor `ℓ'` satisfies `jacquetDualOp (false, j) ℓ' = a_j ℓ'`
   (`exists_eigen_of_isComplexJacquetFunctional`).

3. **Existence.** By `ComplexJacquetModuleFiniteStatement`, `V/𝔫V` is finite-dimensional and
   nonzero, so its dual is too. A finite family of pairwise commuting endomorphisms of a
   nonzero finite-dimensional complex space has a common eigenvector
   (`exists_common_eigenvector_of_commute`). The proof is by induction on the family: take an
   eigenvalue of the next operator restricted to the current subspace
   (`Module.End.exists_eigenvalue`) and pass to the intersection with that eigenspace, which
   is stable under all the operators. So a nonzero Jacquet functional exists.

4. **Finiteness of weights.** By step 2, each `a_j` of a nonzero Jacquet functional is an
   eigenvalue of `jacquetDualOp (false, j)` on the finite-dimensional dual. An endomorphism of
   a finite-dimensional space has finitely many eigenvalues
   (`Module.End.finite_hasEigenvalue`). So the set `E` of first weights `a` of nonzero Jacquet
   functionals is finite (`Set.Finite.pi`), and it is nonempty by step 3.

5. **Minimization.** Choose `a ∈ E` minimizing `P(a) = ∑_k (n − k) Re a_k`
   (`Set.exists_min_image`). It is enough to check the ordering at adjacent positions
   (`fin_le_of_adjacent_le`). Suppose `Re a_{i+1} + 2(i+1) < Re a_i + 2i` for some `i`. Then
   `ComplexJacquetRankOneStatement` gives `a' ∈ E` that agrees with `a` off `{i, i+1}`, with
   the same `Re a_i + Re a_{i+1}` and with `Re a'_i ≤ Re a'_{i+1} + 2`. Therefore
   `P(a') − P(a) = Re a'_i − Re a_i`. From `2 Re a'_i ≤ Re a_i + Re a_{i+1} + 2 < 2 Re a_i`,
   this is negative, which contradicts the minimality of `a`.

## References

* N. R. Wallach, *Representations of reductive Lie groups*, in Automorphic Forms,
  Representations and L-Functions (Corvallis, 1977), Proc. Sympos. Pure Math. 33, part 1,
  AMS, 1979, pp. 71–86. Used: 4.14–4.18 (printed pp. 77–78), 4.20–4.21, 5.3, 5.13
  (pp. 78–79), 6.7 (p. 80). Library source ID `wallach-1979-representations-reductive-lie-groups`.
