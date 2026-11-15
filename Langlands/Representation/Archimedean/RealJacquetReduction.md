# Jacquet functionals of `(𝔤𝔩_n(ℝ), O(n))`-modules and Casselman's subrepresentation theorem

Lean module: `Langlands.Representation.Archimedean.RealJacquetReduction`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier).

## Setting

A `(𝔤𝔩_n(ℝ), O(n))`-module consists of a representation `ρ` of
`Matrix.unitaryGroup (Fin n) ℝ` (that is, `O(n)`) on a complex vector space `V` and a complex
Lie algebra map `π : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ → End_ℂ V`, satisfying the Library's
compatibility predicate `IsRealGKModule n ρ π`. `IsIrreducibleGKModule` and
`IsAdmissibleGKModule` are the Library's irreducibility (which includes `V ≠ 0`) and
admissibility.

The minimal parabolic subgroup of `GL_n(ℝ)` is the upper triangular Borel subgroup
`B = M₀A₀N₀`. Here `M₀ = B ∩ O(n)` is the group of diagonal sign matrices, `A₀` the positive
diagonal matrices and `N₀` the upper unipotent matrices. The real Lie algebra `𝔫₀` of `N₀` is
the strictly upper triangular real matrices; its complexification is `𝔫 = ℂ ⊗_ℝ 𝔫₀`.

The target statement `RealPrincipalSeriesSubrepresentationStatement` (Library module
`RealPrincipalSeriesQuotientReduction`) asks for every irreducible admissible module a list of
`n` real characters and a nonzero intertwining map `B` (`IsRealStandardEmbedding`) from `V`
into the `O(n)`-finite functions of `realStandardModule n` of these characters.

## Definitions

* `realJacquetSubspace n π : Submodule ℂ V` is the complex span of the vectors
  `π(1 ⊗ X) v`, where `v ∈ V` and `X` is a strictly upper triangular real matrix
  (`X i j = 0` whenever `j ≤ i`). The `1 ⊗ X` span `𝔫` over `ℂ` and `π` is `ℂ`-linear, so
  this is `𝔫V`, Wallach's `n₀V` (Wallach 1979, 4.14 and 4.16); `V/𝔫V` is the Jacquet module
  along the minimal parabolic.

* `signReflection n j : Matrix.unitaryGroup (Fin n) ℝ` is the diagonal matrix
  `s_j = diag(1, …, 1, -1, 1, …, 1)` with `-1` at position `j`. These generate `M₀`.

* `IsRealJacquetFunctional n ρ π ℓ a e`, for `ℓ : V →ₗ[ℂ] ℂ`, `a : Fin n → ℂ` and
  `e : Fin n → Fin 2`, means:
  1. `ℓ(π(1 ⊗ X) v) = 0` for every strictly upper triangular real `X` and every `v`, that is,
     `ℓ` vanishes on `𝔫V`;
  2. for every position `j` and every `v`, `ℓ(π(1 ⊗ E_jj) v) = a_j ℓ(v)`, where
     `E_jj = Matrix.single j j 1`, and `ℓ(ρ(s_j) v) = (-1)^{e_j} ℓ(v)`.

  So `ℓ` is a linear form on `V/𝔫V` that is an eigenvector of the transposed actions of
  `𝔞₀` (spanned by the `E_jj`) and of `M₀`. It is the evaluation at `1` of an intertwining map
  into a principal series (Frobenius reciprocity, below).

**Normalization.** A `RealCharacterData` `c` with `exponent` `t` and `parity` `e ∈ {0, 1}`
is the character `x ↦ sgn(x)^e |x|^t` of `ℝˣ` (`RealBlock.character`). The Library's
`principalSeriesCharacter` multiplies the character at position `j` by
`|x|^{(n-1)/2 - j}`, which is `δ_B^{1/2}`. So the function on `B` defining the principal
series of `c_0, …, c_{n-1}` has derivative `t_j + (n - 1)/2 - j` along `E_jj` at `1` and
takes the value `(-1)^{e_j}` at `s_j`. For an embedding `B` into that principal series, the
functional `ℓ = ev₁ ∘ B` is therefore a real Jacquet functional with
`a_j = t_j + (n - 1)/2 - j` and signs `e_j`.

## Statements

* `RealJacquetModuleFiniteStatement`: for every irreducible admissible
  `(𝔤𝔩_n(ℝ), O(n))`-module, `V ⧸ realJacquetSubspace n π` is finite-dimensional and
  `realJacquetSubspace n π ≠ ⊤`.

  Source: Wallach 1979, 4.14 (`V ≠ 𝔫V`, and `V/𝔫V` is finitely generated over
  `(𝔪, K ∩ M)`) together with 4.15–4.16 (for the minimal parabolic this gives
  `1 ≤ dim V/𝔫₀V < ∞`), specialized to `G = GL_n(ℝ)`, `K = O(n)`, `P₀ = B`. This is the
  real counterpart of the Library's `ComplexJacquetModuleFiniteStatement`.

* `RealJacquetFrobeniusStatement`: let `(ρ, π)` be a `(𝔤𝔩_n(ℝ), O(n))`-module
  (`IsRealGKModule`; irreducibility and admissibility are not assumed) and `ℓ ≠ 0` a real
  Jacquet functional with exponents `a` and signs `e`. Then there are
  `c : Fin n → RealCharacterData` with `(c j).parity = e j` and
  `(c j).exponent + (n - 1)/2 - j = a j` for every `j`, and a nonzero
  `B : V →ₗ[ℂ] kFiniteFunctions (realStandardModule n ((List.ofFn c).map RealBlock.character))
  (unitaryCompact ℝ n)` with `IsRealStandardEmbedding n ρ π _ B`.

  Source: Frobenius reciprocity, Wallach 1979, 4.16–4.17 (the map `C(v)(k) = μ(k⁻¹ v)` for
  `μ` in the dual of `V/𝔫₀V`), as used in the proof of Theorem 4.18, specialized to
  `GL_n(ℝ)`, its Borel subgroup and one-dimensional representations of `M₀A₀`. Wallach's
  induced representations use left translation and `f(kp) = δ^{-1/2}σ(p)^{-1}f(k)`; the
  Library's `principalSeries` uses right translation and `f(bg) = χδ^{1/2}(b) f(g)`, which is
  the same after `g ↦ g⁻¹`. In the Library's convention the map is
  `B(v)(b k) = χδ^{1/2}(b) ℓ(ρ(k) v)` for `b ∈ B`, `k ∈ O(n)`. This is well defined because
  `ℓ ∘ ρ(m) = χ(m) ℓ` for `m ∈ M₀ = B ∩ O(n)`. The exact form above (exponents of `ℓ` read
  through the normalization of the previous section) is ours.

* `RealPrincipalSeriesSubrepresentationJacquetReductionStatement`:
  `RealJacquetModuleFiniteStatement → RealJacquetFrobeniusStatement →
  RealPrincipalSeriesSubrepresentationStatement`, all at universe `uV`. Provenance: derived;
  it is the outline of Wallach's proof of Theorem 4.18 for `GL_n(ℝ)`. Only the reduction
  itself is proved here; the two antecedents remain open.

## Proof of the reduction (`realPrincipalSeriesSubrepresentationJacquetReduction`)

The theorem
`realPrincipalSeriesSubrepresentationJacquetReduction :
RealPrincipalSeriesSubrepresentationJacquetReductionStatement.{uV}` is proved as follows.

1. **Operators on `V/𝔫V`.** The family `jacquetOp ρ π : Fin n ⊕ Fin n → End V` consists of
   `π(1 ⊗ E_jj)` (left summand) and `ρ(s_j)` (right summand).
   * For `X` strictly upper triangular, `E_jj X − X E_jj` is again strictly upper triangular
     (`real_single_mul_strict_sub_mem`), and `π(1 ⊗ ·)` turns matrix commutators into
     operator commutators (`real_map_commutator`, from `LieHom.map_lie` and
     `LieAlgebra.ExtendScalars.bracket_tmul`). So `π(1 ⊗ E_jj)` preserves `𝔫V`.
   * By the fourth clause of `IsRealGKModule`, `ρ(s_j) π(1 ⊗ X) = π(1 ⊗ s_j X s_jᵀ) ρ(s_j)`,
     and `s_j X s_jᵀ` only changes signs of entries (`signReflection_conj_apply`), so it is
     strictly upper triangular when `X` is. So `ρ(s_j)` preserves `𝔫V`
     (`jacquetOp_mem`).
   * The operators commute (`jacquetOp_commute`): the `E_jj` commute; `s_j E_ll s_jᵀ = E_ll`
     (`signReflection_conj_single`), so `ρ(s_j)` commutes with `π(1 ⊗ E_ll)` by the same
     clause; and the `s_j` commute with each other (`signReflection_mul_comm`).

   They induce commuting endomorphisms `jacquetQuotOp` of `V/𝔫V`
   (`jacquetQuotOp_commute`), whose transposes `jacquetQuotDualOp` on `(V/𝔫V)^*` commute too
   (`jacquetQuotDualOp_commute`).

2. **A Jacquet functional (`exists_isRealJacquetFunctional`).** By
   `RealJacquetModuleFiniteStatement`, `V/𝔫V` is finite-dimensional and nonzero, so its dual
   is too. The Library's `exists_common_eigenvector_of_commute` (from
   `ComplexJacquetReduction`) gives a nonzero common eigenvector `w` of all
   `jacquetQuotDualOp`, with eigenvalues `c`. Then `ℓ = w ∘ mkQ` is nonzero, vanishes on
   `𝔫V`, and satisfies `ℓ ∘ π(1 ⊗ E_jj) = c(inl j) ℓ` and `ℓ ∘ ρ(s_j) = c(inr j) ℓ`.
   Since `s_j² = 1` (`signReflection_mul_self`), applying the second identity twice to a
   vector with `ℓ(v) ≠ 0` gives `c(inr j)² = 1`, so `c(inr j) = (-1)^{e_j}` for some
   `e_j ∈ Fin 2` (`exists_fin_two_of_sq_eq_one`). Thus `ℓ` is a nonzero real Jacquet
   functional with exponents `a_j = c(inl j)` and signs `e`.

3. **Embedding.** `RealJacquetFrobeniusStatement` applied to `ℓ` gives `c` and a nonzero `B`
   with `IsRealStandardEmbedding`; the list `List.ofFn c` has length `n`
   (`List.length_ofFn`), which is the conclusion of
   `RealPrincipalSeriesSubrepresentationStatement`.

## References

* N. R. Wallach, *Representations of reductive Lie groups*, in Automorphic Forms,
  Representations and L-Functions (Corvallis, 1977), Proc. Sympos. Pure Math. 33, part 1,
  AMS, 1979, pp. 71–86. Used: 4.7–4.8 (p. 77), 4.14–4.18 (pp. 77–78). Library source ID
  `wallach-1979-representations-reductive-lie-groups`.
