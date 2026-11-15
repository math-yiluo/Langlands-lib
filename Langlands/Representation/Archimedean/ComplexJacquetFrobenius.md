# Frobenius reciprocity for Jacquet functionals of `(𝔤𝔩_n(ℂ), U(n))`-modules

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetFrobenius`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier).

## Setting

* `IsComplexGKModule n ρ π` (Library, `GKModule`) is the Library's notion of a
  `(𝔤𝔩_n(ℂ), U(n))`-module: `ρ` is a representation of `Matrix.unitaryGroup (Fin n) ℂ` on
  a complex vector space `V`, and `π : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ End_ℂ V` is a
  map of complex Lie algebras.
* `IsComplexJacquetFunctional n π ℓ a b` (from `ComplexJacquetReduction`) says that
  `ℓ : V →ₗ[ℂ] ℂ` vanishes on `π(1 ⊗ X) V` for every strictly upper triangular `X`. It also
  says that, for every position `j`, `ℓ ∘ π(1 ⊗ E_jj) = a_j ℓ` and
  `ℓ ∘ π(1 ⊗ i E_jj) = b_j ℓ`.
* `ComplexCharacterData` (Library) is a continuous character
  `χ(z) = (z/|z|)^l |z|^{2t}` of `ℂˣ`, with fields `weight = l ∈ ℤ` and `exponent = t ∈ ℂ`.
* `complexStandardModule n ds` (Library, `StandardModule`) is the smooth principal series of
  the characters of the list `ds`. It consists of the `C^∞` functions `f` on `GL_n(ℂ)` with
  `f(diag(z) u g) = ∏_j χ_j(z_j) |z_j|^{(n-1)-2j} f(g)` for `u` upper unipotent; the factor
  `|z_j|_ℂ^{(n-1)/2 - j} = |z_j|^{(n-1)-2j}` is `δ_B^{1/2}`. `kFiniteFunctions … (unitaryCompact
  ℂ n)` is its subspace of `U(n)`-finite functions for right translation.
* `IsComplexStandardEmbedding n ρ π ds B` (Library, `ComplexLanglandsQuotientReduction`) says
  that `B` carries `ρ(k)` to right translation by `k ∈ U(n)` and `π(1 ⊗ X)`, for
  `X ∈ 𝔤𝔩_n(ℂ)`, to the right derivative along `X`.

## Statements

* `ComplexJacquetFrobeniusStatement` (FR). Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module on
  `V : Type uV` and `ℓ ≠ 0` a Jacquet functional with exponents `a`, `b`. There is no
  irreducibility or admissibility hypothesis. Then there are complex characters
  `d 0, …, d (n-1)` such that, for every `j`,
  - `2 (d j).exponent + (n - 1) - 2 j = a j`,
  - `i · (d j).weight = b j`,

  and a nonzero linear map `B` from `V` into the `U(n)`-finite functions of
  `complexStandardModule n (List.ofFn d)` with `IsComplexStandardEmbedding n ρ π
  (List.ofFn d) B`.

  **Normalization.** The intended map is
  `B(v)(β k) = ∏_j χ_j(β_jj) |β_jj|^{(n-1)-2j} · ℓ(ρ(k) v)` for `β` upper triangular and
  `k ∈ U(n)`, where `χ_j` is the character of `d j`. So `B(v)(1) = ℓ(v)`. Differentiating
  `B(v)` at `1` along `E_jj` gives `2 t_j + (n - 1) - 2j`, and along `i E_jj` it gives `i l_j`.
  These must be the exponents `a_j` and `b_j` of `ℓ = ev₁ ∘ B`, which is the pair of
  equations in the statement. In particular the statement asserts that `b_j ∈ iℤ`. This is a
  consequence and not a hypothesis. The functional `ℓ` is only assumed to be an eigenvector
  of the diagonal Lie algebra `𝔪₀` (all complex diagonal matrices). The integrality comes
  from the compact torus `⁰M₀ = M₀ ∩ U(n)` of diagonal unitary matrices, whose Lie algebra
  is `i·(real diagonal)`, through the `U(n)`-action that `IsComplexGKModule` ties to `π`.

  Source: Wallach 1979, 4.8, 4.15, 4.16 and Lemma 4.17 (printed p. 77, PDF p. 80), for
  `G = GL_n(ℂ)` and `K = U(n)`. We keep Wallach's notation for the groups. The minimal
  parabolic `P₀ = M₀ N₀` is the upper triangular Borel subgroup. Its Levi factor `M₀` is the
  full diagonal group `(ℂˣ)^n`, and `N₀` is the upper unipotent group. `M₀ = ⁰M₀ A₀`, where
  `⁰M₀ = M₀ ∩ K` (4.15) is the diagonal unitary torus and `A₀` is the group of positive real
  diagonal matrices. Characters of `M₀` are extended to `P₀` trivially on `N₀`. In Wallach's
  normalization `δ_{P₀}^{1/2}(β) = ∏_j |β_jj|^{(n-1)-2j}`.

  We use two distinct characters of `M₀`.
  * `σ_W` is the character on Wallach's quotient `W`. Here `W = ℂ` is the one-dimensional
    quotient of `V/𝔫₀V` given by `μ = ℓ`. On `W` the element `E_jj` acts by `a_j` and
    `i E_jj` by `b_j`. In Wallach's setting `W` is an `(𝔪₀, ⁰M₀)`-module and hence a
    representation of `M₀`. Here `σ_W` is the character of `M₀` with this differential. It
    exists because `b_j ∈ iℤ`, which is part of the conclusion (point 2 below).
  * `ξ = δ_{P₀}^{-1/2} σ_W` is the inducing character, which Wallach sets in 4.16.

  Wallach's induced representation (4.8) consists of the functions with
  `f(k p) = δ_{P₀}(p)^{-1/2} ξ(p)⁻¹ f(k)`, and `G` acts on it by left translation. In 4.16 he
  defines `C(v)(k) = μ(k⁻¹ · v)`, and Lemma 4.17 says that `C` intertwines the
  `𝔤`-actions. The Library's model uses right translation, and we pass to it by
  `F(g) = f(g⁻¹)`. For `β ∈ P₀` and `k ∈ K` this gives
  `F(β k) = f(k⁻¹ β⁻¹) = δ_{P₀}(β)^{1/2} ξ(β) μ(k · v) = σ_W(β) μ(k · v)`.
  So `F` lies in the Library's standard module of the characters `χ_j` with
  `ξ(diag(z)) = ∏_j χ_j(z_j)`: the Library characters `d j` encode the inducing
  character `ξ`. The factor `∏_j |β_jj|^{(n-1)-2j}` in the formula for `B` is
  `δ_{P₀}^{1/2}(β)`. The exponents of `σ_W = δ_{P₀}^{1/2} ξ` are `2 t_j + (n - 1) - 2j` along
  `E_jj` and `i l_j` along `i E_jj`, as computed above. Our formulation differs from
  Wallach's in three ways.
  1. The hypotheses are weaker. Wallach takes `V` admissible and finitely generated, so that
     `V/𝔫₀V` has an irreducible quotient. Here the functional `ℓ` is given.
  2. In Wallach the quotient `W` is an `(𝔪₀, ⁰M₀)`-module, where `⁰M₀ = K ∩ M₀`. Here only
     the Lie algebra `𝔪₀` acts on `ℓ`. So the character of the compact torus `⁰M₀`, and with
     it `b_j ∈ iℤ`, is part of the conclusion.
  3. The target is the Library's smooth principal series of the characters `d j` rather than
     the Hilbert space `H^{P₀, ξ}`, and `B` maps into its `U(n)`-finite part.

  This module states FR but does not prove it.

* `ComplexLanglandsSubrepresentationJacquetReductionStatement`:
  `ComplexJacquetFrobeniusStatement → ComplexOrderedJacquetFunctionalStatement →
  ComplexLanglandsSubrepresentationStatement`, all at universe `uV`. Here
  `ComplexOrderedJacquetFunctionalStatement` (from `ComplexJacquetReduction`) gives a
  nonzero Jacquet functional with `Re a_i + 2i ≤ Re a_j + 2j` for `i < j`, and
  `ComplexLanglandsSubrepresentationStatement` is the Library's subrepresentation form of the
  Langlands classification for `GL_n(ℂ)`. Provenance: derived. This is the combination of
  Wallach 1979, 4.16–4.18 with the ordering of exponents in Lemma 5.13 and Theorem 6.7,
  organized through the two statements above. The implication is ours.

## Proof of the reduction (`complexLanglandsSubrepresentationJacquetReduction`)

The theorem `complexLanglandsSubrepresentationJacquetReduction :
ComplexLanglandsSubrepresentationJacquetReductionStatement.{uV}` is proved in this module.
Let `(ρ, π)` be irreducible and admissible. The ordered Jacquet statement gives a nonzero
Jacquet functional `ℓ` with exponents `a`, `b` and the ordering above. FR gives characters
`d` and a nonzero embedding `B` into the standard module of `ds = List.ofFn d`, which has
length `n` (`List.length_ofFn`). The remaining condition is
`ds.Pairwise (Re ·.exponent ≤ Re ·.exponent)`. By `List.pairwise_ofFn` this means
`Re t_i ≤ Re t_j` for `i < j`. The real part of `a_j = 2 t_j + (n - 1) - 2j` is
`2 Re t_j + (n - 1) - 2j` (`re_two_mul_add_sub`). So `Re a_i + 2i ≤ Re a_j + 2j` reads
`2 Re t_i + (n - 1) ≤ 2 Re t_j + (n - 1)`, and `linarith` concludes.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
