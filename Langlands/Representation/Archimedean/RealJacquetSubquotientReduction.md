# Harish-Chandra's subquotient theorem and the nonvanishing of the real Jacquet module

Lean module: `Langlands.Representation.Archimedean.RealJacquetSubquotientReduction`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier).

## Setting

The objects are as in the Library modules `RealJacquetReduction` and
`RealJacquetFiniteDimensional`. A `(𝔤𝔩_n(ℝ), O(n))`-module is a representation `ρ` of
`Matrix.unitaryGroup (Fin n) ℝ` (`O(n)`) on a complex vector space `V`, together with a complex
Lie algebra map `π : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ → End_ℂ V`, satisfying
`IsRealGKModule n ρ π`. `IsIrreducibleGKModule` and `IsAdmissibleGKModule` are the Library's
irreducibility and admissibility. `realJacquetSubspace n π` is `𝔫V`, the span of the vectors
`π(1 ⊗ X) v` with `X` strictly upper triangular.

The principal series of `GL_n(ℝ)` for the upper triangular Borel subgroup `B` (the minimal
parabolic subgroup) is the Library's `realStandardModule n (cs.map RealBlock.character)`, for a
list `cs : List RealCharacterData` of length `n`. Since the list has no induction blocks, the
Fourier-coefficient condition in `realStandardModule` is vacuous, and this is the Library's
smooth principal series `principalSeries ℝ n (realPositionCharacter (cs.map
RealBlock.character))`: the smooth functions `f` on `GL_n(ℝ)` with
`f(diag(a) u g) = principalSeriesCharacter(a) f(g)` for `u` upper unipotent, where
`principalSeriesCharacter(a) = ∏ᵢ χᵢ(aᵢ) |aᵢ|^((n-1)/2 - i)` is the product of the characters
`χᵢ = sgn^ε |·|^t` of the list with the normalizing shift `δ_B^{1/2}`. `GL_n(ℝ)` acts by right translation
(`Whittaker.rightTranslation`) and `𝔤𝔩_n(ℝ)` by right derivatives (`rightDerivative`, taken with
the matrix model `matrixModel ℝ n` of `GL_n(ℝ)`). `kFiniteFunctions V (unitaryCompact ℝ n)` is
the space of `O(n)`-finite functions of `V`; it carries the `(𝔤, K)`-module of the principal
series. A function of an element `k : unitaryCompact ℝ n` is evaluated through `ρ` at the
element `⟨((k : GL_n(ℝ)) : Matrix), k.2⟩` of `Matrix.unitaryGroup (Fin n) ℝ`, as in the
Library's `IsRealStandardIntertwiner` and `IsRealStandardEmbedding`.

## Definitions and statements

* `IsRealSubquotientMap n ρ π W T`, for a subspace `W` of the functions `GL_n(ℝ) → ℂ` and a
  linear map `T : W → V`, says that `T` is a `(𝔤, K)`-intertwiner:
  - for every `k : unitaryCompact ℝ n` and `w ∈ W`, the right translate of `w` by `k` lies in
    `W`, and `T` sends it to `ρ(k)(T w)`;
  - for every real matrix `X` and `w ∈ W`, the right derivative of `w` along `X` lies in `W`,
    and `T` sends it to `π(1 ⊗ X)(T w)`.

  This is the Library's `IsRealStandardIntertwiner` with the `O(n)`-finite functions of a
  standard module replaced by an arbitrary space `W`. In particular `W` is stable under right
  translation by `O(n)` and under right derivatives, and so is `ker T`.

* `RealPrincipalSeriesSubquotientStatement` (Harish-Chandra's subquotient theorem for
  `GL_n(ℝ)`): for every `n`, every complex vector space `V : Type uV` and maps `ρ`, `π` with
  `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, there are a
  list `cs : List RealCharacterData` with `cs.length = n`, a subspace `W` of the functions on
  `GL_n(ℝ)` with
  `W ≤ kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n)`,
  and a linear map `T : W → V` that is surjective and satisfies `IsRealSubquotientMap n ρ π W T`.
  So `V` is isomorphic to the subquotient `W / ker T` of the `(𝔤, K)`-module of the principal
  series: `ker T ⊆ W` are `(𝔤, K)`-submodules and `T` induces a `(𝔤, K)`-isomorphism
  `W / ker T ≅ V`.

* `RealJacquetNonvanishingSubquotientReductionStatement`:
  `RealPrincipalSeriesSubquotientStatement.{uV} → RealJacquetNonvanishingStatement.{uV}`. The
  subquotient theorem implies the nonvanishing of the Jacquet module, `𝔫V ≠ V` for every
  irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `V`.

Neither statement is proved in this module.

## Proved results

* `injective_of_isRealStandardEmbedding`: if `(ρ, π)` is irreducible and
  `B : V → kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` is nonzero and
  satisfies `IsRealStandardEmbedding n ρ π ds B`, then `B` is injective. Proof: `ker B` is a
  `(𝔤, K)`-submodule. It is `ρ(k)`-stable: an element `k` of `Matrix.unitaryGroup` comes from the
  element `⟨Unitary.toUnits k, k.2⟩` of `unitaryCompact ℝ n`, and `B(ρ(k) v)` is the right
  translate of `B v = 0`. It is `π(X)`-stable for every `X ∈ ℂ ⊗ 𝔤𝔩_n(ℝ)`: by induction on
  `X` (`TensorProduct.inductionOn`), using `c ⊗ Y = c • (1 ⊗ Y)` and that `B(π(1 ⊗ Y) v)` is
  the right derivative of `B v = 0`, which is `0` (`mfderiv_const`). By irreducibility
  `ker B = ⊥` or `ker B = ⊤`, and `ker B = ⊤` would mean `B = 0`.

* `realPrincipalSeriesSubquotient_of_subrepresentation`:
  `RealPrincipalSeriesSubrepresentationStatement.{uV} → RealPrincipalSeriesSubquotientStatement.{uV}`.
  Proof: take the embedding `B` given by the subrepresentation theorem, injective by the
  previous lemma, and let `f` be `B` followed by the inclusion into functions. Take `W` to be
  the range of `f` and `T` the inverse of the linear isomorphism `V ≃ range f`
  (`LinearEquiv.ofInjective`). Then `W` lies in the `O(n)`-finite functions of the principal
  series, `T` is surjective, and the two clauses of `IsRealSubquotientMap` follow from the two
  clauses of `IsRealStandardEmbedding`: the right translate of `f v` by `k` is `f(ρ(k) v)`, and
  its right derivative along `X` is `f(π(1 ⊗ X) v)`.

So the subquotient statement is no stronger than Casselman's subrepresentation theorem, the
target of this line of work. The three results use only `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

`RealPrincipalSeriesSubquotientStatement` is Harish-Chandra's subquotient theorem, specialized
to `GL_n(ℝ)`, `K = O(n)` and the minimal parabolic subgroup `B`, in algebraic form for
`(𝔤, K)`-modules. Wallach (1979, 4.13) cites it as "the subquotient theorem (Harish-Chandra [3],
Lepowsky [16], Rader [18])". Wallach's reference [3] is Harish-Chandra, *Representations of
semi-simple Lie groups. II*, Trans. Amer. Math. Soc. 76 (1954), 26–65; [16] is J. Lepowsky,
*Algebraic results on representations of semisimple Lie groups*, Trans. Amer. Math. Soc. 176
(1973), 1–44; [18] is C. Rader, Thesis, University of Washington, 1970. None of the three is
in the project's literature and none was read for this statement; the formulation follows
Wallach's description of the principal series in 4.7–4.11 and his citation in 4.13. For the minimal parabolic
`P₀ = M₀^W N₀` of `GL_n(ℝ)` (Wallach's `M₀^W` is the full diagonal group, our `M₀A₀`), an
irreducible representation `σ` of `M₀^W` is a character of `(ℝ^×)^n`, so Wallach's principal
series `V(P₀, σ)` (4.7–4.11) are the `(𝔤, K)`-modules of the Library's
`realStandardModule n (cs.map RealBlock.character)` with `cs.length = n`. Wallach realizes
`I(P, σ)` on functions with `f(kp) = δ_P(p)^{-1/2} σ(p)^{-1} f(k)` and `G` acting by left
translation; `f ↦ (g ↦ f(g⁻¹))` turns this into the Library's convention, with left
`B`-equivariance and right translation. The statement asks for some `cs`, so the
normalization of the inducing character does not matter.

`RealJacquetNonvanishingSubquotientReductionStatement` records Wallach's remark in 4.13 that
4.14 can be proved using "the subquotient theorem ... combined with a technique of Casselman
using the asymptotic expansion of matrix entries of admissible representations (cf.
Miličić [17])". Here it is only the part 4.14 (1), `V ≠ 𝔫V`, for the minimal parabolic
`(P₀, A₀)` of `GL_n(ℝ)` and irreducible admissible `V`, which is the Library's
`RealJacquetNonvanishingStatement`. Wallach states 4.14 (1) for all admissible `V`; the
Library statement only asks it for irreducible admissible `V`. The argument Wallach points to is
not formalized here. In outline: if `𝔫V = V` with `V ≅ W/ker T`, pair `W` with a `K`-finite
vector `ψ` of the dual principal series that annihilates `ker T` but not all of `W`; then the
matrix coefficients `g ↦ ∫_K w(κ g) ψ(κ) dκ` would decay faster than any exponential along the
negative chamber of the diagonal torus, while they satisfy a first-order linear system there.
This forces them to vanish, which contradicts the choice of `ψ`.

## Sources

* N. R. Wallach, *Representations of reductive Lie groups*, in Automorphic Forms,
  Representations and L-Functions (Corvallis, 1977), Proc. Sympos. Pure Math. 33, part 1,
  AMS, 1979, pp. 71–86: 4.7–4.14, printed pp. 76–77 (PDF pp. 79–80 of the Corvallis Part I
  volume); references [3], [16], [17], [18] on printed pp. 85–86.
