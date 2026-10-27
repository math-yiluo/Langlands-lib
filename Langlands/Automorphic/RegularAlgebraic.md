# Infinitesimal characters and the regular algebraic type at infinity

This module defines when an actual automorphic realization of `GL_n` over a
number field `F` has an infinitesimal character. It also defines Clozel's
condition that this character is *regular algebraic*. Harris (1998) uses this
condition to define `Reg(n,E)`, and through it the class `U(n,E)` in the
conclusion of his Proposition 4.8. The condition applies to the Library's
full-operator realizations (`OperatorRealization F n`), their isomorphism
classes, and irreducible cuspidal classes
(`CuspidalOperatorRealization.IsoClass F r`, of rank `r + 1`).

The module only defines the conditions. It does not claim that a realization
has an infinitesimal character, that one with regular algebraic type exists, or
that the condition is equivalent to nonvanishing `(𝔤, K)`-cohomology.

## Setting

The real archimedean matrix algebra is `ArchimedeanMatrix F n`, the `n × n`
matrices over `F ⊗ ℝ = mixedEmbedding.mixedSpace F`. A pair `x = (x₁, x₂)` in
this space has a real coordinate `x₁ w` at each real place `w` and a complex
coordinate `x₂ w` at each complex place `w`. The published
`Langlands/Global/ArchimedeanLieAlgebra` makes these matrices a real Lie
algebra and defines:

- its complexification `ComplexLieAlgebra F n = ℂ ⊗[ℝ] RealLieAlgebra F n`;
- the enveloping algebra `EnvelopingAlgebra F n`, Mathlib's universal
  enveloping algebra of the complexification;
- its center `EnvelopingCenter F n`.

A realization `S` acts through the published
`OperatorRealization.envelopingAction`, the restriction of the actual
differential action on automorphic functions.

## Embedding coordinates and weights

- `EmbeddingIndex F` has one index `inl w` for each real place `w`, and two
  indices `inr (w, false)`, `inr (w, true)` for each complex place `w`. These
  correspond to the complex embeddings of `F`: the embedding of a real place,
  and the embedding of a complex place together with its conjugate.
- `embeddingComponent F j : F ⊗ ℝ →ₐ[ℝ] ℂ` is the coordinate at `j`:
  `x ↦ x₁ w` (as a complex number), `x ↦ x₂ w`, and `x ↦ conj (x₂ w)`,
  respectively. The `simp` lemmas `embeddingComponent_inl`,
  `embeddingComponent_inr_false` and `embeddingComponent_inr_true` record
  these formulas.

Through these coordinates, `z ⊗ X ↦ (z · σ_j(X))_j` identifies the
complexification with `∏_j 𝔤𝔩_n(ℂ)`. This is the familiar decomposition
`𝔤𝔩_n(F_v) ⊗_ℝ ℂ ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` at a complex place (Clozel 1990,
p.113), and `𝔤𝔩_n(ℝ) ⊗_ℝ ℂ = 𝔤𝔩_n(ℂ)` at a real place. The identification
explains the definitions below; it is not itself formalized. Weights are
functions `μ : EmbeddingIndex F → Fin n → ℂ`, with `μ j i` the `i`-th diagonal
coordinate of the weight at the factor `j`.

- `diagonalWeight F n μ d = ∑_j ∑_i μ j i · σ_j(d i)` is the value of `μ` on
  the complexified diagonal matrix `1 ⊗ diag(d)`, for `d : Fin n → F ⊗ ℝ`.
- `realGenerator F n X` is `1 ⊗ X` in the enveloping algebra, for a real
  archimedean matrix `X`.

## Definitions

- `IsHighestWeightVector F n μ w`, for a vector `w` of a module
  `W : ModuleCat.{u} (EnvelopingAlgebra F n)`, says three things:
  1. `w ≠ 0`;
  2. `realGenerator (diag d) • w = diagonalWeight μ d • w` for every `d`;
  3. `realGenerator (single i j a) • w = 0` for all `i < j` and
     `a : F ⊗ ℝ`.

  In other words, `w` is a highest-weight vector of weight `μ` for the Borel
  subalgebra of upper triangular matrices. The complex spans of the elements
  `1 ⊗ diag(d)` and `1 ⊗ a E_{ij}` (`i < j`) are the whole diagonal Cartan
  subalgebra and the whole strictly upper triangular subalgebra of
  `∏_j 𝔤𝔩_n(ℂ)`. This is because `F ⊗_ℚ ℂ ≅ ℂ^{Hom(F,ℂ)}`. A complex
  multiple `z ⊗ X` acts as `z` times `1 ⊗ X`, so testing real matrices
  suffices.
- `IsHighestWeightCharacter F n μ χ`, for an algebra homomorphism
  `χ : EnvelopingCenter F n →ₐ[ℂ] ℂ`, says that some module in universe `u`
  has a highest-weight vector `w` of weight `μ` with `z • w = χ(z) • w` for
  every central `z`.
- `IsRegularAlgebraicCharacter F n χ` says that `IsHighestWeightCharacter`
  holds for some integral weight `μ : EmbeddingIndex F → Fin n → ℤ` with every
  `μ j` antitone, that is, `μ j 1 ≥ μ j 2 ≥ ⋯ ≥ μ j n`. These are the
  dominant weights for the upper triangular Borel subalgebra.
- `OperatorRealization.HasInfinitesimalCharacter S χ` says that every central
  `z` acts on `S.Space` by the scalar `χ(z)`.
- `OperatorRealization.IsRegularAlgebraic S` says that `S` has some
  infinitesimal character `χ` with `IsRegularAlgebraicCharacter F n χ`.
- `OperatorRealization.IsoClass.IsRegularAlgebraic c` says that some
  representative of `c` has regular algebraic type.
- `CuspidalOperatorRealization.IsoClass.IsRegularAlgebraic c` is the same
  condition on the full-operator class of a cuspidal class. Like the published
  `IsConjugateSelfDual`, it carries the instance parameter
  `[CompactSpace (AdeleQuotient F)]`, which the published
  `compactSpace_adeleQuotient` proves.

## Theorems

- Non-vacuity. `augmentation F n` is the algebra character of the enveloping
  algebra that kills every Lie element: Mathlib's `UniversalEnvelopingAlgebra.lift`
  of the zero Lie map to `ℂ`. `trivialModule F n` is `ULift ℂ`, with the
  enveloping algebra acting through `augmentation` (`trivialModule_smul`).
  `isHighestWeightVector_trivial` shows that `trivialVector F n`, the vector
  `1`, is a highest-weight vector of weight `0`. So
  `isRegularAlgebraicCharacter_augmentation` proves that the restriction of
  `augmentation` to the center is regular algebraic. This is the infinitesimal
  character of the trivial representation, which is algebraic of highest
  weight `0`.
- `HasInfinitesimalCharacter.unique`: if `S.Space` has a nonzero vector, then
  `S` has at most one infinitesimal character.
- `HasInfinitesimalCharacter.of_equivalence` and
  `hasInfinitesimalCharacter_iff_of_equivalence`: full-operator equivalences
  preserve infinitesimal characters. Both use the published
  `Intertwiner.differential`. The proof of `of_equivalence` sets a finite
  `maxHeartbeats` of `2000000`: its rewriting step unifies the module
  instances of the Library's anonymous local instances with this module's
  named ones.
- `isRegularAlgebraic_iff_of_equivalence`: the same holds for regular
  algebraic type.
- `isoClass_isRegularAlgebraic_iff`: one representative of a class has regular
  algebraic type exactly when every representative has. The cuspidal version
  reduces to the full-operator version.

## Agreement with Clozel and Harris

Harris (1998), p.185, defines `Reg(n,E)` as the isobaric representations whose
cuspidal constituents `π_i` have `π_{i,∞}` "of cohomological type
[C1, Def. 3.12]; equivalently, `π_{i,∞}` has regular infinitesimal
character". [C1] is Clozel (1990).

Clozel's Définition 1.8 (pp.89–90) defines `Alg(n)`. For each infinite place
`v`, the restriction of the Langlands parameter `r_v` to `ℂ^×` must be
`χ_1 ⊕ ⋯ ⊕ χ_n` with `χ_i(z) = z^{p_i+(n-1)/2} \bar z^{q_i+(n-1)/2}` and
`p_i, q_i ∈ ℤ`. The type at infinity is `p = (p_ι)_ι`, indexed by the complex
embeddings `ι`. His Définition 3.12 (p.111) calls `π` regular when every
`p_ι` has distinct entries, and says that this amounts to regularity of the
infinitesimal character. The remark after Définition 1.8 (p.90) identifies
the infinitesimal character of `π_v` with these exponents, through
Harish-Chandra's isomorphism `Z(𝔤) ≅ S(𝔥)^W`.

In the proof of Théorème 3.13 (pp.112–113), Clozel attaches to a regular
`π ∈ Alg(n)` the dominant integral weights `m_ι = a − δ`, where
`δ = ((n−1)/2, …, −(n−1)/2)` is the half sum of positive roots. He takes the
rational representation `τ = ⊗_ι τ_ι` of `Res_{F/ℚ} GL(n)` of highest weight
`(m_ι)`, and checks that `π_v` has the same infinitesimal character as `τ_v`
at every infinite place. The Lean definition states exactly this conclusion:
the center acts on `π` through the infinitesimal character of an irreducible
algebraic representation of highest weight `μ = (m_ι)`. The following
standard facts show that the two conditions agree. They are the provenance of
the definition; they are not formalized here.

- The highest-weight vector of the representation `τ_μ` witnesses
  `IsHighestWeightCharacter μ χ` when `χ` is the infinitesimal character of
  `τ_μ`.
- Conversely, the center acts on any highest-weight vector of weight `μ`, in
  any module, by the same character. That character is the image of
  `μ + δ` under Harish-Chandra's isomorphism.
- An infinitesimal character `λ = μ + δ` with `μ` dominant integral has
  strictly decreasing entries in `(n−1)/2 + ℤ` at every factor. These are
  Clozel's `p_i + (n−1)/2` with `p_i` distinct integers. Conversely, such a
  regular `λ` is conjugate under the Weyl group to a unique strictly
  decreasing one, and subtracting `δ` gives a dominant integral weight.
- At a real place, the exponents of `r_v|_{ℂ^×}` are the coordinates of the
  infinitesimal character (Clozel, p.90 and p.113). So the integrality
  condition of `Alg(n)` depends only on the infinitesimal character.

## The archimedean component

The Library realization carries the action of the whole archimedean
enveloping algebra. For a factorization `π = π_∞ ⊗ π_f`, the center of the
archimedean enveloping algebra acts through `π_∞`. So "the archimedean
component has infinitesimal character `χ`" is the scalar action of the center
on `S.Space` that `HasInfinitesimalCharacter` states. This module does not
construct a separate archimedean component of the realization.

## Scope

- It is not asserted that the center acts by scalars on every irreducible
  realization. That is a theorem (Harish-Chandra), not part of the definition.
- The `(𝔤, K_∞)`-cohomological characterization of these representations
  (Clozel 1990, §3.5 and Lemma 3.14) is not formalized.
- The definitions apply to any number field. Harris's application uses CM
  fields.

## Source and provenance

- L. Clozel, *Motifs et formes automorphes: applications du principe de
  fonctorialité*, in *Automorphic Forms, Shimura Varieties, and L-functions*,
  Vol. I, Perspectives in Math. 10, Academic Press, 1990, pp.77–159. Source
  `clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`
  (scan: printed page `p` is PDF page `p + 11`). Read: Définition 1.8 and the
  Remarque (pp.89–90), Définition 3.12 (p.111), Théorème 3.13 and the
  construction of `τ` (pp.112–113).
- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210. Source
  `harris-1998-local-langlands`. Read: the definition of `Reg(n,E)` and
  Theorem 1.2 (p.185); Proposition 4.8 (p.201) and the Remark in its proof
  (p.202), which uses an arbitrary cohomological infinite component.

The embedding coordinates, the weight formula and the highest-weight
formulation are internal. They are the standard Lie-theoretic reading of
Clozel's definitions explained above.
