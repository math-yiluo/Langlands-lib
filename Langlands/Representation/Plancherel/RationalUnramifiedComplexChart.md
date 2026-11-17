# Basis charts on actual unramified characters (Renard V.3.20)

Author: Worker 4.

This file gives the group `X(G)` of unramified characters of `G(F)` a single global complex
chart. It is the chart determined by an integer basis of the lattice `Λ(G)`. It also names the
inclusion of the unitary subgroup `Im X(G)` in `X(G)`. These are the objects needed to state
the remaining assertions of Renard V.3.20: that `X(G)` is a complex torus and that `Im X(G)` is
a real submanifold of it. Those assertions are not made here; they belong to a separate statement
unit. This file contains definitions and the facts their construction needs: that the basis
evaluation is an open embedding, and some evaluation lemmas.

## Sources and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques` (SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). V.3.20, printed p.116 /
PDF p.122, constructs the surjection `𝔞*_ℂ = Hom_ℤ(Λ(M), ℂ) → Hom_ℤ(Λ(M), ℂ×) ≃ X(M)` and says:

> Le groupe `Λ(M)` étant un réseau, on voit facilement que ce morphisme est surjectif, en
> relevant dans `ℂ` les valeurs prises sur une base de ce réseau. […] On retrouve ainsi la
> structure de tore algébrique de `X(M)`.

and, for the unitary characters:

> On note `Im(X(M))` le groupe des caractères non ramifiés unitaires de `M`. […] C'est une
> sous-variété réelle du tore complexe `X(M)`, et plus précisément, c'est un tore compact,
> isomorphe à `i𝔞*/(2iπ/ln q)R`.

Renard gives no definition of the complex structure of `X(M)`. The standard one, which this
file implements, comes from the identification `X(M) ≃ Hom_ℤ(Λ(M), ℂ×) ≃ (ℂ×)^r` given by the
values of a character on a basis of the lattice `Λ(M)`. The same identification is the one the
quoted proof of surjectivity uses ("les valeurs prises sur une base de ce réseau"). The chart
depends on the basis. A change of basis acts on the coordinates by a monomial map with integer
exponents, which is holomorphic with holomorphic inverse on `(ℂ×)^r`. That the resulting complex
structure does not depend on the basis is therefore a statement to be proved; it is part of the
planned statement unit, not of this file. Provenance: derived. The definitions are this file's
encoding of the source's implicit structure, built from published Library objects.

## Actual objects and hypotheses

Let `F : Type u` have instances `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, and let `G : GroupScheme (Spec (CommRingCat.of F))`. Renard's
`M` is any Levi subgroup. Here `G` is any group scheme over `F`; the published objects below need
no reductivity.

- `rationalDiscreteValuationImage G` is the published image `Λ(G)` of the valuation map, with
  the discrete topology. `Additive (rationalDiscreteValuationImage G)` is the same group written
  additively, a `ℤ`-module.
- `rationalImageCharacters G` is the published type
  `rationalDiscreteValuationImage G →ₜ* ℂˣ` of characters of `Λ(G)`, with the compact-open
  topology. (Compact subsets of the discrete group `Λ(G)` are finite, so this is the topology
  of pointwise convergence.)
- `b : Module.Basis κ ℤ (Additive (rationalDiscreteValuationImage G))` is an arbitrary integer
  basis, indexed by any `κ : Type v`. No basis is chosen in this file. For a connected reductive
  `G`, the published `rationalReductiveImage_free_finite` shows that a finite basis exists, and
  `rationalReductiveValuationBasis` is one indexed by `Fin (rationalImageRank G)`.
- In the section `CanonicalTopology`, `G.X.left` is affine and `G.X.hom` is locally of finite
  type. `GroupScheme.rationalPoints G` then carries the published canonical topology
  `rationalPointTopology F G.X`, installed as a local instance, exactly as in the published
  `rationalCanonicalImageUnramifiedContinuousEquiv`. `X(G)` is the published subgroup
  `unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)` of continuous
  characters `G(F) → ℂˣ`, with its subspace topology. `Im X(G)` is the published subgroup
  `unitaryUnramifiedCharacters` of the same family, which is by definition
  `unramifiedCharacters ν ⊓ unitaryCharacters G(F)`.

## Declarations

### Characters of the lattice in a basis

- `rationalImageBasisCharacter G b c`, for `c : κ → ℂˣ`, is the character of `Λ(G)` with
  value `c i` on the basis element `b i`. It is defined through `Module.Basis.constr`, so its
  value at `a` is the image of `a` under the `ℤ`-linear map with values `c i` on `b i`.
  `rationalImageBasisCharacter_basis` records `χ(b i) = c i`. For finite `κ`,
  `rationalImageBasisCharacter_apply` gives the Laurent monomial
  `χ(a) = ∏ᵢ c i ^ (b.repr a i)`.
- `rationalImageBasisUnitCoordinates G b : rationalImageCharacters G ≃ₜ* (κ → ℂˣ)`, for finite
  `κ`, sends `χ` to `(χ(b i))ᵢ`. Its inverse is `rationalImageBasisCharacter G b`. The forward
  map is continuous because each coordinate is an evaluation. The inverse is continuous because
  the topology on characters is induced from all evaluations, and each evaluation is the
  Laurent monomial above, a continuous function of the coordinates. This is the published
  `rationalImageCharacterContinuousCoordinates`, with its fixed basis `rationalImageBasis G`
  replaced by an arbitrary basis `b`, and with the same proof.
- `rationalImageBasisEvaluation G b χ : κ → ℂ` is the tuple of complex numbers `(χ(b i))ᵢ`.
  `rationalImageBasisEvaluation_eq` writes it as `rationalImageBasisUnitCoordinates G b`
  followed by `Units.val` in each coordinate.
- `isOpenEmbedding_rationalImageBasisEvaluation`: for finite `κ`, this evaluation is an open
  embedding into `κ → ℂ`. Proof: `Units.val : ℂˣ → ℂ` is an open embedding (Mathlib's
  `Units.isOpenEmbedding_val`). A finite product of open embeddings is an embedding
  (`IsEmbedding.piMap`) and an open map (`IsOpenMap.piMap`, with the cofinite filter trivial on
  a finite index type). Composing with the homeomorphism `rationalImageBasisUnitCoordinates`
  gives the result.

### The chart on `X(G)`

In the section `CanonicalTopology`, for finite `κ`:

- `rationalUnramifiedBasisCoordinates G b χ : κ → ℂ`, for `χ ∈ X(G)`, is the basis evaluation of
  the image character `(rationalCanonicalImageUnramifiedContinuousEquiv G).symm χ`.
  `rationalUnramifiedBasisCoordinates_apply` says that its `i`-th coordinate is `χ(g)` for any
  `g ∈ G(F)` whose valuation image `rationalValuationImageProjection G g` is `b i`. (This lemma
  needs no finiteness of `κ`.)
- `isOpenEmbedding_rationalUnramifiedBasisCoordinates`: these coordinates are an open embedding
  `X(G) → (κ → ℂ)`. They are the open embedding above composed with the inverse of the
  published topological isomorphism `rationalCanonicalImageUnramifiedContinuousEquiv G`.
- `rationalUnramifiedBasisChartedSpace G b : ChartedSpace (κ → ℂ) X(G)` is Mathlib's
  `IsOpenEmbedding.singletonChartedSpace` of this open embedding. Its atlas consists of one
  chart, defined on all of `X(G)`, whose underlying map is `rationalUnramifiedBasisCoordinates G
  b` (`rationalUnramifiedBasisChartedSpace_chartAt`). It is a definition marked
  `instance_reducible`, not an instance, because it depends on `b`. Mathlib's
  `IsOpenEmbedding.isManifold_singleton` makes any such single-chart space a manifold for the
  model `𝓘(𝕜, κ → ℂ)` and every smoothness level, both for `𝕜 = ℂ` and for `𝕜 = ℝ`. With
  `𝕜 = ℂ` this is the complex torus structure; with `𝕜 = ℝ` it is the underlying real
  manifold, which the statement about `Im X(G)` uses. This file does not restate that lemma.
- `rationalUnitaryUnramifiedInclusion G : Im X(G) →* X(G)` is `Subgroup.inclusion inf_le_left`,
  which forgets unitarity (`rationalUnitaryUnramifiedInclusion_val`).

## Formalization choices

- **One global chart.** Renard's complex torus is `(ℂ×)^r`, which is an open subset of `ℂ^r`.
  A single chart into `κ → ℂ` therefore covers `X(G)`. This avoids products of charted spaces.
  It also makes the chart the literal coordinate map of the source's surjectivity argument.
- **Arbitrary basis.** The basis is a parameter, not a choice made by `Classical.choice`, so
  later statements can quantify over all bases and assert that the structure does not depend on
  the basis.
- **Image characters as the intermediate.** The chart is built on the published image
  characters and transported to `X(G)` by the published canonical topological isomorphism, so
  the topology of `X(G)` is its published compact-open subspace topology, not a new one.
- **Algebraic torus.** Renard's phrase "la structure de tore algébrique de `X(M)`" is
  represented on the algebraic side by published modules: `RationalUnramifiedCoordinateAlgebra`
  identifies the algebra of evaluations on `X(G)` with the group algebra of `Λ(G)`, which is a
  Laurent polynomial algebra (`rationalImageLaurentAlgebraEquiv`), and
  `UnramifiedRegularFunctionPoints` shows that evaluations separate the points of `X(G)` and,
  when the common norm kernel is open, that every `ℂ`-algebra homomorphism from that algebra to
  `ℂ` is evaluation at a character of `X(G)`.
  This file adds the analytic side, the complex chart. No scheme structure on `X(G)` is
  constructed here.
- **Universes.** `F : Type u` and the basis index `κ : Type v` are independent.

## What is not asserted

This file proves no statement about the complex or real structure beyond the open-embedding
property needed to define the chart. In particular it does not assert that multiplication is
holomorphic, that the chart is independent of the basis, that the complex exponential
`𝔞*_ℂ → X(G)` is a local biholomorphism, or that `Im X(G)` is a real submanifold isomorphic to
`i𝔞*/(2iπ/ln q)R` as a Lie group. These are the assertions of the planned statement unit. The
topological quotient descriptions `𝔞*_ℂ/(2iπ/ln q)R ≃ X(G)` and
`i𝔞*/(2iπ/ln q)R ≃ Im X(G)` are already published statements
(`RationalComplexParameterQuotientStatement` and `RationalImaginaryParameterQuotientStatement`).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates` | through its imports: `rationalDiscreteValuationImage`, `rationalImageCharacters`, `unramifiedCharacters`, `unitaryUnramifiedCharacters`, `rationalNormCharacters`, `rationalValuationImageProjection`, `rationalPointTopology`, `rationalCanonicalImageUnramifiedContinuousEquiv` and its `symm_projection` lemma |
| `Mathlib.Geometry.Manifold.HasGroupoid` | `IsOpenEmbedding.singletonChartedSpace`, `chartAt` |
| `Mathlib.Analysis.Normed.Ring.Units` | `Units.isOpenEmbedding_val` |
