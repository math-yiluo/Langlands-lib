# The complex torus `X(G)` and its real subtorus `Im X(G)` (Renard V.3.20): statements

Author: Worker 4.

`RationalUnramifiedComplexTorusStatement` states the parts of Renard V.3.20 that concern smooth
structure. These are the complex torus structure of the group `X(G)` of unramified characters,
and the fact that the unitary characters `Im X(G)` form a real submanifold of it. That
submanifold is a compact torus isomorphic to `i𝔞*/(2iπ/ln q)R`. It is the conjunction of four
component statements, one for each part below, so that each part can be proved separately. The
file makes statements and proves nothing.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques` (SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), V.3.20, printed p.116 /
PDF p.122. After constructing the surjection `𝔞*_ℂ → X(M)`, `χ ⊗ s ↦ [g ↦ |χ(g)|_F^s]`, with
kernel `(2iπ/ln q)R`, Renard writes:

> On retrouve ainsi la structure de tore algébrique de `X(M)`.

and, about the unitary characters:

> On note `Im(X(M))` le groupe des caractères non ramifiés unitaires de `M`. […] C'est aussi
> l'image de `i𝔞*` par le morphisme surjectif `𝔞*_ℂ → X(M)`. C'est une sous-variété réelle du
> tore complexe `X(M)`, et plus précisément, c'est un tore compact, isomorphe à
> `i𝔞*/(2iπ/ln q)R`.

Renard's `M` is a Levi subgroup; here it is any connected reductive group `G`.

## What is already published

- `RationalComplexParameterQuotientStatement`: the exponential `𝔞*_ℂ → X(G)` is an open quotient
  map, and `𝔞*_ℂ/(2iπ/ln q)R ≃ₜ X(G)`.
- `RationalImaginaryParameterQuotientStatement`: the analogous topological statement for
  `i𝔞* → Im X(G)`.
- `RationalUnramifiedCoordinateAlgebra` and `UnramifiedRegularFunctionPoints`: the algebra of
  evaluations on `X(G)` is a Laurent polynomial algebra, and its complex points are the
  characters in `X(G)`.
- `RationalUnramifiedComplexChart`: the chart of `X(G)` given by an integer basis `b` of
  `Λ(G)`. A character goes to its values on `b`, as a point of `ℂ^r`.

This statement adds the analytic and smooth structure, which the topological and algebraic
statements do not express.

## Setting

The statement quantifies over a universe `u`, a field `F : Type u` with `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F`, a group scheme
`G : GroupScheme (Spec (CommRingCat.of F))` and `hG : GroupScheme.IsConnectedReductive G`. From
`hG` it installs `IsAffineHom G.X.hom`, `IsAffine G.X.left` and `Smooth G.X.hom`. It gives
`GroupScheme.rationalPoints G` the canonical topology `rationalPointTopology F G.X`. These are
the same instances as in the published quotient statements, so `X(G)`, `Im X(G)` and the
exponential are the published objects:

- `X(G) = unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)`;
- `Im X(G) = unitaryUnramifiedCharacters (…)`, the unitary unramified characters;
- `rationalCanonicalUnramifiedComplexExponential G : Multiplicative (Λ(G) →+ ℂ) →* X(G)`, with
  `exp(λ)(g) = exp(−λ(H(g)) ln q)` (`rationalCanonicalUnramifiedComplexExponential_val`), where
  `H(g)` is the valuation image of `g` and `q` the residue cardinality.

Write `r = rationalImageRank G` and `E = Fin r → ℂ`. The statement quantifies over every basis
`b : Module.Basis (Fin r) ℤ (Additive (rationalDiscreteValuationImage G))`. Such a basis exists
by the published `rationalReductiveImage_free_finite`. For `s : Fin r → ℂ`, `b.constr ℤ s` is
the element of `𝔞*_ℂ = Hom_ℤ(Λ(G), ℂ)` with value `s i` on `b i`; these are coordinates on `𝔞*_ℂ`.
`X(G)` is given the charted space `rationalUnramifiedBasisChartedSpace G b`. It has one chart,
`χ ↦ (χ(b i))ᵢ ∈ E`. Under the complex model `𝓘(ℂ, E)` this is a complex manifold, and under the
real model `𝓘(ℝ, E)` the underlying real manifold.

## The statements

Each of the four component statements quantifies over the setting above. It asserts its part
for every `F`, `G`, `hG` and `b`, with the chart of `b` on `X(G)`:

1. **Basis independence**, `RationalUnramifiedBasisChartIndependenceStatement`. For every basis
   `b'`, the map `rationalUnramifiedBasisCoordinates G b'` from `X(G)` to `E` is a local
   biholomorphism: `IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) ω`. So the charts of all bases define the
   same complex-analytic structure.
2. **Complex Lie group**, `RationalUnramifiedComplexLieGroupStatement`.
   `LieGroup 𝓘(ℂ, E) ω X(G)`: multiplication and inversion are holomorphic.
3. **Exponential**, `RationalUnramifiedComplexExponentialStatement`. `s ↦ exp(b.constr ℤ s)`,
   from `E` to `X(G)`, is a local biholomorphism (`IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) ω`).
4. **The real subtorus**, `RationalUnitaryUnramifiedSubmanifoldStatement`. There is a charted
   space on `Im X(G)` modelled on `Fin r → ℝ` such that:
   - `Im X(G)` is a real Lie group: `LieGroup 𝓘(ℝ, Fin r → ℝ) ∞`;
   - the inclusion `rationalUnitaryUnramifiedInclusion G : Im X(G) → X(G)` is a smooth
     embedding (`Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) ∞`), with `X(G)` regarded
     as a real manifold;
   - there is a map `e : (Fin r → ℝ) → Im X(G)` with `e(t) = exp(b.constr ℤ (t·i))` in `X(G)`
     for every `t`, and `e` is a local diffeomorphism
     (`IsLocalDiffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) ∞`).

Here `ω` is analytic smoothness. Over `ℂ` it is equivalent to holomorphy. `∞` is ordinary
smoothness.

`RationalUnramifiedComplexTorusStatement` is the conjunction of the four, in this order, all at
the same universe `u`. Since each component quantifies over the whole setting, the conjunction
is equivalent to stating the four parts together for every `F`, `G`, `hG` and `b`.

In part 4 the existentially quantified charted space is the one used by `LieGroup` on `Im X(G)`
and by `Manifold.IsSmoothEmbedding` for the source of the inclusion: there is no other
`ChartedSpace` instance on this subgroup. The target `X(G)` of the inclusion carries the chart of
`b`. A scratch check of the elaborated definition confirmed both.

## Correspondence with the source

- "la structure de tore algébrique de `X(M)`", "le tore complexe `X(M)`": parts 1 and 2. Part 1
  makes the structure canonical, and part 2 makes it a complex Lie group. With the chart, which
  identifies `X(G)` with the open subset `(ℂ×)^r` of `ℂ^r`, it is the complex torus `(ℂ×)^r`.
  The algebraic side is the published coordinate algebra (see above).
- The morphism `𝔞*_ℂ → X(M)` is a local biholomorphism: part 3. Renard uses it implicitly when
  he describes `X(M)` as the quotient `𝔞*_ℂ/(2iπ/ln q)R`. The quotient as a topological group is
  the published `RationalComplexParameterQuotientStatement`.
- "C'est une sous-variété réelle du tore complexe `X(M)`": the first two items of part 4. A real
  submanifold is encoded as a manifold structure on the subset for which the inclusion is a
  smooth embedding. The charted space is existentially quantified because Renard names no
  charts. Every such structure is a Lie group structure, by the first item.
- "c'est un tore compact, isomorphe à `i𝔞*/(2iπ/ln q)R`": the last item of part 4. The map
  `i𝔞* → Im X(G)` is a homomorphism, since `e(t)` is the exponential of `t·i`, and a local
  diffeomorphism. Its surjectivity, its kernel and the topological isomorphism with the quotient
  are the published `RationalImaginaryParameterQuotientStatement`. Compactness of `Im X(G)` is
  the published `compactSpace_rationalUnitaryUnramifiedCharacters`.

## Why the statement is true

In the chart of `b`, `X(G)` is `(ℂ×)^r ⊂ ℂ^r` with coordinatewise multiplication. Inversion is
`z ↦ z⁻¹`. The chart of another basis `b'` differs from it by the monomial map
`z ↦ (∏ⱼ zⱼ^{mᵢⱼ})ᵢ`, where `(mᵢⱼ)` is the change-of-basis matrix, which lies in `GL_r(ℤ)`. This
map is a biholomorphism of `(ℂ×)^r`. In the coordinates of `b`, the exponential is
`s ↦ (exp(−sᵢ ln q))ᵢ`, a local biholomorphism `ℂ^r → (ℂ×)^r`, because `ln q ≠ 0` (`q > 1`).
`Im X(G)` is the subset `|zᵢ| = 1` for all `i`, the compact torus `(S¹)^r`. It is an embedded
real submanifold and a real Lie group, and `t ↦ (exp(−i tᵢ ln q))ᵢ` is a local diffeomorphism
`ℝ^r → (S¹)^r`. No proof is given here.

## Formalization choices

- **Coordinates.** The statement uses `E = Fin r → ℂ` as the model, through the chart of a basis.
  It does not construct a model for `𝔞*_ℂ` itself. The coordinates `s ↦ b.constr ℤ s` identify
  `ℂ^r` with `𝔞*_ℂ`.
- **Quantification over bases.** The statement is made for every basis. Part 1 then says that
  the structure does not depend on it. It is therefore not a structure tied to the basis chosen
  by `rationalReductiveValuationBasis`.
- **Smoothness levels.** The complex assertions use `ω`, which over `ℂ` is holomorphy; this is
  the natural meaning of "tore complexe". The real assertions use `∞`, matching "sous-variété
  réelle". Both are as strong as the source requires.
- **Existential real structure.** The real manifold structure of `Im X(G)` is existentially
  quantified, with Mathlib's `Manifold.IsSmoothEmbedding` (a topological embedding that is an
  immersion in charts of the maximal atlases). This is the usual definition of an embedded
  submanifold.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalUnramifiedComplexChart` | `rationalUnramifiedBasisChartedSpace`, `rationalUnramifiedBasisCoordinates`, `rationalUnitaryUnramifiedInclusion`; through its imports `unramifiedCharacters`, `unitaryUnramifiedCharacters`, `rationalNormCharacters`, `rationalImageRank`, `rationalDiscreteValuationImage`, `rationalPointTopology` |
| `Langlands.Representation.Plancherel.RationalImageComplexExponential` | `rationalCanonicalUnramifiedComplexExponential` |
| `Mathlib.Geometry.Manifold.Algebra.LieGroup` | `LieGroup` |
| `Mathlib.Geometry.Manifold.LocalDiffeomorph` | `IsLocalDiffeomorph` |
| `Mathlib.Geometry.Manifold.SmoothEmbedding` | `Manifold.IsSmoothEmbedding` |
