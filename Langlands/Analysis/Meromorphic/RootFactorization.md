# Finite sums of products of root factors

Module `Langlands.Analysis.Meromorphic.RootFactorization`. It contains definitions and proved
lemmas only, about scalar functions on a complex vector space `X`. Meromorphy is the Library's
`IsMeromorphicInCoordinatesOn` (module `Langlands.Analysis.Meromorphic.LinearCoordinates`):
in every complex linear coordinate system `ℂⁿ ≃ X` the function is meromorphic with the given
domain of holomorphy, and that domain is open and dense.

## Provenance (derived)

The notions record the shape of the argument of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §8.6, pp. 225–226 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). For an elementary symmetry the
intertwining operator depends on the parameter only through one coroot coordinate. Composing
such operators in finite bases expresses the coefficients of a general intertwining operator
as sums of products of functions, each depending on one root form. The paper does not
formulate these notions; the lemmas are elementary facts about them.

## Translations

- `IsMeromorphicOn.comp_add_const`: on `ℂᵐ`, `s ↦ f (s + c)` is meromorphic with domain
  `(· + c) ⁻¹' U` when `f` is meromorphic with domain `U`. The holomorphy and the local
  quotient presentations are composed with the translation; the preimage of a connected
  neighbourhood is its image under `s ↦ s - c`, so it is connected.
- `IsMeromorphicInCoordinatesOn.comp_add_const`: the same in linear coordinates. In a chart
  `e`, the translation by `ν` becomes the translation by `e.symm ν`.
- `IsMeromorphicInCoordinatesOn.translate_invariant_of_open`: let `f` be meromorphic in
  coordinates with domain `D`, `ν ∈ X`, `e` a chart and `O` a nonempty open set of `ℂⁿ`. If
  `f (e s + ν) = f (e s)` for all `s ∈ O` with `e s ∈ D` and `e s + ν ∈ D`, then
  `f (x + ν) = f x` whenever `x ∈ D` and `x + ν ∈ D`. Proof: `x ↦ f (x + ν)` is meromorphic
  with domain `(· + ν) ⁻¹' D`, and the identity principle
  `IsMeromorphicInCoordinatesOn.eqOn_of_eqOn_open` gives agreement with `f` on
  `(· + ν) ⁻¹' D ∩ D`.

## Entire functions

`IsEntireInCoordinates f` says that `f ∘ e` is complex differentiable on `ℂᵐ` for every
complex linear isomorphism `e : ℂᵐ ≃ X`. Constants and products are entire
(`isEntireInCoordinates_const`, `IsEntireInCoordinates.mul`), entire functions stay entire
after a linear change of variables (`IsEntireInCoordinates.comp_linearEquiv`), and on a
finite-dimensional space an entire function is meromorphic in coordinates with any domain
that is open and dense in coordinates (`IsEntireInCoordinates.isMeromorphicInCoordinatesOn`,
from `isMeromorphicInCoordinatesOn_univ` and `IsMeromorphicInCoordinatesOn.congr_mono`).

## Root factors and root factorizations

Fix linear forms `L : ι → (X →ₗ[ℂ] ℂ)`, a set `R ⊆ ι` of allowed indices and a set `D ⊆ X`.

- `IsRootFactorOn L R D f`: `f` is entire in coordinates, or `f` is meromorphic in coordinates
  with domain `D` and there is `β ∈ R` with `f (x + ν) = f x` whenever `x ∈ D`, `x + ν ∈ D`
  and `L β ν = 0`. For the forms `r.rootFunctional hA hT` and the set `r.unipotentRoots` this
  is word for word the alternative required of each factor in
  `Langlands.Global.IntertwiningRootFactorizationStatement`.
- `HasRootFactorizationOn L R D f`: there are `J`, `n` and factors `fac j t`, all root factors
  on `D`, with `f x = ∑ j, ∏ t, fac j t x` for every `x ∈ D`.

Proved properties:

- `IsRootFactorOn.mono`, `HasRootFactorizationOn.mono`: if `D' ⊆ D` is open and dense in
  coordinates, root factors and root factorizations on `D` are root factors and root
  factorizations on `D'`. The meromorphic factors are restricted by `congr_mono`, and the
  invariance on `D'` is a special case of the invariance on `D`.
- `IsRootFactorOn.comp_linearEquiv`, `HasRootFactorizationOn.comp_linearEquiv`: let
  `e : X ≃ₗ[ℂ] Y` and forms `L'` on `Y` with allowed set `R'` such that for each `β' ∈ R'`
  there is `β ∈ R` with `L β ν = 0 → L' β' (e ν) = 0`. Then root factors (factorizations) on
  `D' ⊆ Y` pull back along `e` to root factors (factorizations) on `e ⁻¹' D'`.
- `HasRootFactorizationOn.of_isRootFactorOn` (one summand, one factor),
  `hasRootFactorizationOn_zero` (no summand), `HasRootFactorizationOn.congr` (agreement on
  `D`), `HasRootFactorizationOn.add` (the summands of both, each padded with constant factors
  `1` to `n₁ + n₂` factors), `HasRootFactorizationOn.mul` (summands indexed by pairs through
  `finProdFinEquiv`, factors concatenated), `HasRootFactorizationOn.sum` (finite sums, by
  induction).
- `HasRootFactorizationOn.exists_bound`: a root factorization with `J` summands and `n`
  factors can be rewritten with any `J' ≥ max J (n + 1)` summands and `n' ≥ max J (n + 1)`
  factors. Each existing summand is padded with constant factors `1`; each new summand has
  only constant factors `0`, so its product is `0` because `n' ≥ 1`.
- `exists_uniform_rootFactorization`: finitely many functions `coeff i`, `i : Fin k`, with root
  factorizations on `D` have root factorizations `fac i j t` on `D` with common numbers `J` and
  `n`. Take the supremum of the bounds of `exists_bound`.
