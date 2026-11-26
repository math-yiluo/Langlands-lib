# Finiteness of étale cohomology on compact analytic spaces

## Source

Vladimir Berkovich, *Vanishing cycles for formal schemes*, Invent. Math.
115 (1994), Corollary 5.6, printed p. 556 (PDF p. 18), and its proof on
pp. 556–557. Registered ID `berkovich-1994-vanishing-cycles-formal-schemes`,
SHA-256 `f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
The corollary gives finite ordinary étale cohomology for finite locally
constant sheaves of order prime to the residue characteristic on a compact
analytic space over an algebraically closed field. Each point must have a
neighbourhood that is a finite union of closed analytic domains admitting
quasi-étale maps to analytifications of schemes of finite type.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999), §2, printed p. 303 (PDF p. 5), uses
Berkovich's Corollary 5.6 on the two compact analytic domains whose
difference is the distinguished open domain used in Fact 1. The exact
sequence of the open domain and its closed complement then gives
compact-support finiteness. Registered ID
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

## Lean proposition

`Langlands.Cohomology.AnalyticEtaleFinitenessStatement` concerns the
Library's compact Hausdorff analytic spaces over an algebraically closed,
complete nontrivially normed ultrametric field `K`. The field, space and
chart universes agree because `AffineAnalytification.localized` has that
restriction. The module universe may be larger. There are two geometric
and coefficient predicates.

- `HasQuasiAlgebraicAffinoidNeighbourhoods X` asks for a finite union of
  affinoid chart ranges that is a neighbourhood of each point of `X`.
  Each chart's actual localized analytic domain admits a quasi-étale map
  to `AffineAnalytification.localized K P`, where `P` is a finite
  polynomial presentation of a `K`-algebra `B`. The allowed chart ranges
  are closed analytic domains because they are compact subsets of the
  Hausdorff space. This is a specialization of the source to affinoid
  domains and affine schemes of finite type.
- `IsFiniteLocallyConstantAnalyticEtaleSheaf R F` asks, for each point,
  for an étale test object whose image contains that point and a finite
  `R`-module whose constant sheaf is isomorphic to the restriction of
  `F` there. Restriction is precomposition by the opposite of
  `MorphismProperty.Over.map` along the étale arrow. The isomorphism is
  expressed on the actual presheaves underlying the two sheaves on the
  test object. The family of such objects is jointly surjective, the
  covering criterion of the analytic étale site.

For every `N > 0` with `‖(N : K)‖ = 1`, take `R = ULift (ZMod N)` and
such a sheaf `F`. The norm condition says that the order bound `N` is
prime to the residue characteristic. The conclusion is finite underlying
set of `H^q(X, F)` calculated by the Library's `etaleCohomology` in every
degree `q`. This states the compact ordinary-cohomology input to Harris's
argument. Finiteness for a noncompact difference requires the localisation
sequence, and the application to the Drinfeld domains requires their
quasi-algebraic geometry.
