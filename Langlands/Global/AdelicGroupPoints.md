# Rational and adelic group-scheme points

For every number field `F` and every actual group scheme `G` over `F`,
the four coefficient groups in this module are its points over `F`, the
full adele ring, the finite adele ring, and the product of the archimedean
completions. These are scheme morphisms from the corresponding spectra.
The coefficient rings are Mathlib's actual number-field adele rings.
There is no splitness or reductivity restriction on these constructions.

`AdelicGroupPoints.rational` is induced by the diagonal algebra map
`F → AdeleRing (𝓞 F) F`. `rationalSubgroup` is its image subgroup.
Naturality with respect to a homomorphism of group schemes follows from
the coefficient-point functor. General injectivity, discreteness,
closedness, local compactness, and any quotient or measure assertions
remain separate obligations.

The four `GeneralLinearGroupPoints` multiplicative equivalences reuse
the published `GeneralLinear.affinePointsEquiv`. Their targets are
exactly the existing `RationalGL`, `AdelicGL`, `FiniteAdelicGL`, and
`InfiniteAdelicGL`. The proved principal-map compatibility is the
existing naturality theorem applied to the diagonal adele algebra map:
it identifies the new scheme-point principal map with the existing
entrywise `AdelicGL.rational`. These are group equivalences; no topology
on the general coefficient-point groups is asserted here.

Provenance: Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), §2.2, printed pp. 51–56, defines scheme points over topological
coefficient rings; §2.3, printed pp. 56–60, applies this to adeles.
The registered source is `getz-hahn-2024-automorphic-representations`.
The four specializations and naturality bridge are internal
consequences of the existing scheme-point and matrix constructions.
The split-centre quotient of (2.20), reduction theory, and automorphic
function-space comparisons require further constructions.
