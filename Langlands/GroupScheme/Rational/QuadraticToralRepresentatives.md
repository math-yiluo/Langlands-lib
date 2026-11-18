# Toral representatives on a quadratic cover

`Langlands.GroupScheme.QuadraticToralRepresentativesStatement` is the local
representative assertion of Platonov and Rapinchuk, *Algebraic Groups and
Number Theory* (1994), Proposition 6.17, pp. 337–338, in the Library's
language of cocycles on covers. The coefficient extension is an algebraically
closed quadratic extension of a field of characteristic zero. For a
connected reductive group over the base, the assertion asks for a maximal
torus over the base and a cocycle of the torus on the quadratic cover.
Its pushforward must be cohomologous to the given cocycle on that cover.

The companion theorem `toralRepresentative_realBaseChange_of_quadratic`
assumes this assertion and applies it to a field cover after pullback
to a field `K` isomorphic to `ℝ`. Suppose the covering field `E` is
algebraic over the original base field `F` and contains a square root of
`-1`. Let `M` be the degree-two algebraic closure of `K`. An
`F`-embedding `E → M` gives a map from `Spec M` to the pullback cover.
The square root in `K ⊗[F] E` gives a map of covers in the other direction,
using `RealAlgebraicClosureStatement`.

Refine the given cocycle to `Spec M` and apply the quadratic-cover
assertion. Pull the resulting torus cocycle back to the real pullback
cover. Its refinement back to `Spec M` is cohomologous to the original
torus cocycle by comparing two parallel refinement maps. The map
`Spec M → Spec K` is faithfully flat and quasi-compact, so the resulting
cohomology comparison on `Spec M` descends to the real pullback cover.
