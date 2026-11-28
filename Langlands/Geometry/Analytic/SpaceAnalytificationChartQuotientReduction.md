# Analytic quotients of étale chart families from elementary étale points

For a separated algebraic space `X` over a complete ultrametric nontrivially normed
field `K`, let `x : Spec A → X` be étale with `A` of finite type over `K`, and fix a
prime `p` of `A`. Given `SeparatedElementaryEtalePointStatement.{u}`,
`ElemChart.ofPrime` chooses an elementary étale chart `y : Spec B → X` at a prime
`q` of `B`, with a finite polynomial presentation for `B`. For each affine model
`M : TestModel (pointHom K x) (pointHom K y)` of the overlap, the subtype records
that `Spec M.C` has a prime mapping to `p` and `q` along the two projections.
The definition uses classical choice on the elementary point statement. It builds
the presentation by `FinitePolynomialPresentation.ofFiniteType` and flips each
overlap square to apply the prime existence clause of that statement.

The theorem
`Langlands.Analytic.SpaceAnalytification.ChartQuotient.spaceAnalytificationChartQuotient_of`
has two hypotheses.

- `Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedElementaryEtalePointStatement.{u}`
  supplies an elementary étale point over the image of each prime of an étale affine
  chart of finite type of a separated algebraic space over a field.
- `Langlands.Analytic.SaturatedAtlasPresentation.EtaleHomSheafStatement.{u, u}` gives the
  sheaf property of Hom presheaves on small étale sites of analytic spaces.

Together these hypotheses imply
`Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationChartQuotientStatement.{u}`.
For every complete ultrametric nontrivially normed field `K`, separated algebraic space `X`
over `Spec K`, and family of étale affine test points `x i : Spec A_i → X` with finite
polynomial presentations `P i`, there are an analytic space `Y` and étale maps
`π i : Spec(A_i)ᵃⁿ ⟶ Y`, jointly surjective on points. Every presheaf fibre square
`Spec B = Spec A_i ×_X Spec A_j` with a finite polynomial presentation of `B` becomes a
pullback square with the chart maps `π i` and `π j`.

## Proof

For each `j = (i, p)` with `p` a prime of `A_i`, the proof applies `ElemChart.ofPrime`
using finite type of `A_i` from `P i`. It takes `E j` to be the chosen chart and
specializes the subtype property to the chosen intersection model `Nj` to obtain `ha`.

For a piece index `m = (j, v)`, the analytic point `v` of `Spec(B_j)ᵃⁿ` has center `q_j`.
The lemma `ElemChart.exists_trivial_open` gives a neighbourhood `O₁ m` on which the
analytified self-relation is trivial. The proof intersects `O₁ m` with the image of the
analytified projection from `Nj` to `Spec(B_j)ᵃⁿ`. The resulting set `O m`
is open by `etaleOpenMap`. The lemma `exists_baseMap_eq_center` lifts `v` to the
intersection with the prescribed center from `ha`, so `v ∈ O m`. Containment in `O₁ m`
gives the relation-triviality hypothesis `htriv`, and containment in the projection image
gives `hOr`.

The witness is the glued space of `chartRelation` with the maps `π i`; `etale_π`,
`π_surjective` and `isPullback_π` give the three properties.

## Provenance

The conclusion specializes the quotient existence in Conrad–Temkin, *Non-archimedean
analytification of algebraic spaces* (2009), Theorem 4.2.2, p.20, to the analytified
relation of the given chart family. The paragraph after Theorem 4.2.1 describes this
relation, and Lemma 4.2.3 and Corollary 4.3.2 motivate gluing and étale localization.
The formal proof obtains its open pieces using elementary étale neighbourhoods as in
Stacks Project, Decent Algebraic Spaces, Lemma 68.11.4 (Tag 0BBP) and Definition
68.11.5 (Tag 0BGU). The descent used by the assembly is the second hypothesis, the
étale Hom-sheaf property of Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), §4.1, with Conrad–Temkin, Theorem 4.1.2.
