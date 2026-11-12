# Parabolic and radical diagrams under finite separable Weil restriction

Author: Worker 111.

`Langlands.GroupScheme.AffineWeilParabolicRadicalTransportStatement.{u}` is a
closed `Prop`-valued definition. It states a geometric prerequisite for the
elementary-subgroup comparison. It does not prove that prerequisite.

Let `k K : Type u` be arbitrary fields with a finite separable extension
structure, and let `G` be a group scheme over `K` with
`IsConnectedReductive G`. The statement asserts two things:

1. Given an actual parabolic `p : P → G` and its represented geometric
   unipotent radical `r : U → P`, restriction of both arrows by the published
   `AffineWeil.map k K` again gives a parabolic and its geometric unipotent
   radical.
2. Given any actual parabolic–radical diagram `U → P → R_{K/k} G` over `k`,
   there is such a diagram `U' → P' → G` over `K` and actual group-scheme
   isomorphisms `eP : P ≅ R_{K/k} P'` and `eU : U ≅ R_{K/k} U'`.
   Both squares commute:

   ```text
   eP.hom ≫ AffineWeil.map k K p' = p
   eU.hom ≫ AffineWeil.map k K r' = r ≫ eP.hom.
   ```

The predicates are the existing `IsParabolicSubgroup` and
`LeviSubgroup.IsGeometricUnipotentRadical`, with their geometric,
all-test meanings. The isomorphisms are actual group-scheme isomorphisms,
not only equivalences of rational points. The statement does not mention
elementary subgroups or assume a rational generation theorem.

The original group's affineness and local finite type are derived inside the
proposition from `IsConnectedReductive G`, exactly as in the consumer statement.
The forward clause displays affine and local finite-type instances for `P` and
`U` because the existing affine Weil construction requires them. These are
automatic in the intended application: both arrows are closed immersions into
an affine group, and both sources are smooth over the field. The converse
supplies those instances for `P'` and `U'` as existential evidence. There is no
perfectness, infinitude, local-field, topological or characteristic hypothesis.

The source is Borel–Tits, *Groupes réductifs* (1965), registered
`borel-tits-1965-groupes-reductifs`, 6.17–6.19 and 6.21(i), printed
pp.111–112 / PDF pp.58–59. Worker 111 read the extracted text and rendered
original pages. Section 6.17 fixes a finite separable extension and identifies
the restriction over a separable closure with the product of the conjugate
groups. Section 6.19 gives the bijection of rational parabolic subgroups.
For the radicals, that splitting identifies a restricted parabolic with the
product of its conjugates; the radical of this product is the product of their
radicals, which is the restriction of its original radical. Equality after the
faithful scalar extension descends to equality of the subgroups. The resulting
identifications give the two commuting squares above. The identities for
standard parabolics and their unipotent groups appear in 6.21(i), equations
(2)–(3).

This formulation is **derived**: the source does not state the proposition
using arbitrary representatives of both arrows and commuting isomorphisms.
Those choices make explicit the representative invariance of the source's
subgroup assertions. No bijection of chosen representatives is claimed.

CGP, *Pseudo-reductive groups*, second edition (2015), Appendix A.5,
equation (A.5.1), printed p.504 / PDF p.530, describes the adjunction.
Worker 111 also read Proposition A.5.15(1)–(2) and its proof, printed
pp.520–523 / PDF pp.546–549. That proposition concerns centralizers and
tori; it is not the source of this parabolic correspondence.

The separate module `Rational.AffineWeilParabolicElementaryReduction` proves
that this geometric statement implies the published
`AffineWeilParabolicElementarySubgroupStatement` by comparing its generator
sets and then taking subgroup closures. The geometric statement itself
remains a proof obligation.
