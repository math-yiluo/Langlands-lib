# A common maximal torus of two Borel subgroups: statement

Worker 1334. The statement interface and source locator were supplied by
Workers 1417 and 1240 in the task specification.

`Langlands.GroupScheme.TwoBorelCommonMaximalTorusStatement.{u}` states that,
over an algebraically closed field `k : Type u`, any two Borel subgroups of a
connected reductive group contain a common maximal torus of that ambient
group. It is a proposition definition; this module supplies no proof.

The source is Borel and Tits, *Groupes réductifs* (1965), source ID
`borel-tits-1965-groupes-reductifs`, §2.4, printed p.65 (one-based PDF p.12,
zero-based PDF page 11). The paragraph after the geometric Bruhat
decomposition says that the intersection of the fixed Borel subgroup `B`
with any Borel subgroup `B'` contains a maximal torus of `G`. The surrounding
§2.3, printed pp.64–65 (one-based PDF pp.11–12), assumes that `G` is connected
and reductive, constructs `B` using a maximal torus and positive roots, and
states that every Borel subgroup is conjugate to `B`. Thus the assertion
applies to any pair of Borel subgroups: conjugate the first to the fixed
one, apply §2.4 to the transformed second subgroup, and conjugate the
resulting torus back.

The algebraic-group conventions in §0.3, printed pp.57–58 (one-based PDF
pp.4–5), use linear algebraic groups and allow the intrinsic interpretation
as geometrically reduced affine group schemes. Here the ambient hypothesis
is the existing `IsConnectedReductive G`, unchanged. In particular it
includes smoothness, affineness and connectedness, as well as triviality of
the geometric unipotent radical. Smoothness and affineness over a field
ensure finite type, so this is the connected reductive algebraic-group
setting of the source. The field is algebraically closed, of unrestricted
characteristic; the universe `u` is arbitrary.

For actual group schemes `B`, `B'` and actual homomorphisms `i : B ⟶ G`,
`i' : B' ⟶ G`, the two hypotheses use the published `IsBorelSubgroup`
predicate. The conclusion chooses a commutative group scheme `T`, an
ambient homomorphism `t : T.toGrp ⟶ G`, and homomorphisms
`f : T.toGrp ⟶ B`, `f' : T.toGrp ⟶ B'`. The published `IsMaximalTorus t`
says that `T` is a torus, `t` is a closed subgroup, and `t` is maximal among
closed tori of `G`. The equations `f ≫ i = t` and `f' ≫ i' = t` express the
source's subgroup inclusions as factorizations of group-scheme
homomorphisms. They are equalities of morphisms, hence hold on every test
scheme, including nonreduced tests.

This expression through morphisms is the categorical reformulation of
the source assertion. It requires no chosen intersection scheme and no
torus, conjugacy theorem or Bruhat decomposition as an input. The source's
geometric Bruhat argument explains the provenance, rather than adding a
premise to the proposition. A proof of this target remains a separate
obligation; its successor task excludes the downstream rational Bruhat
decomposition, Borel–Tits 4.18 and the two parabolic-intersection targets.
