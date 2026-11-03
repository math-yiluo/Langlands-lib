# A common rational maximal torus for two parabolic subgroups

Author: Worker 308.

`Langlands.GroupScheme.ParabolicIntersectionTorusStatement.{u}` states
the first assertion of Borel–Tits, *Groupes réductifs* (1965),
Proposition 4.7, printed page 88 (zero-based PDF page 34).
Source ID: `borel-tits-1965-groupes-reductifs`; SHA-256:
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.

For any field `k : Type u`, a connected reductive group scheme `G` over
`k`, and two actual rational parabolic subgroup morphisms
`j : P ⟶ G` and `j' : P' ⟶ G`, the proposition asks for an actual
commutative group scheme `T` over the same field and an inclusion
`i : T.toGrp ⟶ G` satisfying the published `IsMaximalTorus` predicate.
There must be actual group scheme homomorphisms `f : T.toGrp ⟶ P`
and `f' : T.toGrp ⟶ P'` with `f ≫ j = i` and `f' ≫ j' = i`.
These factorization equations imply containment in both parabolic
subgroup functors on every test scheme. They do not compare only
rational points.

The torus is maximal in the ambient `G`. It is allowed to be nonsplit:
the proposition uses `IsTorus` through `IsMaximalTorus`, rather than
`IsMaximalSplitTorus`. There is no perfectness, characteristic,
cardinality, or algebraic-closedness restriction on `k`, and no
minimality requirement on the parabolics.

The source proves the assertion using separable splitting and the
maximum-rank intersection of the two parabolics, together with rational
maximal-torus existence (4.5, 4.6, and 2.14). This module states the
result without proving those geometric inputs or their combination.
It does not formalize the other assertions of Proposition 4.7 concerning
descent, radicals, or Levi subgroups.

This is the common rational maximal torus input used in the proof of
Corollary 4.18. It supplies no maximal split torus or centralizer
containment by itself. Passing to the largest split subtorus and
proving the required centralizer inclusions remain separate obligations.
