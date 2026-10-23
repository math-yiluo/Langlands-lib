# Sylow detection for positive-degree group cohomology

Author: Worker 313.

This module states two propositions about Mathlib's ordinary group cohomology.
Both are `Prop`-valued definitions, with a single arbitrary universe `u` and
all mathematical parameters quantified inside the proposition. No proof of either
proposition is supplied here.

## Detection statement

`Langlands.Cohomology.SylowDetection.{u}` states the following. For every
commutative ring `k : Type u`, finite group `G : Type u`, representation
`A : Rep.{u} k G`, natural number `n` with `0 < n`, and class
`x : groupCohomology A n`, if the restriction of `x` to every Sylow `p`-subgroup
of `G`, for every prime natural number `p`, is zero, then `x = 0`.

The precise restriction map for `P : Sylow p G` is

```lean
groupCohomology.map P.1.subtype (𝟙 (Rep.res P.1.subtype A)) n
```

Its domain is `groupCohomology A n` and its codomain is
`groupCohomology (Rep.res P.1.subtype A) n`. Thus the subgroup acts on the
original coefficient module by restriction along its actual inclusion in `G`.
The coefficient morphism is the identity on that restricted representation.
The prime hypothesis is the explicit implication `p.Prime → ...`; it is not
an assumption that every natural number is prime. All Sylow subgroups are
quantified, including those for primes not dividing the group order.

The statement uses `[Finite G]`, not a chosen enumeration of `G`. The coefficient
module need not be finite, finitely generated, or trivial as a representation.
There is no finiteness assumption on any cohomology group and no supplied
restriction, transfer, or index identity. Degree zero is outside the scope of
this statement.

## Subsingleton corollary statement

`Langlands.Cohomology.SylowSubsingleton.{u}` has the same ring, group,
representation, and positive-degree quantifiers. It states that if
`groupCohomology (Rep.res P.1.subtype A) n` is a subsingleton for every prime `p`
and every `P : Sylow p G`, then `groupCohomology A n` is a subsingleton.
These cohomology modules have a zero element, so subsingleton means that every
class is zero. This is the corollary target suggested by detection: every
restricted class is then zero, and detection forces every original class to be
zero. Neither the corollary nor its implication from detection is proved here.

## Source correspondence and derived provenance

The original source is Emil Artin and John Tate, *Class Field Theory*, AMS
Chelsea, 2009, Chapter XIV, section 2, Lemma 1, printed pp. 147–148
(PDF pp. 156–157), especially Case 2 on printed p. 148. Registered source:
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The retained source is
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.

Lemma 1 concerns bounds on cohomology orders in a formation, assuming exact
inflation–restriction sequences in a positive degree. Its second case uses
injectivity of restriction to a Sylow subgroup on the corresponding primary
part. The two propositions in this module isolate the resulting detection and
vanishing principle for an arbitrary finite group and arbitrary coefficients;
they do not restate the formation lemma or its order-divisibility conclusion.
In particular, the source's counting argument is not a reason to add a
cohomology finiteness hypothesis to these propositions. A `k`-linear
representation supplies an underlying abelian group with a `G`-action, so the
same group-cohomological principle applies with the extra scalar structure.

The generalization has the usual elementwise justification: restriction followed
by corestriction multiplies a class by the subgroup index. A class restricting
to zero on every Sylow subgroup is therefore annihilated by every Sylow index.
Those positive indices have no common prime divisor, which forces the class to
be zero. This argument concerns the additive order of one class, not finiteness
of the entire cohomology group. The published Library already provides
`Langlands.Tate.corestriction_restriction` and
`Langlands.Tate.restriction_groupCohomology` as ingredients for a separate proof
through the positive-degree Tate comparison. They are not hypotheses of the
statements and need not be imported to formulate them.

The Lean module imports only Mathlib's Sylow theory and ordinary cohomology
functoriality. It introduces no alternative cohomology construction and makes
no assertion about arithmetic formations, field descent, or prime-layer
induction. A subsequent proof task should target the complete closed
proposition `Langlands.Cohomology.SylowDetection.{u}`.
