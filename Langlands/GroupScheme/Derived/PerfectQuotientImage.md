# The derived subgroup maps onto every perfect fpqc quotient

This unit proves, over a field `k`, that the derived subgroup `D` of a
smooth connected affine group `G` maps onto every quotient homomorphism
`q : G ⟶ Q` that is quasi-compact, flat and surjective, provided `Q` is
affine and locally of finite type and its derived subgroup functor is the
whole group functor (`derivedSubgroup Q = ⊤`, the Library's form of
"`Q` is perfect", Milne Definition 12.45). The conclusion is that the
underlying morphism of schemes of `d ≫ q` is surjective.

It is the step `G = T · D(G)` in the proof of Milne Proposition 12.46(b),
isolated as a reusable lemma: when `T` is a central torus with `G/T`
perfect, `D(G)` maps onto `G/T`. Milne argues that `G/(T · D(G))` is
both commutative and perfect, hence trivial. The Lean proof takes a
different route, described below, through the closed image of `D` in `Q`.
No reductivity, centrality or torus hypothesis appears here; the kernel of
`q` is arbitrary.

## Categorical and point-level helpers

All of these live in namespace `Langlands.GroupScheme.PerfectQuotientImage`.

`exists_lift_of_effectiveEpi` is a general category-theory fact: if
`g ≫ m = e ≫ f` with `e` an effective epimorphism and `m` a
monomorphism, then `f` factors through `m`. The proof uses that an
effective epimorphism is a strong epimorphism, and takes the diagonal lift
of the commutative square `g, e, m, f`.

`exists_commutator_factor` works over an arbitrary base scheme. If the
range of a homomorphism `d : D ⟶ G` contains all commutators
(`SubgroupFunctor.ContainsCommutators`), then the universal commutator
morphism `commutatorMap (𝟙 G) (𝟙 G) : G × G ⟶ G` factors through `d`.
The proof applies the hypothesis to the two projections, viewed as points
of `G` on the test object `G × G`.

`containsCommutators_range_of_factor` works over an arbitrary base scheme.
Its data are a homomorphism `q : G ⟶ Q` that is quasi-compact, flat and
surjective, a homomorphism `d : D ⟶ G` whose range contains all
commutators, a closed subgroup `inc : C ⟶ Q` and `fac : D ⟶ C` with
`fac ≫ inc = d ≫ q`. Its conclusion is that the range of `inc` contains
all commutators of `Q`. Write `w` for the factor of the commutator of `G`
through `d`. The published identity `CommutatorDescent.tensorHom_commutatorMap`
says that `q × q` followed by the commutator of `Q` equals the commutator
of `G` followed by `q`. This is `w ≫ fac ≫ inc`. The published
`CommutatorDescent.effectiveEpi_tensorHom` makes the underlying morphism of
`q × q` an effective epimorphism. `inc` is a closed immersion, hence a
monomorphism. `exists_lift_of_effectiveEpi` then factors the commutator
morphism of `Q` through `inc`. The factor is a morphism over the base.
Composing it with an arbitrary pair of points `x, y` and using
`commutatorMap_lift` shows that every commutator `[x, y]` lies in the range
of `inc`.

`surjective_of_top_le_range` works over an arbitrary base scheme. If the
range of `inc : C ⟶ Q` contains every point, the identity point of `Q`
lifts to a section `s` with `s ≫ inc = 𝟙`. Then the underlying morphism of
`inc` is surjective.

## Main results

`surjective_comp_of_containsCommutators` (namespace
`Langlands.GroupScheme`) works over `Spec k` for a field `k`. Its
hypotheses are:

- `D` is smooth, connected and affine over `k`;
- `Q` is affine and locally of finite type;
- `q : G ⟶ Q` is quasi-compact, flat and surjective;
- the range of `d : D ⟶ G` contains all commutators;
- `derivedSubgroup Q = ⊤`.

Its conclusion is that the underlying morphism of `d ≫ q` is surjective.
The published `HomImage.exists_image` factors `d ≫ q` as `fac ≫ inc`. Here
`fac` is flat and surjective and `inc : C ⟶ Q` is a closed subgroup. By
`containsCommutators_range_of_factor`, the range of `inc` contains all
commutators. The published minimality lemma `derivedSubgroup_le_range` then
gives `⊤ = derivedSubgroup Q ≤ range inc`. By `surjective_of_top_le_range`,
`inc` is surjective. Hence `d ≫ q = fac ≫ inc` is surjective.

`IsDerivedSubgroup.surjective_comp_of_derivedSubgroup_eq_top` (namespace
`Langlands.GroupScheme`) is the form used for a derived-subgroup inclusion
`d : D ⟶ G` (`IsDerivedSubgroup d`). It is an internal proof-producing
definition: a `def` whose type is the proposition below, so that it can be
recorded as this unit's entry declaration. The linter options before it
suppress the warnings for a Prop-valued and class-valued `def`. It is used
exactly like a theorem. There `G` is smooth, connected and
affine over the field `k`, and `q` and `Q` are as above. It supplies the
hypotheses on `D` from published results:

- smoothness: `IsDerivedSubgroup.smooth_of_connected`;
- connectedness: `derivedSubgroupConnectedness`;
- affineness: `d` is a closed immersion into the affine `G`.

The commutator hypothesis is `IsDerivedSubgroup.containsCommutators`.

## Scope

Surjectivity is surjectivity of the underlying morphism of schemes. Over a
field this is Milne's notion for homomorphisms of algebraic groups (Milne
Appendix A.22: surjective iff surjective on closed points of the
underlying varieties). The quotient `Q` and the morphism `q` are given; this
unit does not construct quotients. Nor does it prove that any particular
quotient is perfect. The two hypotheses are supplied separately when the
lemma is applied to a central torus `T` with `G/T` semisimple (Milne 12.46(b)
and 21.50).

## Provenance

Derived. The statement is the surjectivity step `G = T · D(G)` in the
proof of Milne, *Algebraic Groups* (2017), Proposition 12.46(b) (printed
p.245, proof p.246 / PDF pp.261-262). Here it is stated for an arbitrary
flat, surjective, quasi-compact quotient with perfect target. Perfectness
is Milne Definition 12.45 (printed p.245 / PDF p.261). The derived group
is Milne Definition 6.16 with the commutator description of Proposition
6.18 (printed p.129 / PDF p.145). The Library's `derivedSubgroup` is the
all-test-scheme form of the latter. Appendix A.22 is on printed
pp.570-571 / PDF pp.586-587; its surjectivity sentence is on p.571. The
errata page (snapshot 2026-11-02) has no entry for 6.16, 6.18, 12.45,
12.46 or A.22. Its p.129 entry concerns only 6.19(c)-(e), and its p.570
entry concerns footnote 3, which belongs to A.20.

Authorship: Worker 1383.
