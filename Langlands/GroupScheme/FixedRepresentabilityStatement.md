# Closed representability of fixed subgroups and centralizers

This module declares proposition targets. It does not prove representability or
choose a representing group scheme.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition A.8.10(1) and the remarks following its statement, printed
pp. 547–549 (PDF pp. 573–575), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The proposition concerns actions on separated schemes. Here the target is a
group scheme and the action respects its group law.

`SubgroupFunctor.IsClosedRepresentable F` means that there exist an actual
group scheme `C` over the same base and a homomorphism `i : C → G` such that:

- `F.IsRepresentedBy i`: the scheme map is a monomorphism and its range equals
  `F` on every test scheme over the base;
- `IsClosedSubgroup i`: the underlying scheme map is a closed immersion.

The existential witness is a group scheme with its inclusion, rather than an
unrelated model for its rational points. This predicate is an internal
abbreviation for the source's closed subgroup representability conclusion.

`HasFpqcProjectiveCoordinateModule H` records precisely the coordinate-module
hypothesis used here. For `H` over `Spec R`, put
`A = ((algΓ R).obj H.X).unop`, its global-section algebra with the structural
`R`-algebra map. There must exist a commutative `R`-algebra `B` such that `B`
is faithfully flat over `R` and `B ⊗[R] A` is a projective `B`-module.
For affine `H`, this tensor product is the coordinate algebra of the base
change to `Spec B`, as in the source. Projective means projective as a module;
there is no finite-generation premise. Affineness and flatness of `H` are
separate hypotheses, outside this predicate.

`FixedSubgroupRepresentabilityStatement` quantifies over every commutative base
ring, every affine flat acting group scheme `H`, every separated target group
scheme `G`, and every published `AutomorphicAction H G`. Under
`HasFpqcProjectiveCoordinateModule H`, it asserts that the published
`a.fixedSubgroup` is closed representable. This fixed functor tests invariance
after every refinement of every test scheme, including nonreduced tests. It is
not defined by invariance under only the points over the original test scheme.
The source states the functor on affine tests; the all-scheme formulation
uses its Zariski-local extension and the closed subscheme representing it.
The subgroup structure comes from the automorphic action laws and the
published subgroup functor.

`FieldFixedSubgroupRepresentabilityStatement` is the field specialization.
It assumes only affineness of the acting group, in addition to the actual
action and the group-scheme structures. Over a field the acting group is
flat, its coordinate vector space is projective, and a group scheme is
separated; the source explicitly discusses this case. Neither smoothness,
finite type, nor linear reductivity of the acting group is required.
The target group is not required to be affine, smooth, connected, or of
finite type.

`FieldCentralizerRepresentabilityStatement` specializes further to the
conjugation action associated with any homomorphism `j : H.toGrp → G`,
where `H` is affine and commutative over the field. The published theorem
`AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer` identifies
its fixed functor with `torusCentralizer j`. Despite that API name, `H`
need not be a torus or smooth, and `j` need not be a monomorphism. Thus this
target retains the scope needed for the kernel of a nonprimitive character,
once that kernel's affineness is supplied.

These declarations cover the closed representability part of A.8.10(1).
They do not assert the tangent-space comparison, smoothness, reductivity of
an identity component, compatibility with arbitrary base change, or descent
of an action through a quotient. In particular, projectivity alone is not a
smoothness premise, and no nonsmooth character kernel is assumed smooth.
