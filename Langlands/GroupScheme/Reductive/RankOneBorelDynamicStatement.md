# The two dynamic Borels in semisimple rank one: statement

`Langlands.GroupScheme.RankOneBorelDynamicStatement.{u}` is a proposition
definition. This module does not prove it.

Let `k : Type u` be an algebraically closed field, `G` a connected reductive
group scheme over `Spec k`, and `j : T ⟶ G` a split maximal torus.
Assume any two roots of `j` are linearly dependent over `ℤ` in
`characterLattice T`. Given a root `α` and a cocharacter `ν` with
`latticePairing T α ν ≠ 0`, every Borel embedding `b : B ⟶ G` through which
`j` factors represents one of the two dynamic subgroup functors
`P_G(ν ≫ j)` and `P_G((-ν) ≫ j)`.

The hypotheses use the actual `IsConnectedReductive`, `IsSplitTorus`,
`IsMaximalTorus`, `roots` and `IsBorelSubgroup` predicates. Affineness needed
by the actual Lie-weight definition of `roots` comes from connected
reductivity. The rank condition is the same pairwise dependence used by
`RankOneRootReducednessStatement`; the explicit root `α` excludes the
rootless case. The factorization `t ≫ b = j` keeps the specified torus
embedding. `IsRepresentedBy` includes both monomorphism and equality of
subgroup functors on every test scheme.

## Source and derivation

Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Lemma 20.20, printed pp.414–415
(PDF pp.430–431), proves that a split maximal torus in a reductive group of
semisimple rank one lies in exactly two Borels, the dynamic parabolics of
opposite generators of the derived maximal torus. The preceding
Theorem 20.16 and discussion on printed pp.412–413 (PDF pp.428–429)
give the rank-one geometry and the one-dimensional unipotent radicals.

The Lean statement is a derived reformulation. It replaces the semisimple
rank condition with pairwise dependence of actual Lie roots and permits any
cocharacter pairing nontrivially with one root. A proof must establish the
comparison of these rank conditions, then relate the dynamic subgroups for
this cocharacter to those for a generator of the derived torus. Since all
roots lie on one rational line, their nonzero pairings have the signs
determined by that line; reversing the cocharacter reverses these signs.
The actual dynamic Lie formulas and smooth connected subgroup comparison
can transfer the dynamic subgroup equalities. These are proof obligations,
not premises silently added to the proposition.

Only algebraically closed fields are asserted here. For these fields the
Library's maximal smooth connected solvable closed subgroup convention for
`IsBorelSubgroup` matches the usual Borel convention. The characteristic is
arbitrary. This statement does not assert reducedness, dimensions of root
spaces, a root datum, or the general Borel/cocharacter classification.

## Consumer boundary

The helper module `Dynamic.WeightExclusion` proves that a Lie-image
weight in a given dynamic parabolic pairs nonnegatively with its
cocharacter. It therefore excludes two opposite nonzero weight witnesses
once the present geometric statement supplies a parabolic with nonzero
pairing. This use does not prove the present statement. Its proof must be
independent of `RegularCocharacterBorelStatement`,
`ParabolicDynamicStatement`, and `RankOneSolvableObstructionStatement`,
whose proof needs this rank-one geometry.
