# Finite vector-bundle series for supplied relative unipotent radicals

Author: Worker 204.

`Langlands.GroupScheme.RelativeUnipotentRadicalFiltrationStatement` is a
universe-polymorphic proposition target. This module defines the proposition;
it does not construct a filtration or prove that the proposition holds.

For every affine `S : Scheme.{u}`, actual group schemes `G`, `P`, `U` over
`S`, and homomorphisms `i : P ⟶ G` and `r : U ⟶ P`, the hypotheses

- `IsReductive G`;
- `IsRelativeParabolicSubgroup i`;
- `IsRelativeUnipotentRadical r`

imply `RelativeUnipotent.HasFiniteVectorBundleSeries U`.

The relative predicates are imported unchanged from
`Langlands.GroupScheme.RelativeLevi.Basic`. In particular, the supplied
radical is a smooth closed normal subgroup whose geometric fibres are the
unipotent radicals of the corresponding fibres of `P`. The proposition is
universal in every supplied `r`; it neither chooses a radical nor asserts its
existence. There is no noetherian, field, connectedness, nonemptiness, or
global constant-rank hypothesis.

The conclusion uses the geometric predicate from
`Langlands.GroupScheme.RelativeUnipotent.Basic`: a finite recursive
kernel/quotient series, a group trivial on all test schemes at the terminal
end, smooth closed normal kernels, represented fppf quotients, and
vector-bundle additive successive quotients with actual finite locally free
linear data. No torsor or cocycle-vanishing premise or conclusion occurs in
this target.

## Original source and the finite length

Brian Conrad, *Reductive group schemes* (2014), source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
Theorem 5.4.3, p.174, with proof pp.175–177; in particular Lemma 5.4.4,
p.176. PDF and printed page numbers agree.

The theorem supplies a descending filtration of the relative radical by
smooth closed subgroups. Its terms are normal in `P`, and the represented
successive quotients have compatible linear vector-bundle structures. These
give the kernels and quotients required by the recursive series predicate.
The target retains normality in each preceding term; it omits the stronger
automorphism invariance, commutator bounds, and base-change compatibility
provided by the source.

Part (i) of the theorem says that the fibre of the term `U_i` at `s` is
trivial once `i > dim R_u(P_s)`. The radical is smooth over `S`, so its Lie
module along the identity is finite locally free. Its rank is the fibre
dimension, a locally constant finite function of `s`. Since the affine base
is quasi-compact, finitely many constant-rank opens cover it; those finitely
many ranks have a common finite upper bound. Choosing `i` larger than that
bound makes every fibre of `U_i` trivial. This also covers an empty base.
The smooth group `U_i` is then the trivial group over `S`: its structural
morphism is étale with singleton geometric fibres, hence is an isomorphism.
It is therefore trivial on every test scheme, as the terminal clause of
`HasVectorBundleSeries` requires. Truncating at this index gives a single
finite length over the whole base.

This quasi-compact truncation and the translation into the recursive
interface are the derived content of this target. The original theorem
allows general bases and a descending filtration without requiring a
uniform global length. Here affineness supplies the needed bound; no
noetherian or connected-base assumption is introduced. Identifying a
supplied radical with the source's relative radical, the finite truncation,
and the quotient identifications remain proof obligations.

## Consumer interface

For the affine Levi argument, obtain a relative radical separately, apply
this filtration target to that `r`, and use
`Langlands.GroupScheme.RelativeUnipotentAffineTorsorStatement` from
`Langlands.GroupScheme.RelativeUnipotent.AffineTorsorStatement` to obtain a
section of an actual fpqc torsor under `U`. The smoothness of `U` is already
recorded in the radical predicate; its affineness follows from its closed
immersion into the affine relative parabolic `P`. The remaining construction
of a torsor representing Levi subgroups is separate. The unchanged parent
target is `Langlands.GroupScheme.RelativeLeviAffineExistenceStatement`.
