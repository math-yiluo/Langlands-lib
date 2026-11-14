# Vector-bundle series and affine torsor vanishing

Author: Worker 204.

`Langlands.GroupScheme.RelativeUnipotentAffineTorsorStatement` is a
universe-polymorphic proposition target. This module defines the proposition;
it does not prove it.

For every affine scheme `S : Scheme.{u}` and every actual smooth affine
`U : Langlands.GroupScheme S`, the hypothesis
`RelativeUnipotent.HasFiniteVectorBundleSeries U` implies that every actual
fpqc `U`-torsor over `S` has a section. The group and its series are over `S`
itself. There is no field of definition, noetherian hypothesis, connectedness
condition on `S` or on the total group, or global trivialization of the
successive bundle quotients. Their finite local ranks may vary over the base.

## Actual torsor and conclusion

`X : Over S` is an actual scheme over the base.
`ModObj U.X X` supplies a lawful left action in the category of schemes over
`S`. The hypotheses on `X.hom` are flatness, surjectivity, and
quasi-compactness. Together with the action, invertibility of
`ModObj.leftSMul U.X X` says that the actual shear

```text
U ×_S X → X ×_S X, (u, x) ↦ (u • x, x)
```

is an isomorphism. These are the fpqc torsor conditions. Neither a choice of
local section nor any cocycle-vanishing assertion is supplied as a premise.
The conclusion is an actual scheme morphism `s : S ⟶ X.left` satisfying
`s ≫ X.hom = 𝟙 S`.

The series predicate is defined in
`Langlands.GroupScheme.RelativeUnipotent.Basic`. It consists only of
geometric data: a finite recursive chain with trivial terminal group,
smooth closed normal kernels, represented fppf quotient homomorphisms, and
successive quotients naturally represented by sections of finite locally
free module sheaves. In particular, the series hypothesis does not already
contain the conclusion of this statement.

## Original source and derived scope

Brian Conrad, *Reductive group schemes* (2014), source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
Corollary 5.4.8, p.179, first proof paragraph. PDF and printed page numbers
agree. The paragraph reduces triviality of torsors under the relative
unipotent radical to affine vanishing for its vector-bundle successive
quotients, using the filtration of Theorem 5.4.3, pp.174–177.

The target isolates the argument for any smooth affine group supplied with
such a finite series. That is a derived generalization of the argument,
rather than a transcription of the full corollary. The source uses pointed
degree-one étale cohomology; the target uses actual fpqc torsors. For a smooth
affine group, an fpqc torsor is locally isomorphic to the group, hence smooth
over its base, and has étale local sections. The comparison, affine vanishing
for finite locally free module sheaves, and induction along the series are
proof obligations of this target.

## Interface for affine Levi existence

The separate target
`Langlands.GroupScheme.RelativeUnipotentRadicalFiltrationStatement` in
`Langlands.GroupScheme.RelativeUnipotent.RadicalFiltrationStatement` supplies
the series for a given relative unipotent radical `r : U ⟶ P`. Smoothness is
already a field of `IsRelativeUnipotentRadical r`; its closed immersion into
the affine relative parabolic supplies affineness of `U`.

To use the two targets in the affine Levi argument, one must first obtain a
relative radical and represent the functor of Levi subgroups by an actual
`U`-torsor, including the lawful action, fpqc cover, and shear isomorphism.
Applying this torsor target then gives a section; the representing
identification turns that section into a Levi subgroup. Radical existence,
Levi-torsor representability, and that final interpretation are separate
obligations. This module does not prove affine Levi existence or alter
`Langlands.GroupScheme.RelativeLeviAffineExistenceStatement` or its imports.
