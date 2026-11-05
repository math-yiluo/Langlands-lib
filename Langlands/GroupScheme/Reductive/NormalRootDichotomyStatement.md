# Root subgroups and smooth connected normal subgroups

`Langlands.GroupScheme.SemisimpleNormalRootDichotomyStatement.{u}` isolates
the root-group step in the rewritten proof of Milne's Theorem 21.51. Over
an algebraically closed field of arbitrary characteristic, let `G` be an
actual semisimple group scheme, let `t : T.toGrp ⟶ G` be a split maximal
torus, and let `h : H ⟶ G` be a smooth connected closed normal subgroup.
For every actual relative root `α`, the actual root functor
`RelativeRoot.subgroup t α` is contained in the full range of `h`, or it
centralizes all of `H` on every test scheme and every refinement.

The original is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field*, corrected reprint (2022), registered source
`milne-2022-algebraic-groups`, the proof of Theorem 21.51, printed p.440
(PDF p.451), from the choice of maximal tori through the conclusion that
each root group outside `H` centralizes `H`. The registered 2017 and 2022
author errata were read. The 2017 errata say the proof was rewritten in
the 2022 reprint; the 2022 errata contain no further correction to this
theorem.

The source first proves that `H` is semisimple. For a root group outside
`H`, normality forces its character to restrict trivially to a maximal
torus of `H`. Conjugating a root parametrization of `H` by the outside
root group gives a morphism from the affine line to the multiplicative
group; this morphism is constant, and hence the root groups commute.
Generation of `H` by its root groups then gives the stated centralization.
This paragraph records the source argument, not an implemented Lean proof.

The statement uses the published Lie-weight roots, intrinsic
orbit-extension root functors, actual closed subgroup inclusions, and
all-test normality. Any required comparison with the source's classical
root groups is part of the proof obligation. The fixed subgroup of
`AutomorphicAction.conjugation h` is the existing full centralizer:
membership means invariance under every `H`-point after every refinement.
Thus no rational-points-only commutation, chosen factor decomposition, or
chosen centralizer representative is substituted for the conclusion.
Affineness and finite type of `H` follow from the closed inclusion and the
ambient semisimplicity; its smoothness and connectedness are explicit.

This is an internal extraction of a distinct source lemma, rather than a
claim that the source states it separately. It defines a proposition
target and proves neither the dichotomy nor almost-simple generation.
