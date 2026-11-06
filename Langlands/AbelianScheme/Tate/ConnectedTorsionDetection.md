# Detecting torsion-kernel vanishing at one geometric point

Authors: Worker 410 and Worker 1584.

This internal helper is derived from the published finite étale geometric fibre
functor and the actual torsion scheme constructions. It supplies the
connected-base geometric step in
`ConnectedIntegralLatticeReflectionStatement`; it makes no claim about
rational denominators or an integral lift.

The published `AbelianScheme.Tate.torsionCover` from `FiniteMonodromy` regards the existing actual torsion
group scheme as a finite étale cover. Its underlying object is exactly
`(GroupScheme.torsion A.toGrp (n : ℤ)).X`; the finite and étale properties
are supplied by the explicit `TorsionFiniteEtaleStatement` premise for a
positive unit index. It introduces no replacement torsion scheme.

`FiniteEtale.hom_ext_of_geometric_fiber` states that two morphisms of actual
finite étale covers of a connected locally noetherian scheme are equal when
their actions on the points above one algebraically closed geometric point
are equal. The proof obtains finiteness from `geometricFiberFinite` and the
Galois category and fibre-functor structures from
`geometricGaloisFiberFunctor`. Mathlib proves that such a fibre functor is
faithful, so equality of its maps gives equality of the cover morphisms.
This reuses the published connected-base geometric arguments.

`AbelianScheme.Tate.kernel_comp_eq_one_of_levelMap_eq_zero` assumes the
published finite étale torsion proposition, a positive natural number `n`
that is a unit in the global sections of the base, actual abelian schemes
`A` and `B`, and an actual homomorphism `f : A ⟶ B`. If `levelMap f n`
vanishes on all level-`n` points at the supplied geometric point, the
conclusion is the equation of actual group-scheme homomorphisms

```text
kernelι (multiplication A.toGrp (n : ℤ)) ≫ groupHom f = 1.
```

The proof regards the actual torsion group schemes of `A` and `B` as finite
étale covers, using the explicit torsion hypothesis twice. It compares the
restriction `torsionMap f n` with the trivial homomorphism. The published
`kernelLevelEquiv` converts geometric points of the source torsion scheme
to the level group. Vanishing of `levelMap` then says that the restricted
map and the trivial map agree after the target torsion inclusion.
That inclusion is a monomorphism, so they agree on geometric points of
the torsion covers themselves. Faithfulness of the geometric fibre functor
gives equality on the whole torsion scheme. Finally `torsionMap_ι`
identifies the resulting equation with the required kernel composite.

The helper retains the connected, locally noetherian base and uses only
the one supplied geometric point. It requires neither a reduced nor a
normal base. Algebraic closure is sufficient for this step; no
characteristic-zero hypothesis is used. The finite étale torsion proposition
remains an explicit premise, as it is in the parent target. There is no new
external literature claim: the proof composes existing Library results and
their actual scheme morphisms.
