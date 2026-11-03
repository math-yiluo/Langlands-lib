# Integral cocharacters of actual split components

Author: Worker 1322.

For a morphism `t : T → M` from a commutative group scheme,
`centralCocharacters t` is the integer submodule of actual cocharacters of `T`
whose composite into `M` is central on every test scheme. The zero, sum and
integer multiple conditions follow from the corresponding pointwise group laws
and the subgroup laws of the full scheme-center functor. This definition works
over any base scheme and requires no representability of the center.

Over a field, suppose a central morphism `a : A → M` factors as `f : A → T`
followed by `t`. Every integral cocharacter in the image of `f` is then central
after composition with `t`, by precomposition of the central morphism `a`.

If `M` is affine, `a` is an actual split component and the underlying scheme map
of `t` is monic, `IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters`
identifies this integral image exactly with `centralCocharacters t`. For the
reverse containment, the published split-component factorization theorem
factors the central composite of each actual cocharacter through `A`, since
the multiplicative group is split. Cancellation of the monic map `t` identifies
the resulting composite into `T` with the original integral cocharacter.
No independence, rank comparison, reductivity or splitness of `T` is assumed.

Finally, `IsSplitComponent.rootAnnihilator_le_range_cocharacterMapReal` applies
the integral-image identity and the real integral-span criterion. For a finite
character selection, it proves real annihilator containment when every actual
integral cocharacter annihilating those characters is central after composition
with `t`. That centrality remains a premise of this final lemma. The earlier
integral-image identity itself has no root-vanishing premise.

This unit is derived from the existing actual split-component factorization
theorem, the all-test center and the integral-annihilator span theorem. It uses
no external source. It does not prove centrality for a particular standard Levi,
the opposite real containment, standard-Levi reductivity or the unrestricted
standard-Levi central-direction proposition.
