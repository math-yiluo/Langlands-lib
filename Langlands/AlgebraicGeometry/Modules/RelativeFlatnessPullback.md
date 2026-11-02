# Ordinary pullback preserves relative module flatness

For a cartesian square of arbitrary schemes
`P → X`, `P → T`, `X → S`, `T → S`, write the maps as `a`, `p`, `f`, `g`.
`isFlatOver_pullback_of_isPullback` proves that a module sheaf `M` flat over
`S` through `f` has ordinary pullback `a* M` flat over `T` through `p`.
The predicate is the actual stalk-flatness predicate `Modules.IsFlatOver`:
the scalar map at each point is the given scheme morphism's stalk map.
The schemes, points and module sheaves remain arbitrary in universe `u`.
No quasi-coherence, finiteness, properness or quasi-compactness assumption is
needed for this preservation result.

`flatPullback` restricts `Scheme.Modules.pullback a` to the full categories
of modules satisfying these relative-flatness predicates. It sends each
object to its actual ordinary pullback, with the proved preservation witness,
and each morphism to the ordinary pullback morphism. In particular it retains
all module morphisms; taking cores can subsequently restrict to isomorphisms.

The construction supplies the relative-flatness part of the scheme
specialization of Stacks Project, Section 99.5 (Tag 08KA), Situation 99.5.1,
object item (3), and Lemma 99.5.2. The original requires actual flat module
families and uses ordinary pullback for restriction. The intrinsic lemmas here
prove the required preservation directly. This unit does not construct the
finite-presentation/proper-support family groupoid or its coherent
pseudofunctor; those are separate parts of the host construction.

## Implemented proof

`flat_tensor_of_pushout_localization` is the algebraic core. If `C` is the
pushout of `R → A` and `R → B`, `D` is a localization of `C`, and the
`A`-module `M` is flat over `R`, then `D ⊗[A] M` is flat over `B`.
The pushout cancellation equivalence first identifies `C ⊗[A] M` with
`B ⊗[R] M`. The proved localization lemma
`Langlands.Algebra.flat_of_isLocalizedModule_of_flat` preserves this
`B`-flatness when localizing over `C`. Tensor cancellation then identifies
that localization with `D ⊗[A] M` as a `B`-module.

`flat_tensor_of_sections` accepts a pushout of commutative section rings
`R → Q`, `R → B`, with pushout `Q'`, and the actual compatible maps from
`Q` and `Q'` to localizations `L` and `D`. The published tensor
prime-localization criterion identifies `D` as a localization of
`L ⊗[R] B` through the supplied map to `D`. Thus the preceding algebraic
core applies to an `L`-module flat over `R`. The scalar towers are proved
from the given equalities of ring maps.

`flat_stalk_of_affine_base` restricts a relatively flat module stalk to the
section ring of an affine neighbourhood in the old base. That base local
ring is a localization of the section ring, hence flat, and flatness is
transitive. The germ/stalk-map identity identifies this action with the
actual section map followed by the source germ.

`flat_tensor_stalk` chooses affine neighbourhoods in the old base, old
source and new base around the images of an arbitrary point of `P`.
Their inverse-image intersection in `P` is affine, and the actual section
maps form a pushout. The source and pullback local rings are the respective
stalk localizations of these affine section rings. Applying
`flat_tensor_of_sections` gives flatness over sections of the new base.
The new base local ring is itself a localization, so
`Module.flat_iff_of_isLocalization` upgrades the conclusion to flatness
over that actual local ring.

Finally `StalkPullback.pullbackStalkTensorEquiv` identifies the actual
stalk of `a* M` with the tensor stalk just considered. Restricting that
linear equivalence along `p.stalkMap` transfers flatness to precisely the
action required by `IsFlatOver p`. The full-subcategory lift then gives
`flatPullback` and its action on arrows.

## Source

The retained original is
`Stacks Project- The stack of coherent sheaves (Section 99.5, Tag 08KA)/08KA.html`,
Situation 99.5.1 (Tag 08KB), item (3), and Lemma 99.5.2 (Tag 08W5), including
its proof. The source concerns algebraic spaces; this unit implements the
scheme pullback preservation needed by the host's stated specialization.
The explicit localization argument is an internal proof of that preservation.
