# The contragredient formula from second adjointness

Author: Worker 138. Namespace `Langlands.SmoothRep`.

This is the forward implication of David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VI.9.6, printed pp.201–202 / PDF pp.207–208.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The abstract functors below are an internal formulation of the source's Hom chain
(VI.9.6.3); this module does not assert that its premises hold for arbitrary functors.

Let `L` be a functor from smooth complex representations of a topological group `M`
to those of a topological group `G`, and let `r` and `R` go in the reverse direction.
Both groups are topological groups. The group and representation carrier universes are
independent. Write `D_G` and `D_M` for the smooth contragredient functors.

`contragredientIsoOfSecondAdjunction` takes Frobenius reciprocity `F : r ⊣ L`, a natural
isomorphism `C : L.op ⋙ D_G ≅ D_M ⋙ L`, and second adjointness `A : L ⊣ R`, and constructs
`D_G ⋙ R ≅ r.op ⋙ D_M`. No exactness, admissibility or reflexivity is assumed.

The implemented proof composes `A` with the smooth-contragredient adjunction
`D_G.rightOp ⊣ D_G`. This makes `D_G ⋙ R` right adjoint to `L ⋙ D_G.rightOp`.
It separately composes `D_M.rightOp ⊣ D_M` with the opposite of `F`, then transports
its left functor along `contragredientRightOpIso C`. This makes `r.op ⋙ D_M` right
adjoint to the same functor. Mathlib's `Adjunction.rightAdjointUniq` gives the stated
natural isomorphism. This is Yoneda applied to the source's Hom chain.

`nonempty_contragredientIso_of_secondAdjunction` is the same implication with an
existentially supplied second adjunction. The converse is not claimed here.
