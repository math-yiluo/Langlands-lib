# Finite representable presentations of Čech nerves

This internal construction supplies a `FiniteBasisCover.CechPresentation` from
chosen limiting cones for every tuple of covering objects. It constructs
isomorphisms of the actual presheaf Čech nerve terms, with formulas for their
inverse followed by the canonical projections. Its inputs retain the existence
and basis membership of the geometric limits.

Let `C : Type u` be a category with morphisms in `Type v`, locally small in
universe `w`. The presheaves take values in `Type w`. The coproduct indices used
here lie in `Type 0`. For a finite family `f i : V i ⟶ U`, let `A` be the arrow
from the coproduct of the shrunken representables of `V i` to the shrunken
representable of `U`, with components induced by `f i`.

For every tuple `α : Fin k → Fin m`, suppose that `c α` is a wide pullback cone
of the family `f (α j)` and that `hc α` proves it limiting. Then
`coproductWidePullbackIso` identifies the coproduct of the representables of
`(c α).pt` with the presheaf wide pullback of `k` copies of `A`. The construction
also covers `k = 0`, when the base component is needed to characterize a section.

The forward map `coproductWidePullbackMap` is the coproduct of the maps induced
by each cone's base and projections. The equations
`coproductWidePullbackMap_ι_π` and `coproductWidePullbackMap_ι_base` compute these
maps on each summand.

The proof that this map is an isomorphism works at every presheaf object `Z`.
`coproductSectionsEquiv` identifies a coproduct section with its summand index
and section; its two evaluation lemmas compute this identification and its
inverse. `presheafWidePullback_sections_ext` gives equality from the base and all
projection components, using that evaluation preserves the presheaf limit.
For surjectivity, the components of a wide pullback section determine a tuple
of summand indices and, by shrunken Yoneda, compatible arrows to the `V (α j)`
and `U`. The limiting cone supplies an arrow to its point. Its representable
section gives the required preimage. For injectivity, equality of the projection
components first identifies the summand tuples. The limiting cone's uniqueness
then identifies the two arrows to the same point, hence their sections. Thus
every component is bijective, and the natural transformation is an isomorphism.

For `k = n + 1`, `representableCoproductCechIso` is the inverse of this wide
pullback isomorphism, giving the tuple-indexed decomposition of degree `n` of
`A.cechNerve`. Its two inverse/projection equations are the equations of the
canonical forward map above.

Now fix a Grothendieck topology `J`, a family `B : ι → C`, and a finite basis
cover `s` of `U`. The construction
`FiniteBasisCover.cechPresentationOfCones` takes, in every degree `n`:

- an index `b n α : ι` for every tuple `α : Fin (n + 1) → Fin s.size`;
- a limiting wide pullback cone `c n α` of the arrows `s.arrow (α j)`;
- an isomorphism `e n α : (c n α).pt ≅ B (b n α)`.

It composes the tuple-indexed decomposition with the coproduct of the Yoneda
images of `e n α`, then reindexes the finite tuple type using
`(Fintype.equivFin _).symm`. Its size in degree `n` is the cardinality of this
tuple type, and its basis index at `i` is `b n ((Fintype.equivFin _).symm i)`.
The resulting isomorphism has exactly the type required by
`FiniteBasisCover.CechPresentation` from `FiniteCoverCechSystem`.

The lemmas `cechPresentationOfCones_ι_inv_π` and
`cechPresentationOfCones_ι_inv_base` compute its inverse on each finite summand.
Writing `α = (Fintype.equivFin _).symm i`, the first is the Yoneda image of
`(e n α).inv ≫ (c n α).π j`, followed by the inclusion of covering summand
`α j`; the second is the Yoneda image of
`(e n α).inv ≫ (c n α).base`. Both also have reassociation lemmas.

The proof uses only the existing Library cover and presentation definitions,
Mathlib's coproducts, shrunken Yoneda, and the universal property of wide
pullbacks. No new literature claim is used. No general existence of these cones,
compactness or equivariant structure on their points, or coefficient exactness
is proved here. Those remain inputs to the analytic comparison proof.
