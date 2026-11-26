# Local actions of Hecke twists of cuspidal presentations

`heckeTwistAtCompletionEquiv` identifies the actual finite component of
a Hecke determinant twist of a cuspidal spectral presentation with the
determinant twist by the local quasicharacter on the original component.
The proof uses the pointwise expression for the finite determinant
character and the equivalences for the local and global twists.

`heckeDoubleTwistAtCompletionEquiv` identifies the finite component
after two twists with the local twist by their product. The product is
written in the order of the second character times the first, as in
the Library's twist composition identity.
`heckeTwistAtCompletionEquiv_of_trivial` gives the equivalence with
the original local component when the Hecke character is trivial at
the given place.

`heckeTwistDualAtCompletionEquiv` takes an original cuspidal spectral
presentation, a presentation of its actual global contragredient, and
a presentation of the actual contragredient of its Hecke twist. Each
of the three presentations has irreducible admissible finite
components. The inverse Hecke twist of the original contragredient
and the supplied contragredient of the twist both identify locally
with the smooth contragredient of the twisted forward component.
Composing these local equivalences yields the asserted nonempty
equivalence at every finite place.
