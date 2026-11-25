# Near lifts along a strong map

`HasStrongNearLifts g` is the existence part of Berkovich's Key Lemma 7.2
(*Vanishing cycles for formal schemes*, Invent. Math. 115, 1994) for
commutative squares, stated for a strong map `g : T ⟶ B` of saturated
atlas presentations. The definition is internal to this formalization.
For every finite set `E` of test triples on `T` there is a finite set
`D` of test triples on `B` with the following property. Let `x : S ⟶ T`
and `y : S ⟶ B` be strong maps with `StrongNear τ y (x ≫ g)` for every
`τ` in `D`. Then there are a quasi-isomorphism `r : S' ⟶ S` and a strong
map `x' : S' ⟶ T` with `x' ≫ g = r ≫ y` and `StrongNear τ x' (r ≫ x)` for
every `τ` in `E`.

The quasi-isomorphism `r` lets a lift be built on a refinement of the
source atlas, where it is glued from local lifts. In the localized
category `r` is invertible, so the property yields near lifts of
morphisms of analytic spaces.
