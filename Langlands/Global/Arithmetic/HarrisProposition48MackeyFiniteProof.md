# The auxiliary finite component of the Harris Mackey character

These lemmas give the finite-place calculation for the raw character in the
proof of Harris’s Proposition 4.8 (1998, printed pp. 202–203, TeX lines
1574–1614 and 1630–1648). The norm is taken from the actual compositum
`D · a(E')` to `a(E')`, and the place of `a(E')` is the image of the parent
auxiliary place of `E'` under the inverse image map for the inverse of `a`.

The transported place still lies above the parent base place since `a` fixes
`E`. Uniqueness in the parent closure gives uniqueness in `a(E')`, so the
compositum place and the parent closure place both restrict to this transported
place. The finite component formula is the one-place idele norm formula
followed by transport through the completed inverse of the conjugate
embedding. On the completed parent normal closure, this inverse agrees with
the given continuous extension of `a⁻¹` by the equality on dense global
elements.

`mackeyCharacter_finiteComponent_localNorm` uses the literal restriction
of the parent auxiliary top place to the compositum. Parent place
compatibility identifies the parent inducing completion with `Q.F'` by
restricting the completion map to its range. The given automorphism `τ`
then identifies the conjugate inducing completion with `Q.F'.conj τ`.
Composition of completion maps in the tower makes this identification
commute with a supplied identification of the compositum completion in
the same ambient closure. The norm transport theorem carries the
determinant norm through that square. Applying the parent's component
identity gives the character `Q.χs` evaluated on the resulting norm after
inverse conjugation.

`MackeyChild.CompletedBase.parentInducingField_eq` compares the actual child
inducing completion with the compositum in the parent's algebraic closure.
The completion correspondence at the unique auxiliary place preserves joins,
as does embedding its fields into the parent's algebraic closure. The
commuting square for the completed base gives `T.field` as the image of `D`,
and the conjugation square gives `(Q.F'.conj τ).field` as the image of
`a(E')`. The child completion is carried across the chosen closure
isomorphism by `parentInducingEquiv`. Its composite with the child place
map agrees with the inclusion of the literal compositum completion into
the parent's algebraic closure.

`MackeyChild.CompletedBase.place_hasComponent` uses that agreement to
verify the component identity at the child's actual auxiliary place.
The defining equality of `HasComponent` identifies the given local unit
with the image of the unit in the number-field completion. The previous
norm formula therefore evaluates the finite component on the same unit
as the transported local character. The lemma accepts any continuous
local character with this pointwise norm formula.
