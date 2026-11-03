# Finite algebra approximation of actual Picard arrows

This internal unit translates the section and equality descent interfaces into
statements about actual arrows between restricted line-bundle families. It
uses the relative Picard pseudofunctor and its coherent Hom presheaf, together
with the section and equality descent helpers. It also applies the published
theorem `properLineBundleHomRepresentability` to discharge representability
for a proper, flat, locally finitely presented morphism.

For an affine map `t : Spec R → S`, the two families `L` and `M` live on the
actual relative total space above `t`. `affineFamilyBaseArrow t A` is the
slice arrow induced by the actual structure map `Spec A → Spec R`.
`AffineFamilyArrow` is the type of actual Picard arrows between the ordinary
restrictions of these families. `affineFamilyArrowRestrict` retains the
composition comparisons in the existing relative Isom presheaf. The displayed
`pullHom` identity specifies those comparisons.

An arrow between the two original families is equivalent to a section on the
identity affine base. The construction combines the pseudofunctor's identity
comparison, the unit of the iterated-slice equivalence and the explicit universe
lift. Restricting that section gives precisely the ordinary pullback of the
original arrow. The proof first checks the generic identity-restriction formula
for a pseudofunctor Hom presheaf, then uses functoriality and equality of the
composed slice arrows. Thus there is no replacement of the specified arrow by
an arbitrary isomorphic arrow.

The chosen-arrow theorem applies section descent and takes the value out of
its universe lift. The equality theorem transports two original arrows through
the identity-section equivalence, applies equality descent and uses the
restriction formula on both sides. Both conclusions preserve any prescribed
finite coefficient set, and all rings and geometric objects retain universe
`u`.

`HasAffineFamilyArrowApproximation f t L M` is the conjunction of those two
actual-arrow properties, with their full quantifiers and exact restriction
equalities. The `_of_descent` theorem pairs the two adapters. The
`_of_isomRepresentability` theorem obtains their inputs from the section and
equality descent helpers; `_of_homRepresentability` applies the published
Hom-to-Isom implication first. These three theorems retain their named premises.

Finally, `hasAffineFamilyArrowApproximation` applies the last conditional
theorem to the published, universe-polymorphic
`properLineBundleHomRepresentability`. Its only geometric hypotheses are
properness, flatness and local finite presentation of `f`. It has no
representability premise. The base ring and the test algebra are arbitrary
commutative rings at universe `u`. No noetherian, flatness or finite-type
condition is imposed on the test algebra.

This is an internal consequence of the existing approximation and
representability results, with the identity-section comparison proved here.
It supplies the two displayed finite-stage properties. It does not assert a
filtered-colimit category equivalence, infinitesimal gluing or existence of a
smooth chart.
