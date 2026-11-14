# A fixed-direction criterion for special-apartment chambers

This internal reduction retains the exact proposition
`UnramifiedSpecialApartmentChamberStatement.{u}` and all of its original
hypotheses. It isolates an arithmetic root nonvanishing obligation.

For any supplied stable coefficient apartment over a field extension `K/k`,
`KPApartmentData.HasIncidentGaloisDirections k K i D p` is a proposition
about its actual ordinary affine roots and reduced translation space. For
each ordinary root `ψ` vanishing at `p`, it requires a translation vector
fixed by every actual linear coefficient action on which `ψ.linear` is
nonzero. The vector may depend on the root. No compatibility datum or
fixedness of `p` is implicit in this definition.

`KPApartmentData.exists_regular_galois_stable_facet_of_directions` assumes
an integer-valued valuation, connected reductivity of the scalar-extended
group, maximal splitness of the supplied torus, full V6 compatibility with
a supplied centralizer, coefficient stability, a coefficient-fixed point,
and the direction predicate at that point. It concludes the exact
regular-point and invariant-whole-facet existential in the same apartment.
The proof bundles the supplied data with `integerBuildingData` and obtains
local finiteness from the published actual opposite-factor-pair theorem.
It then applies `exists_regularPoint_fixed` from
`AffineInvariantRegularPoint` and the existing `image_facet_galois`.

`UnramifiedSpecialApartmentRegularDirectionStatement` is an unproved
arithmetic proposition at every universe `u`. It retains all the special
torus data of the chamber statement: the prescribed maximal base-field
split torus, its factorization through the closed commutative subgroup,
maximal splitness after the maximal unramified extension, every compatible
apartment and centralizer, and coefficient stability. At every point fixed
by the actual affine coefficient action it asks for
`HasIncidentGaloisDirections`. There is no splitting, anisotropy, residue
characteristic, or field characteristic hypothesis.

`unramifiedSpecialApartmentChamber_of_regularDirection` proves the
implication from this new arithmetic proposition to the unchanged
`UnramifiedSpecialApartmentChamberStatement`. The existing theorem
`unramifiedGaloisFixedApartment` supplies the initial point.
`KPApartmentData.Apartment.ext` turns its root-family fixedness into actual
affine fixedness. The new direction proposition then supplies precisely
the premise of the fixed-data criterion above. Algebraic-extension
ascent supplies connected reductivity upstairs.

The reduction is internal and derived from the published geometric
construction and fixed-point theorem. It does not assert the new
arithmetic direction statement or the chamber target unconditionally.
In a residual-group proof, the remaining input must compare ordinary
roots through a fixed point with residual roots and show that their
restrictions to fixed directions are nonzero. Merely knowing a fixed
point or a stable chamber elsewhere does not discharge that input.
