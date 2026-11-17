# Affine normal quotients supplied on an fppf cover

This internal construction descends supplied affine fppf quotients by a
represented normal subgroup from an arbitrary fppf cover of the base.
It is derived from the Library's effective affine fpqc quotient descent,
arbitrary-kernel open-cover quotient gluing, and finite affine refinement
of quasi-compact covers. The cover-refinement argument adapts the existing
étale-cover gluing construction to flat, locally finitely presented covers.

Let `G` and `N` be group schemes over a scheme `S`, with `G` affine over
`S`, and let `i : N ⟶ G` be a monomorphism in `Over S` whose full range
subgroup functor is normal. For every member of a supplied fppf cover,
assume that an affine group scheme and an actual fppf quotient by the
base-changed range of `i` have been supplied.

`exists_affine_fppfQuotient_of_fppfCover` constructs an affine group
scheme `M` over `S` and a homomorphism `r : G ⟶ M` which is the actual
fppf quotient by the full range of `i`. The definition
`affineFppfQuotientOfCover` chooses such a target and projection, retaining
the affineness and full quotient proofs in its return type.
No smoothness, reducedness, or finite type hypothesis is imposed on `N`
or `G`. Existence of the local quotient schemes remains an explicit premise.

The implementation first treats a finite affine fppf cover of an affine
base. Its disjoint union is an affine fpqc cover. The supplied local
quotients glue over the open cover of this disjoint union by the published
arbitrary-kernel open-gluing theorem. Effective affine fpqc descent then
descends the result to the affine base.

For an arbitrary fppf cover of an affine base, the component maps are open
because they are flat and locally of finite presentation. The existing
quasi-compact-cover refinement theorem gives a finite affine refinement.
The original quotient maps are pulled back to that refinement using the
published base-change composition comparisons, and the finite affine case
applies.

Finally, an arbitrary base is covered by its affine opens. The preceding
argument supplies quotients on each affine open. The same arbitrary-kernel
open-gluing theorem produces the global quotient. Every step retains
equality with the full represented kernel subgroup functor.
