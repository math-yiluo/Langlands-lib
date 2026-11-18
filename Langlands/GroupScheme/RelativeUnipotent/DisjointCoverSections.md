# Sections on an actual disjoint scheme open cover

This internal module for the relative radical filtration identifies sections of
an actual module on a scheme with families of sections on the actual component
pullbacks of a disjoint open cover. The equivalence uses canonical section
pullback. It assumes neither quasi-coherence nor a finite or nonempty index set.

On distinct pieces, the overlap is empty, so all module morphisms there agree.
On a repeated piece, the two pullback projections agree by monicity of the open
immersion. Their canonical square comparison reduces to the identity. Thus any
family of actual module morphisms is compatible, and the existing open-cover
module-morphism gluing theorem applies.

For sections, use their module morphisms from the structure sheaf, conjugated
by the canonical pullback unit comparison. Gluing these morphisms gives a
global section with the prescribed component sections. Uniqueness follows by
joint detection of module morphisms and the injectivity of the section-morphism
identification. Additivity is that of canonical section pullback.

This derived construction supplies the section side of all-test coordinates for
the finite disjoint face-chart cover. It does not construct the later linear
transition cocycle or prove that a descended global quotient is a vector bundle.
