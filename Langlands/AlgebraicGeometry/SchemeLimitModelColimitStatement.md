# Actual relative Hom colimit comparison

This derived target expresses the natural Hom-colimit bijection in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(1), using the explicit quotient and canonical map
of `SchemeLimitModelColimit`. It retains the weaker individual hypotheses
of the factorization and equality criteria in `ModelMorphismDescent`.

All objects share an arbitrary universe `u`. Fix a small cofiltered category
`I`, a diagram `D : I ⥤ Scheme` whose values are affine, arbitrary schemes
`S`, `X` and `Y`, a compatible family `tᵢ : Dᵢ → S`, two morphisms
`a : X → S` and `b : Y → S`, and an actual limit cone `c` of `D` with its
`IsLimit` witness. Supply `p : c.pt → S` and the equations `c.πᵢ ≫ tᵢ = p`.
Neither the models `X`, `Y` nor `S` are assumed affine or separated.

The proposition `ModelHomColimitComparison` asserts three conclusions.

1. If `a` is quasi-compact and `b` is locally of finite type, then the
   canonical map `homColimitMap D t a b c p hp` is injective. Quasi-separatedness
   of `a` and local finite presentation of `b` are not premises of this clause.
2. If `a` is quasi-compact and quasi-separated and `b` is locally of finite
   presentation, then the same canonical map is surjective.
3. Under the hypotheses of clause 2, the map is bijective and the actual
   base-change cocone `homCocone D t a b c p hp` has an `IsColimit` witness.
   `Nonempty` expresses existence of that witness as a proposition. This is
   the categorical universal property of the supplied cocone with point
   `LimitHom a b p` and legs `toLimit i`.

The domain of the comparison is the quotient of the disjoint union of the
actual level relative Hom sets. The comparison sends a level representative
to its actual base change over the limit base. Its bijectivity and cocone
universal property are conclusions, not structural assumptions.

The provenance is derived. Conrad states the bijection for finitely presented
models over a directed system of rings. Taking opposite spectra recovers that
configuration. The present target generalizes to arbitrary cofiltered affine
base schemes over any fixed scheme, and it only requires quasi-compactness
and quasi-separatedness of the source model and local finite presentation
of the target. The separate `ModelMorphismDescent` factorization and eventual
equality criteria support these hypotheses; filtered type-colimit criteria
turn them into surjectivity and injectivity, and the canonical cocone then
has the colimit universal property.

This file defines a proposition, not its proof. The spectral specialization
from a directed ring colimit, initial model existence, property descent,
prescribed-isomorphism descent, arithmetic realizations, and topology are
separate units. The hypotheses in clause 1 are deliberately weaker than
those needed for clause 2.
