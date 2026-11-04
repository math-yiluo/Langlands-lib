# Dominant representatives by positive uniformizer translation

Author: Worker 1292.

This derived helper works with actual rational points, the actual centralizer
valuation and the full-lattice residue from the published Renard interfaces.
It assumes finite positive-root support, and for the finite transversal also
finite index of the split valuation image. These structural inputs remain
explicit and are not proved here.

`uniformizerTranslate s ν n z` multiplies `z` on the left by the uniformizer
value of `n • ν`, for a natural number `n`. That multiplier is in `C0`, so
its integer valuation lies in the split valuation image. Its full-lattice
residue is therefore the identity, and translation preserves the residue.

`exists_uniformizerTranslate_mem_dominant` bounds above the negatives of all
positive-root orders of `z`. Finite support gives one real bound. Choose a
natural number at least that bound. Every positive root pairs positively
with `ν`, by the definition of positive roots. Its integral pairing is thus
at least one. Uniformizer normalization and additivity show that translating
by that natural multiple of `ν` makes every root order nonnegative. The
argument needs no genericity beyond the definition of the positive roots.

`latticeResidue_surjOn_dominant` first represents an arbitrary quotient class
by an actual point, using surjectivity of the valuation onto its actual range
and of the quotient map. The translation above gives a dominant point in
the same residue. `exists_finite_dominant_latticeTransversal` chooses one
such point for each element of the finite quotient. The range is finite,
its residue map is bijective, and every chosen point is dominant.

The provenance is elementary finite-order and quotient reasoning applied
to the published actual objects, with normalization imported from
`RenardDominantValuation`. The conclusion is the exact imported
`IsFiniteLatticeTransversal` predicate together with dominance. No equality
between positive products and the dominant intersection, or uniqueness of
positive products, is claimed. The full host theorem still requires published
structural inputs and its other conclusions.
