# Faithfulness of affine analytification

The product map is defined for a finite polynomial presentation over a
nontrivially normed ultrametric field `K`. Its injectivity and the results
on localized affine morphisms also assume `K` is complete. The field and
the two presented algebras may be in independent universes.

To detect a nonzero element of a finitely generated algebra, take a
maximal ideal containing its annihilator. The intersection of the powers
of that maximal ideal excludes the element by the Noetherian
intersection theorem. The quotient by the corresponding power is
finite over the ground field by Zariski's lemma and finiteness ascent
across a finitely generated nilpotent kernel. This algebraic step works
over any field.

The regular representation on a finite product of copies of the ground
field equips this quotient with its operator norm. The quotient is
ultrametric by the operator norm inequality and complete by finite
dimensionality over the complete field. At a polydisc radius bounding
the norms of the generators in this quotient, Tate evaluation extends
the quotient map. It descends through the closed relation ideal to give
a factorization through a polynomial-locus chart algebra. Thus equality on every chart
detects the original algebra elements, including nilpotents. The algebra
map `chartAlgebraProductMap` is the product of the maps to all these
charts.

The bounded pullback maps of an affine analytification recover each
algebra map on the selected original charts. The bounded equivalences
between each chart and its selected representative give the same
equalities on every chart. The product map's injectivity therefore makes
the assignment of original strong maps injective. The published
separation results for saturation and localization then give
`localizedHom_injective` for two algebra maps with the same presented
source and target.

If an affine analytification map is epimorphic, compare two maps to the
analytified affine line induced by elements with equal images under
the algebra map. Functoriality gives equal composites with the
epimorphism. Cancellation and faithfulness give equality of the two
algebra maps out of the polynomial ring. Evaluating on its variable
gives equality of the original elements.

This is internal derived infrastructure for comparing the closed affine
overlaps of separated algebraic spaces.
