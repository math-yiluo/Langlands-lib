# Dense indexed families of actual rational points

`HasDenseRationalPointFamily p` means that the union of the topological images of a specified indexed family of ground-field rational points is Zariski dense in the scheme. The index type may have an independent arbitrary universe. This differs from assuming only that all rational points together are dense: the equality criterion needs equality only on the specified family.

For a reduced source and separated target, `hom_ext_of_denseRationalPointFamily` proves that criterion by lifting each point in the family to the scheme-theoretic equalizer. The dense union makes the equalizer map dominant; the existing reduced-source, separated-target morphism theorem then gives equality. Neither algebraic closure nor finite type is required once the indicated density is supplied.

This is a derived internal extension of `RationalDensityExt.hom_ext_of_denseRationalPoints`, retaining its actual scheme-theoretic rational points and proof route. It provides a detection construction for the group-representation adapter and does not establish density for any new scheme.
