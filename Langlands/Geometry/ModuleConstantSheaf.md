# Constant module sheaf germs and actual stalk images

This internal helper concerns the actual stalk colimits of a constant
`ModuleCat R` sheaf, defined as the sheafification of the constant
presheaf. It uses any commutative coefficient ring and any topological
space, with one common universe for the ring, space and module values.
Its provenance is the sheafification unit's actual stalk isomorphism
and the defining naturality of germs. No literature theorem is asserted.

`constantSheafGerm V x` sends a constant vector in V through the
constant-presheaf sheafification unit on the whole space, then takes
its actual germ at x. `constantSheafGerm_surjective` proves that every
actual stalk element of this constant sheaf has this form. The proof
lifts an element through the isomorphism induced on stalks by the
sheafification unit, chooses a constant-presheaf germ representative,
and uses restriction of a global constant vector to replace that
representative by the whole-space germ of the same vector.

For a sheaf map f from this constant sheaf to an actual module sheaf M,
`constantSheaf_stalk_range` equates the linear range of the actual
stalk map of f with the range of the constant vectors, evaluated by f
on the whole space and then mapped to their M germs. The proof uses
the preceding surjectivity and naturality of the actual stalk map.
No connectedness, separation, local freeness or nonemptiness hypothesis
is required. This range comparison does not assert injectivity of f.
