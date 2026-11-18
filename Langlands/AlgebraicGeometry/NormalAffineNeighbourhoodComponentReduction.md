# Reduction to integral schemes

This derived construction supplies the final disconnected-scheme
reduction for Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4.
It is a reduction with an explicit integral-constructor parameter, not
the unconditional affine-neighbourhood constructor.

`normal_stalks_of_isOpenImmersion` transports the domain and integral
closedness of all stalks to an open subscheme using the stalk-map ring
isomorphisms. `ringKrullDim_stalk_eq_of_isOpenImmersion` transports
the stalk dimension. `separatedScheme_of_affine_base` proves absolute
separatedness for a scheme separated over an affine base.

The constructor `normalAffineNeighbourhoodOfIntegralConstructor` takes
an actual affine-neighbourhood constructor for integral separated
locally noetherian schemes locally of finite presentation over
`Spec R`. It then produces affine neighbourhoods under the full
noetherian-base hypotheses: a locally finite type, quasi-compact,
separated morphism to `Spec R`, domain and integrally closed stalks,
and a finite set with the dimension bound.

The morphism hypotheses make the source a noetherian scheme. Its
domain stalks give disjoint integral open irreducible components.
Each component inherits normal stalks, separatedness, local
noetherianity and local finite presentation over the base. The finite
set and its dimension bound pull back along the component inclusion.
Applying the supplied integral constructor in each component and the
finite disjoint affine-open assembly gives the resulting open.
The empty scheme and empty selected set are included. All declarations
work in every universe.
