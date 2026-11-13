# Integral and rational formal Hom on Spec R

This module constructs the actual Zariski sheaf of rational morphisms
between fixed finite-coordinate formal O-modules M and N over R. It uses
the existing power-series homomorphisms and Mathlib's structure sheaf and
categorical sheafification. No representing object is supplied as input.

`coefficientStructurePresheaf R` is Mathlib's structure presheaf of
Spec R with the structural R-algebra on each ring of sections retained.
Its restriction maps are the actual structure-sheaf restriction maps.
Composing it with `algebraHomFunctor M N` gives
`integralHomPresheaf`; its value on U is the O-module of formal
homomorphisms after extending the coefficients to Γ(U, O_Spec R).
`integralHomSheaf` is the associated O-module sheaf when O and R are in
the same universe, as required by the available filtered-colimit instance.

`rationalHomPresheaf F M N` has value
F tensor_O Hom(M over Γ(U), N over Γ(U)). Its restriction maps are the
coherent tensor extensions already constructed in `AlgebraHomFunctor`.
`rationalHomSheaf` applies genuine categorical sheafification in
F-modules for the Zariski topology. In particular its global sections
are defined by the sheaf construction, without assuming that they are
all images of global tensors with uniformly bounded denominators.

`RationalSection` is the F-module of sections on any open set.
`ofRational` is the sheafification unit, `restrict` is the restriction
map, and the proved identities give identity, composition and
compatibility of restrictions with the unit. `ofGlobal` sends the
original global tensor Hom into this sheaf, extending coefficients to
the global sections of the actual structure sheaf first. Injectivity or
surjectivity of this last map is not asserted.

The provenance is internal: this supplies a concrete construction of
the rational Hom sheaf needed for the local quasi-isogeny definition.
Its relation to a separately defined sheaf of morphisms between formal
schemes is not established here. The field and base ring have the same
universe; for the rational construction the coefficient ring O may have a
different universe.
