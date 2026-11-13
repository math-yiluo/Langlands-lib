# Restriction of coefficient algebras and actual point comparisons

For an O-algebra homomorphism φ : R → S, this module constructs the
restriction of commutative S-algebras to commutative R-algebras.
R and S and all their test algebras lie in the same universe.
The restricted structural map is the actual composite R → S → A.
An S-algebra homomorphism retains its underlying ring map, whose
R-linearity follows from its S-linearity. These constructions form
`restrictCoefficientFunctor φ`.

`coefficientPointEquiv M φ A` identifies the actual points of the
base-changed formal O-module M_S over A with those of M over the
restricted R-algebra A. Both sides consist of the same nilpotent
coordinate tuples. The equivalence and its inverse retain the tuple.
They are O-linear because mapping the coefficients of the addition
and scalar-action series successively along R → S and S → A equals
mapping them along the composite.

`Hom.coefficientPointEquiv_natural` proves compatibility with evaluated
formal-module homomorphisms by the same coefficient-substitution
identity. `coefficientPointEquiv_algebraMap` gives compatibility with
all S-algebra maps. Restricting the equivalence to the actual point
kernels gives `Hom.coefficientKernelEquiv` and the natural isomorphism
`Hom.coefficientKernelIso`.

This is internal coefficient-change infrastructure derived from the
formal-series definitions in `FormalModule`, `ModuleMorphism`,
`NilpotentAlgebras` and `KernelPoints`. It compares actual point
functors and kernels, without a representability assumption.
It supplies no finite kernel algebra, base-change theorem for rank or
isogeny, local gluing, or moduli representability.
