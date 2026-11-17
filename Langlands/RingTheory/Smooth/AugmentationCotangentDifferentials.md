# Augmentation cotangents and pulled-back Kähler differentials

Let `R` and `A` be commutative rings in independent universes, with algebra
structures `R → A` and `A → R` and a compatible scalar tower `R → A → R`.
The outer `R`-algebra structure on `R` is its identity structure, so the
composite is the identity. Write `ε` for the resulting
`augmentation R A : A →ₐ[R] R`, and put `I = ker (algebraMap A R)`.

This is an internal algebraic bridge for the actual cotangent sheaf.
It combines the Library's universal augmentation class map from
`CoordinateWeights.AugmentedAlgebra` with Mathlib's Kähler universal
property and the canonical map
`KaehlerDifferential.kerCotangentToTensor`. It adds no external source claim.
No smoothness, finite type, projectivity, field or noetherian hypothesis
is used.

`cotangent_smul` proves that the natural action of `a : A` on the actual
cotangent module `I/I²` equals multiplication by `ε(a)` through its
`R`-module structure. The proof writes
`a = (a - algebraMap R A (ε a)) + algebraMap R A (ε a)` and uses the fact
that `I` annihilates `I/I²`. This supplies the local scalar tower needed
for extension of scalars through `A → R`.

`classDerivation` packages the actual augmentation class map as a
derivation `A → I/I²` relative to `R`. Its product rule follows from
the augmentation class product rule and the scalar factorization above.

`toTensor` is Mathlib's canonical map, restricted to base scalars,

`I/I² →ₗ[R] R ⊗[A] KaehlerDifferential R A`.

`toTensor_toCotangent` computes its value on an actual ideal class as
`1 ⊗ d(a)`. The map `fromTensor` in the opposite direction lifts
`classDerivation` through the universal differential module and then
extends scalars along the augmentation. `fromTensor_tmul_D` computes it
on differential tensors as `r ⊗ d(a) ↦ r • [a - ε(a)]`.

`toTensor_classMap` proves that applying the forward map to the
augmentation class of any `a` gives `1 ⊗ d(a)`, since differentials
of base constants vanish. The left inverse identity is checked on
the surjective ideal-class generators. The right inverse identity
uses the tensor base-change universal property and uniqueness of
maps out of Kähler differentials, then checks differential generators.

`cotangentEquivTensor` is the resulting `R`-linear equivalence with
forward map exactly `toTensor` and inverse exactly `fromTensor`.
For an independently specified augmentation, one may install its
`A`-algebra structure on `R` and the scalar-tower witness coming from
its `R`-algebra homomorphism law, then apply this construction.
The module does not yet identify sections of the actual scheme
cotangent sheaf or assert a sheaf restriction comparison.
