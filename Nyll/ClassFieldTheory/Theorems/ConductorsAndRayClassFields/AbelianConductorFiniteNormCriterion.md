# Finite conductor exponents and local norms

Module `Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteNormCriterion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields, and let `c` be a ray class modulus of K that is the abelian conductor of L/K (`IsAbelianConductor K L c`, the library's notion).

`IsAbelianConductor.finiteExponent_le_iff_higherUnit_le_tensorNorm`: for a finite place `v` of K and n ∈ ℕ, the exponent of `c` at `v` is at most `n` if and only if the higher unit group `rayLocalHigherUnitGroup v n` of the completion K_v lies in the image of the norm map on units (K_v ⊗_K L)ˣ → K_vˣ, where the norm is the determinant norm `Algebra.norm`.

The statement uses no place of L above `v`. The proof first identifies `c` with the conductor of the idele-class norm group, using that the abelian conductor is unique. Its exponent at `v` is the local conductor exponent, the least `n` whose higher unit group lies in the local norm group. The image of the tensor norm is shown to agree with the norm group of a chosen local extension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/AbelianConductorFiniteNormCriterion.lean`: the Lean file is the source byte for byte (SHA-256 `b884565934e4c2554824c619a34847962162ca0e1600234c50f561ee60931fbf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
