# Norms at a finite place

Module `Nyll.ClassFieldTheory.Definitions.NormTheorems.IsNormAtFinitePlace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The condition that an element of a number field `K` is a local norm from a finite extension `L` at a finite prime.

- `IsNormAtFinitePlace K L w x`: for a finite prime `w` of `K` and `x ∈ Kˣ`, there is a unit `y` of `K_w ⊗[K] L` whose determinant norm `Algebra.norm K_w y` is the image of `x` in the completion `K_w`.

## Points to watch

The norm is taken from the whole algebra `K_w ⊗[K] L`, not from one completion of `L`. The file does not relate this predicate to `finitePlaceTensorNormSubgroup`, which uses the same norm map.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/NormTheorems/IsNormAtFinitePlace.lean`: the Lean file is the source byte for byte (SHA-256 `96e26ee60b867937245fbd736c38d571f83a33549d3025c0b6dc07872f6f0b55`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
