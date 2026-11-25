# Norms at an infinite place

Module `Nyll.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The condition that an element of a number field `K` is a local norm from a finite extension `L` at an infinite place.

- `IsNormAtInfinitePlace K L w x`: for an infinite place `w` of `K` and `x ∈ Kˣ`, there is a unit `y` of `K_w ⊗[K] L`, where `K_w` is Mathlib's completion `w.Completion`, whose determinant norm is the image of `x` in `K_w`.

## Points to watch

The norm is taken from the whole algebra `K_w ⊗[K] L`, not from one completion of `L`; the file does not translate the condition into a sign condition at real places.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/NormTheorems/IsNormAtInfinitePlace.lean`: the Lean file is the source byte for byte (SHA-256 `695d8f51d88a799748c99663b0d78ab150446cae89b8b8013b45fbb298288742`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
