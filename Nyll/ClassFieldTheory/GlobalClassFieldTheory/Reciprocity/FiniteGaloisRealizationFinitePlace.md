# Extending a finite place of L to the separable closure of ℚ

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationFinitePlace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension of number fields, embedded in ℚ̄ = `SeparableClosure ℚ` by the library's compatible embeddings. This file extends an extension w to L of a finite place v of K to an absolute value on ℚ̄.

- `numberFieldTowerFinitePlaceExtensionToSeparableClosure K L v w`: given v a height-one prime of 𝓞 K and w an extension of `adicAbv K v` to L, an extension of `adicAbv K v` to ℚ̄. It is built with `extendToAlgebraicallyClosed`.
- `..._algebraMap` (simp) and `..._restrict`: restricted to L along the chosen embedding, it is w itself, not a conjugate.

## Points to watch

- The extension to ℚ̄ is a choice; only its restriction to L is pinned down.
- The K- and L-algebra structures on ℚ̄ are supplied by `let` in each statement.
- The module heading mentions comparing decomposition data and completions; this file contains only the extension and its restriction.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FiniteGaloisRealizationFinitePlace.lean`: the Lean file is the source byte for byte (SHA-256 `d3ce5fcad5f7df63b1d81166c288ebaf6ddc4b457bc7ec6f3ffc2282193dd1dd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
