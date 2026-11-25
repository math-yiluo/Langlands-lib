# Unramified at all finite places

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The condition that an extension of number fields `L/K` is unramified at every finite prime of `K`.

- `IsUnramifiedAtFinitePlaces K L`: for every finite prime `v` of `𝓞 K`, Mathlib's `Algebra.IsUnramifiedIn (𝓞 L) v` holds.

## Points to watch

Infinite places are not constrained: a real place of `K` may ramify.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/IsUnramifiedAtFinitePlaces.lean`: the Lean file is the source byte for byte (SHA-256 `a8ab788de5799091c66c78d4c18ed6455b84bf4ecf3b482ebac73aeb900e46b1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
