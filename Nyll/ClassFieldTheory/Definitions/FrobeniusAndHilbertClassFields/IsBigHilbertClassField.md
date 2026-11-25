# The big Hilbert class field

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A predicate for the maximal finite abelian extension of a number field `K` that is unramified at all finite primes, real places being allowed to ramify.

- `IsBigHilbertClassField E`: for a finite abelian extension `E` of `K` inside `SeparableClosure K`, `E` is unramified at every finite prime (`IsUnramifiedAtFinitePlaces`), and every finite abelian extension `F` unramified at every finite prime admits a `K`-algebra embedding `F →ₐ[K] E`.

## Points to watch

- Ramification at real places is allowed, so this is in general larger than the usual Hilbert class field, which the library calls `IsSmallHilbertClassField`.
- Containment is expressed by the existence of a `K`-embedding, not by inclusion of subfields of `SeparableClosure K`.
- Only the predicate is defined; existence is not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/IsBigHilbertClassField.lean`: the Lean file is the source byte for byte (SHA-256 `d4955a62925edfa671a13e7b1db78138613cd232c1ad741369dbcd9b7d953297`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
