# The small Hilbert class field

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A predicate for the Hilbert class field of a number field `K` in the usual sense: the maximal finite abelian extension unramified at every place, real places included.

- `IsSmallHilbertClassField E`: for a finite abelian extension `E` of `K` inside `SeparableClosure K`, `E` is everywhere unramified (`IsEverywhereUnramified`), and every everywhere unramified finite abelian extension `F` admits a `K`-algebra embedding `F →ₐ[K] E`.

## Points to watch

Containment is expressed by the existence of a `K`-embedding, not by inclusion of subfields of `SeparableClosure K`. Only the predicate is defined; existence is not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/IsSmallHilbertClassField.lean`: the Lean file is the source byte for byte (SHA-256 `323969b4f750a4410166017fa5fd7406bf36f4e4df80f63a3663b341ea055c50`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
