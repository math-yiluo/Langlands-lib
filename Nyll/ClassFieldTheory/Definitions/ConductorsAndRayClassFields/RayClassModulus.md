# Ray class moduli

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A modulus of a number field `K` is a finitely supported exponent function on the finite primes together with a finite set of real places. The file defines moduli and their divisibility lattice.

- `RayClassRealPlace K`: the real infinite places of `K`, a subtype of `InfinitePlace K`.
- `RayClassModulus K`: a structure with `finitePart : HeightOneSpectrum (𝓞 K) →₀ ℕ` and `infinitePart : Finset (RayClassRealPlace K)`; `RayClassModulus.ext` gives equality from equality of both parts.
- Partial order: `m ≤ n` means `m.finitePart v ≤ n.finitePart v` at every finite prime `v` and `m.infinitePart ⊆ n.infinitePart` (`le_iff`), that is, `m` divides `n`.
- Lattice: the meet takes minimum exponents and intersects the sets of real places, the join takes maximum exponents and their union; `finitePart_inf`, `finitePart_sup`, `mem_infinitePart_inf` and `mem_infinitePart_sup` describe them.

## Points to watch

The modulus is the library's own structure: its finite part is an exponent function, not an ideal of `𝓞 K`, and complex places cannot occur.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassModulus.lean`: the Lean file is the source byte for byte (SHA-256 `ee5c055b4e1a6eb0faed17b2ef33223279518581c20dbd3532b5309fc841a82b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
