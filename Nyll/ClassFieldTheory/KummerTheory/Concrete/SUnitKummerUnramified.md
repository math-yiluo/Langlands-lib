# The full S-unit Kummer extension is unramified outside S and n

Module `Nyll.ClassFieldTheory.KummerTheory.Concrete.SUnitKummerUnramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a number field containing the `n`-th roots of unity, with `n ≠ 0` in `K`, and `S` a finite set of finite places. The full `S`-unit Kummer extension `K(√[n]{Kˢ})`, formed in a separable closure `Ω` of `K`, is unramified at every finite place outside `S` at which `n` is a unit. This is the ramification input in the library's existence proof for the global norm topology.

## Main results

- `adjoin_rootUnit_eq_chosenSimpleKummerExtension`: if `α` is a nonzero root of `X ^ n − b` in `SeparableClosure K`, with `b ∈ Kˣ` and a primitive `n`-th root of unity in `K`, then `K(α)` is the library's chosen simple Kummer extension `chosenSimpleKummerExtension K n hn b`.
- `exists_sUnit_chosenSimpleKummerExtension_eq_adjoin_of_mem_fullRootSet`: every defining root `β` of the full extension generates the chosen simple Kummer extension of some `S`-unit.
- `exists_sUnitRootUnit_generating_internalAdjoin`: the same inside an intermediate field `E` of `Ω`: `K(β)` has a generator `α` with `α ^ n` an `S`-unit `u`, and `K(β)` is isomorphic over `K` to the chosen simple Kummer extension of `u`. Consequently `fullSUnitKummerRoot_internalAdjoin_isGalois`: `K(β)/K` is Galois.
- `fullSUnitKummerExtension_chosenFinitePlaceIsUnramified_of_not_mem`: for a finite place `v ∉ S` with `v(n) = 1`, the full extension is unramified at its chosen place above `v` (`ChosenFinitePlaceIsUnramified`).
- `fullSUnitKummerExtension_isUnramifiedAt_of_below_not_mem`: every prime `P` of the full extension whose place below lies outside `S` and has `v(n) = 1` is unramified over `𝓞 K` (`Algebra.IsUnramifiedAt`).
- Two helper results compare adjoining an element inside an intermediate field with adjoining it in the ambient field.

## Proofs

Defining roots are rescaled to roots of `S`-units with a lemma from another file. A root of `X ^ n − b` and the chosen root generate the same field because each lies in the other's Kummer radical closure. For unramifiedness, a finite set of defining roots generates the full extension; each simple field `K(α)` is unramified at places where `u` and `n` are units, by `kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one`; so the inertia group of each simple field is trivial, and `inertiaGroup_eq_bot_of_finset_adjoin_eq_top` gives trivial inertia for the compositum.

## Remarks

- The hypothesis `v(n) = 1` excludes the places above primes dividing `n`; the statement says nothing at those places.
- The finite-dimensionality, Galois and number-field structures of the full extension are bound with `let` in the statements, taken from `fullSUnitKummerExtension_finiteDimensional` and `fullSUnitKummerExtension_isGalois`.
- `ChosenFinitePlaceIsUnramified` is the library's notion, at one chosen place above `v`; the last theorem passes to every prime above `v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/KummerTheory/Concrete/SUnitKummerUnramified.lean`: the Lean file is the source byte for byte (SHA-256 `834a79c72148b1958c18daa996763c35cf6374a29fa8465207e587aabaa87115`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
