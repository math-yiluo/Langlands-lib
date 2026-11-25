# Base change of a prime-degree extension to K(μ_p)

Module `Nyll.ClassFieldTheory.KummerTheory.Concrete.CyclotomicPrimeBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be an extension of number fields of prime degree `p`. The cyclotomic field `K(μ_p)` has degree at most `p − 1` over `K`, so its degree is coprime to `p`. This file deduces that the tensor product `K(μ_p) ⊗[K] L` is a field, of degree `p` over `K(μ_p)`, and, when `L/K` is Galois, Galois over `K(μ_p)` with cyclic group of order `p`. This is the base change that places a prime-degree extension in the setting of Kummer theory.

## Main definitions and results

- `cyclotomicField_finrank_le_totient`: over a field of characteristic zero, `CyclotomicField m F` has degree at most `φ(m)`, for `m > 0`.
- `PrimeCyclotomicBase K p` is `CyclotomicField p K`, a finite Galois extension of `K` and a number field; `primeCyclotomicBase_finrank_lt` gives degree `< p` for prime `p`, and `primeCyclotomicBase_primitiveRoots_nonempty` gives a primitive `p`-th root of unity in it.
- `PrimeCyclotomicPushout K L p` is `K(μ_p) ⊗[K] L`. Assuming `p` prime and `[L : K] = p`:
  - `primeCyclotomicBase_finrank_coprime`: the two degrees are coprime;
  - `primeCyclotomicPushoutField`, `primeCyclotomicPushoutAlgebra`: the field structure and the `K(μ_p)`-algebra structure on the tensor product;
  - `primeCyclotomicPushout_finrank`: its degree over `K(μ_p)` is `p`; `primeCyclotomicPushout_numberField`: it is a number field;
  - `primeCyclotomicPushout_isGalois` and `primeCyclotomicPushout_isCyclic`: it is Galois over `K(μ_p)` with cyclic Galois group, these two using `[IsGalois K L]`;
  - `primeCyclotomicPushoutGalEquivPiZMod`: an isomorphism of that Galois group with `Fin 1 → Multiplicative (ZMod p)`.

## Proofs

The degree bound compares the minimal polynomial of a primitive root with the cyclotomic polynomial. The field and Galois statements come from the library's results on tensor products of extensions of coprime degrees (`tensorProduct_isField_of_finrank_coprime`, `tensorProduct_isGalois_of_finrank_coprime`); the degree from Mathlib's `Module.finrank_baseChange`; cyclicity from the prime order of the group.

## Remarks

- The field structure on the tensor product is not an instance: the statements bind it, and the algebra structure, with `let` inside their types, so they must be used with these same structures.
- The isomorphism with `Fin 1 → Multiplicative (ZMod p)` is built from an arbitrary choice of generator (`zmodCyclicMulEquiv`); it is not a canonical Kummer pairing.
- `K` and `L` are taken in the same universe (`K L : Type u`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/KummerTheory/Concrete/CyclotomicPrimeBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `32ba471b8c73afd1010ea3f1d5970316ed75dfe53cdcbb867b9043d549cca343`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
