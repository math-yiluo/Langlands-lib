# Hensel factorization from reductions of primitive irreducible factors

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.PrimitiveFactorization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a valuation ring V ⊂ K, this file shows that Hensel's factorization lemma follows from a condition on the reductions of primitive polynomials that are irreducible over K. Unique factorization in K[X] then distributes the irreducible factors of f along any coprime factorization of its reduction. According to the module comment, this is the common last step of the unique-extension criterion and the factor-lifting criterion.

## Definition

- `PrimitiveIrreducibleReductionProperty V`: for every primitive Q ∈ V[X] with Q irreducible over K, the reduction Q̄ has degree 0 or degree deg Q, and Q̄ has no factorization Q̄ = a·b into coprime factors that both have positive degree. The second clause is a factorization-free way of saying that a nonconstant Q̄ is a scalar times a power of one irreducible polynomial.

## Main results

- `primitiveIrreducibleReduction_dvd_left_or_right_of_coprime`: under the property, if Q̄ divides ḡ·h̄ with ḡ, h̄ coprime, then Q̄ divides ḡ or h̄.
- `partition_primitive_irreducible_factors_along_coprime_reduction`: given finitely many such Q whose reductions multiply to ḡ·h̄ with ḡ, h̄ coprime, their product is G·H with G reducing to ḡ, H reducing to h̄, and deg G = deg ḡ.
- `henselFactorization_of_primitiveIrreducibleReductionProperty`: the property implies `HenselFactorizationProperty V` (defined in an earlier file): whenever f ∈ V[X] has nonzero reduction f̄ = ḡ·h̄ with ḡ, h̄ coprime, there are G, H ∈ V[X] with f = G·H, G and H reducing to ḡ and h̄, deg G = deg ḡ and deg H ≤ deg f − deg ḡ.

## Proof

Nonzero reduction makes f primitive, so f is associated to a product of primitive factors irreducible over K, by the file on primitive reductions. Induction over the factors puts those with constant reduction into H and each other factor on the side its reduction divides; the degree clause of the property gives the exact degree of G, and the remaining unit is absorbed into H.

## Points to watch

- `PrimitiveIrreducibleReductionProperty` is the library's own hypothesis; this file does not show that any valuation ring satisfies it, it only derives Hensel factorization from it.
- The factorization keeps the exact degree only for G; H gets an upper bound, and neither factor is stated to be monic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/PrimitiveFactorization.lean`: the Lean file is the source byte for byte (SHA-256 `59c53f45b1be8c5bd4b469f8e7234b58f216d238db9a685508e587e2aa218266`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
