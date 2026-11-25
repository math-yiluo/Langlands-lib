# Primitive polynomials over a valuation ring

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.PrimitiveReduction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file relates primitivity of polynomials over a valuation ring V ⊂ K to their reduction, and proves the Gauss-lemma facts needed to factor a primitive polynomial into primitive pieces that are irreducible over K. Primitivity is Mathlib's `Polynomial.IsPrimitive`: every constant divisor is a unit.

## Main results

- `polynomial_isPrimitive_of_residue_ne_zero`: over any local ring, a polynomial with nonzero reduction is primitive.
- `exists_isUnit_coeff_of_isPrimitive` and `polynomial_residue_ne_zero_of_isPrimitive`: a primitive polynomial over V has a unit coefficient, hence a nonzero reduction. Together with the previous item, over a valuation ring primitivity is the same as nonzero reduction.
- `associated_of_isPrimitive_of_map_associated`: primitive f, g ∈ V[X] that are associated in K[X] are already associated in V[X].
- `isPrimitive_mul_of_valuationSubring`, with `Finset` and multiset versions: products of primitive polynomials over V are primitive (via Mathlib's content ideal).
- `exists_primitive_irreducible_lift_of_irreducible`: every irreducible p ∈ K[X] is associated to the image of a primitive irreducible q ∈ V[X].
- `primitive_associated_prod_primitive_irreducible_map_factors`: a primitive f ∈ V[X] is associated in V[X] to a finite product of primitive polynomials whose images in K[X] are irreducible.

A helper lemma says that termwise associated factors have associated multiset products.

## Proof

The key step divides by a coefficient of maximal valuation: it divides every other coefficient in V, which yields the unit coefficient and the primitive rescaling of an irreducible p. The factorization takes the normalized factors of f in K[X], lifts each, and descends the resulting association from K[X] to V[X].

## Points to watch

- The namespace is `DiscreteValuationField`, but V is an arbitrary valuation subring; no discreteness is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/PrimitiveReduction.lean`: the Lean file is the source byte for byte (SHA-256 `830bb7b47dac6227153d09bdb7abef30dbad3cb7e11b64865eca6f7adfe24299`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
