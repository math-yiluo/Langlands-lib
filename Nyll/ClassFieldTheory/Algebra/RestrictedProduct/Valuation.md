# Valuation vectors on restricted products of valued fields

Module `Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a family of fields Fᵢ, each with a valuation into ℤᵐ⁰ (Mathlib's `Valued (F i) ℤᵐ⁰`), this file sends the restricted product of the unit groups Fᵢˣ with respect to the integral units 𝒪ᵢˣ to the free abelian group on the index set, by taking orders at each index. The file comment presents this as the common construction behind valuation vectors of number-field and function-field ideles.

## Definitions and results

- `localOrder F`: the order x ↦ −log v(x) as a homomorphism Fˣ → ℤ; it vanishes exactly on the integral units (`localOrder_eq_zero_iff`, using `mem_localUnits_iff`: v(x) = 1).
- `chosenLocalOrderSection F hval n`: if v is surjective, a chosen unit of order n.
- `UnitProduct F`: the restricted product of the Fᵢˣ relative to the 𝒪ᵢˣ; only finitely many components lie outside 𝒪ᵢˣ (`finite_nonLocalUnits`).
- `valuationVector F`: the homomorphism from `UnitProduct F` to the finitely supported functions ι →₀ ℤ (written multiplicatively), sending a to (ordᵢ(aᵢ))ᵢ.
- `valuationVector_ker`: its kernel is `integralSubgroup F`, the families that are integral units at every index.
- `valuationVectorSection`, `valuationVector_surjective`: if every valuation is surjective, every finitely supported vector has a chosen preimage, so the map is onto.

## Points to watch

- Surjectivity of each local valuation is the hypothesis `hval`; it is not deduced from discreteness.
- The section is built by `Classical.choose` and is given only as a function: the file proves that it is a right inverse of `valuationVector`, not that it is a homomorphism.
- No archimedean or excluded indices: the restricted product is taken over the whole index set with respect to the integral units everywhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Algebra/RestrictedProduct/Valuation.lean`: the Lean file is the source byte for byte (SHA-256 `67b0dd6b9c55c2954895baa3b5f03538c9e04f6f41596586012d1c363710ffa8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
