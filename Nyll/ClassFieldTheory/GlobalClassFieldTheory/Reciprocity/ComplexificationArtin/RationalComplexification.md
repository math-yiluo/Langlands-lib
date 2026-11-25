# Artin reciprocity for ℚ(i)/ℚ on principal ideles

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RationalComplexification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file treats the quadratic extension ℚ(i)/ℚ, realized as the cyclotomic field of fourth roots of unity, and proves that the global Artin map of this extension kills every principal idele of ℚ.

## Main definitions and results

- `rationalComplexificationCyclotomicField`: the level-4 subfield of the library's rational cyclotomic closure `KummerTheory.rationalCyclotomicField` (level `2 ^ 2`, with `rationalComplexificationPrime = 2`). Instances say it is a cyclotomic extension for `{4}` and a CM field; finiteness, being a number field and being abelian Galois are local instances.
- `complexFourthRootField`: the subfield of ℂ generated over ℚ by all z with z⁴ = 1; `complexI_isPrimitiveRoot_four` supplies `I` as a primitive fourth root. `rationalComplexificationComplexEquiv` identifies the two fields as ℚ-algebras, and `complexFourthRootField_map_complexConjugation` shows the concrete field is stable under complex conjugation.
- `rationalComplexification_galoisGroup_card`: the Galois group has order 2. `rationalComplexification_chosenInfinitePlace_isRamified`: the chosen infinite place above the real place of ℚ is ramified (complex over real).
- `rationalComplexificationPrincipalInfiniteArtin_eq_one_of_num_pos` and `..._ne_one_of_num_neg`: the infinite Artin factor of the principal idele of x ∈ ℚˣ is trivial when x > 0 and nontrivial when x < 0.
- `rationalComplexificationGlobalArtin_principalIdele` (simp): `globalArtinMonoidHom` for this extension sends the principal idele of every x ∈ ℚˣ to 1.

## Proof

Through the cyclotomic character Gal → (ℤ/4)ˣ, the product of the finite local Artin factors of x equals the reduction mod 4 of the sign of x, by the earlier rational cyclotomic product formula `rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign`. For x > 0 both factors are trivial. For x < 0 the infinite factor is nontrivial, since its kernel is the norm subgroup and norms from ℂ to ℝ are positive, and the finite factor is nontrivial; in a group of order 2 both are the unique nontrivial element, which is its own inverse, so the product is 1.

## Watch for

- The Artin maps are the library's own, built from local factors at chosen places above each place of ℚ (`chosenFinitePlaceArtinMonoidHom`, `chosenInfinitePlaceArtinMonoidHom`).
- The result concerns only this one extension and only principal ideles of ℚ.
- The field is a level of the library's cyclotomic closure, not Mathlib's `CyclotomicField`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ComplexificationArtin/RationalComplexification.lean`: the Lean file is the source byte for byte (SHA-256 `56cef5b876d3d67f10b43fd7c80f83d18049b54dab8569a0e52018bede2162e4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
