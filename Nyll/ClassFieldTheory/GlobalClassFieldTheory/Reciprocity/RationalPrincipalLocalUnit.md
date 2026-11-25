# The local unit of a rational principal idele at p

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrincipalLocalUnit`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

For `x : ℚˣ` and a prime `p`, the rational number `rationalPrimeUnit x p = p ^ (−v_p(x)) · x` is a `p`-adic unit. This file identifies that unit in the three places where global reciprocity over `ℚ` meets it: the height-one valuation at `p`, the field `ℚ_[p]`, and the valuation subring of the local field `ℚ_[p]` used by the multiplicative Lubin–Tate construction. It also identifies the uniformizer of that construction with `p` itself, and transports the finite component at `p` of a principal idele to `ℚ_[p]`.

## Main definitions and results

- `rationalPrimeUnit_heightOneValuation_eq_one`: the valuation of `ℚ` at the height-one prime corresponding to `p` takes the value one on `rationalPrimeUnit x p`.
- `rationalPrimeUnitValuationSubringUnit x p`: that unit as a unit of the valuation subring of `padicLocalField p`, obtained from `ℤ_[p]ˣ`; its coercion to `ℚ_[p]` is the image of the rational number.
- `standardLubinTateBaseUniformizerUnit_eq_rationalPrimeGenerator`: the base uniformizer of the standard multiplicative Lubin–Tate series over `ℚ_[p]` is the image of `p`.
- `rationalPadicFieldUnit_eq_unitFactor_mul_baseUniformizer_zpow`: in `ℚ_[p]ˣ`, `x` is the Lubin–Tate unit factor of `rationalPrimeUnitValuationSubringUnit x p` times the uniformizer to the power `v_p(x)`.
- `rationalPadicFieldUnit_uniformizerValueExponent` and `rationalPadicFieldUnit_uniformizerUnitPart`: the exponent and the unit part chosen by the library's complete-DVF uniformizer decomposition of `x` are `v_p(x)` and `rationalPrimeUnitValuationSubringUnit x p`.
- `padicCompletionEquiv_principalFiniteComponent`: under the canonical equivalence between `ℚ_[p]` and the adic completion of `ℚ` at `p`, the finite component at `p` of the principal idele of `x` is the image of `x` in `ℚ_[p]ˣ`. The variants `…_factorization`, `…_uniformizerUnitPart`, `…_rationalPrimeGenerator` and `…_eq_lubinTateUnitFactor` combine this with the results above.
- `rationalPrimeUnit_mul_primeGenerator_zpow`: `rationalPrimeUnit x p · p ^ v_p(x) = x` in `ℚˣ`.

## Proofs

The valuation statement uses Mathlib's comparison of the height-one valuations of `ℚ` with the `p`-adic valuation, together with the fact that `rationalPrimeUnit x p` has `p`-adic valuation zero. The exponent statement computes the library's multiplicative integer valuation on the factorization `x = u · ϖ ^ v_p(x)`, using that `u` lies in the unit group; the unit-part statement then follows by injectivity of the map from valuation-subring units to field units. The component statements reduce to `finiteComponent_principalIdele` and the fact that the completion equivalence commutes with the embedding of `ℚ`.

## Remarks

- `padicLocalField`, `standardLubinTateUnitFactorFieldUnit`, `uniformizerValueExponent` and `fieldUnitUniformizerUnitPart` are the library's own constructions, not Mathlib's.
- The sign of `x` is not separated here: it stays inside the unit part.

## Changed declarations

The source declares the anonymous local instance `local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalPrincipalLocalUnit.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `cf286e406cd40cbc9aece35db8d32ab6a791c1d1e1be1c3ae01c16186cd4e50f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
