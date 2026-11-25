# Correction sums for multiplicativity of reciprocity

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.CorrectionSum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Bookkeeping for the proof that the abstract reciprocity map is multiplicative: an identity among action differences is rewritten as a sum of three terms `τᵢ xᵢ − xᵢ`, the shape required by the universal norm-descent lemma.

- `frobeniusMultiplicativityCorrectionTerm` and `frobeniusMultiplicativityCorrectionAction`: the triples `(p₄ − p₃, p₁ − p₃, p₃ − τ₁ p₃)` and `(τ₄, τ₁, τ₄)`.
- `frobeniusMultiplicativity_actionDifference_eq_correctionSum`: in any `Rep ℤ R`, `(τ₄ p₄ − p₄) + (τ₁ p₁ − p₁) + (p₃ − τ₄τ₁ p₃) = Σᵢ (τᵢ xᵢ − xᵢ)` for these triples.
- `DegreeData.frobeniusMultiplicativityCorrectionAction_mem_degreeKernel`: for a finite residue abstract field `K`, a closed `L ≤ K` with `G_L` normal in `G_K`, and Frobenius elements `φ` (of exponent one), `σ₁`, `σ₂` of `G_K / I_L`, with `σ₄ = frobeniusActionConjugate φ σ₂ d(σ₁)` and `τ₁`, `τ₄` the remainders `frobeniusActionRemainder` of `σ₁`, `σ₄` relative to `φ` (earlier files), all three acting elements have normalized degree zero.

The product is `τ₄τ₁` in this order; `R` need not be commutative.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/CorrectionSum.lean`: the Lean file is the source byte for byte (SHA-256 `bec82bb15d5994102252e46b00c2c57cb143c6d4c250ed836c5e2ab16536fd4a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
