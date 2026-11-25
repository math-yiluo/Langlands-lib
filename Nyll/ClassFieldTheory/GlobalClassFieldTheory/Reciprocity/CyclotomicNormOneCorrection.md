# Norm-one correction for the normalized cyclotomic value

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicNormOneCorrection`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, the file shows that multiplying an idele by a suitable positive archimedean idele makes its absolute norm 1 without changing its normalized cyclotomic value.

`exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue`: for every idele a of K there is a norm-one idele b with `normalizedCyclotomicZHatIdeleValue K b = normalizedCyclotomicZHatIdeleValue K a`.

Proof: let d = [K : ℚ] and r the absolute norm of a, and let s be the positive real d-th root of r. Push the rational positive archimedean idele attached to s (`rationalPositiveArchimedeanIdele s`) into the ideles of K; this idele c has absolute norm r⁻¹. The rational Artin map is trivial on positive archimedean ideles, so c has normalized value 0, by the base-inclusion formula `normalizedCyclotomicZHatIdeleValue_baseIdeleInclusion`. Take b = a · c.

The number field is taken in universe 0: the binder is `K : Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicNormOneCorrection.lean`: the Lean file is the source byte for byte (SHA-256 `2f8cf4f425798013063ffea1fb75082d163de73ac15dd8799ca9905fa59eb168`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
