# A positive archimedean section of the idele norm

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, this file builds a continuous homomorphism from the positive real units ℝ≥0ˣ into the idele group of K. Its values are supported at one infinite place, and composing it with the absolute idele norm gives r ↦ r⁻¹. As an application, every idele is written as a norm-one idele times a positive archimedean idele.

## Main definitions and results

- `positiveArchimedeanLocalComponent v`: sends r > 0 to r, seen as a unit of K_v through K_v ≅ ℝ at a real place or K_v ≅ ℂ at a complex place. `positiveArchimedeanLocalComponentContinuous` is the same map as a continuous homomorphism.
- `positiveArchimedeanRoot`: r ↦ r^(1/m), where m is the multiplicity (1 or 2) of the infinite place w₀ that Mathlib's Dirichlet unit theorem singles out.
- `positiveArchimedeanSection K`: the idele whose component at w₀ is r^(1/m) and whose other components are all 1. `positiveArchimedeanSectionContinuous` and `continuous_positiveArchimedeanSection` record its continuity.
- `positiveArchimedeanSection_finiteComponent`: every finite component is 1.
- `positiveArchimedeanSection_infiniteComponent_mem_positive`: every infinite component lies in `RayClass.infinitePositiveSubgroup`.
- `positiveArchimedeanSection_absoluteNorm`: the absolute norm of `positiveArchimedeanSection K r` is r⁻¹.
- `positiveArchimedeanNormOneCorrection K a`: the norm-one idele a · s(N(a)), where s is the section and N the absolute norm. By `eq_positiveArchimedeanNormOneCorrection_mul_section_inv`, a equals this correction times s(N(a))⁻¹.

## Points to watch

- The section gives absolute norm r⁻¹, not r. The library's `IdeleGroup.absoluteNorm` divides by the archimedean norm, so it is the reciprocal of the usual ∏_v |a_v|_v. Composed with the section, the usual norm would be the identity.
- The construction depends on the place w₀ chosen in Mathlib's `NumberField.Units.dirichletUnitTheorem`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/PositiveArchimedeanSection.lean`: the Lean file is the source byte for byte (SHA-256 `b9fcedb70000da607478ea4160f4325de3bcffcf390e37d62b594b87326da052`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
