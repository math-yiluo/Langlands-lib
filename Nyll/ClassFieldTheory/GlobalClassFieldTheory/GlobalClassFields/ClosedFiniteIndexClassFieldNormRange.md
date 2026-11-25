# The norm group of the class field over its base copy

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldNormRange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed finite-index subgroup of the idele class group `C_K` of a number field `K`. The class field `closedFiniteIndexClassField H hclosed` is built over a fixed-field copy `K₀ = closedFiniteIndexClassFieldBase H hclosed` of `K`, with an isomorphism `e : K ≃ₐ[ℚ] K₀`. This file computes its norm group over `K₀`.

## Main results

- `closedFiniteIndexClassField_ideleClassNorm_range_over_base`: the range of the idele class norm from the class field to the idele class group of `K₀` is the image of `H` under the transport `ideleClassCongr e`, an isomorphism from `C_K` to the idele class group of `K₀`.
- `ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension`: the norm subgroup that the abstract class-formation correspondence attaches to the selected subextension is the same transported subgroup, in additive form.

Both are deduced from imported results on the ordinary norm class field. The rest of the file consists of private wrappers that move between a subgroup and its additive presentation.

The statement is over the copy `K₀`; the norm group over `K` itself is treated in another file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldNormRange.lean`: the Lean file is the source byte for byte (SHA-256 `f2193447094f7cb9fed6078a083d3123dd6281800340fe56aa5460433d05444f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
