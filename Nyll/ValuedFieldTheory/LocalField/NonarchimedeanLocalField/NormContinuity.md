# Continuity of the field norm

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension of normed fields the field norm is continuous. The file proves this, also for the norm on unit groups; its comment calls it the analytic input for topological finite local reciprocity.

- `algebraNorm_continuous_of_finiteDimensional`: if `K` is a complete nontrivially normed field and `L` a normed field that is a finite-dimensional `K`-algebra with continuous scalar multiplication, then `Algebra.norm K : L → K` is continuous.
- `normUnits_continuous_of_finiteDimensional`: under the same hypotheses, `normUnits K L : Lˣ → Kˣ` is continuous.
- `integerUnitsToFieldUnits_continuous`: the inclusion `𝒪[K]ˣ → Kˣ` is continuous, for any field with a valuative relation and a topology.

The norm of `x` is the determinant of the matrix of multiplication by `x` in a basis, and that matrix depends continuously on `x` because linear maps on a finite-dimensional space over a complete field are continuous.

The first two theorems concern normed fields, not the `ValuativeRel` setting of the neighbouring files; using them for local fields requires supplying norms.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean`: the Lean file is the source byte for byte (SHA-256 `abc4983f5ad7b0832a0076c2d21b51ec8aa6307e6bd9ca5abdfd365304cededb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
