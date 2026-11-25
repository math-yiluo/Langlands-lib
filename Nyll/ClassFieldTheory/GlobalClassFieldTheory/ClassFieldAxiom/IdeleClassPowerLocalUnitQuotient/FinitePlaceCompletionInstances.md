# Instances on the completion of a number field at a finite place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K and a finite place v (a height-one prime of `𝓞 K`), the file registers three instances on the completion `v.adicCompletion K`, as used in the finite-place arithmetic of class field theory.

- `finitePlaceAdicCompletion_isCompleteDiscrete`: its valuation, with values in `ℤₘ₀`, is complete and discrete.
- `finitePlaceAdicCompletion_charZero`: the completion has characteristic zero, since K embeds into it.
- `finitePlaceAdicCompletion_residueFinite`: the residue field of the valuation ring is finite, by an imported lemma `finite_adicCompletion_residueField`.

## Points to watch

- `IsCompleteDiscrete` is the library's own class (in `ValuationTheory.DiscreteValuationField`), not a Mathlib notion; it bundles rank-one discreteness with adic completeness of the valuation ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/FinitePlaceCompletionInstances.lean`: the Lean file is the source byte for byte (SHA-256 `7de512d8c62a7f7fdf8f02fac99e75a6068273716fb6b479dfe95c1f2fb259a7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
