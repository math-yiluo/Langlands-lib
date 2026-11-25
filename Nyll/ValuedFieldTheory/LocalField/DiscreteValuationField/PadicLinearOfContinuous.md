# Continuous additive maps of ℤ_p-modules are ℤ_p-linear

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicLinearOfContinuous`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For topological ℤ_p-modules, continuity upgrades an additive map to a ℤ_p-linear one. The file proves this and collects small tools for the structure theory of the unit group of a local field.

- `map_padicInt_smul_of_continuous`: let `A`, `B` be topological ℤ_p-modules with continuous scalar multiplication, `B` Hausdorff. A continuous additive map `f : A →+ B` satisfies `f (a • x) = a • f x` for every `a` in ℤ_p. The set of such `a` is closed and contains the natural numbers, which are dense in ℤ_p.
- `padicLinearEquivOfContinuousAddEquiv`: an additive equivalence with continuous forward map, repackaged as a ℤ_p-linear equivalence.
- `continuous_padicInt_finPi_linearMap`: every ℤ_p-linear map from `Fin d → ℤ_p` to a module with continuous addition and scalar multiplication is continuous.
- `moduleFinite_of_surjective_of_ker`: if `f : M →ₗ[R] N` is surjective and `N` and `ker f` are finitely generated, so is `M`.
- `continuousAddEquivOfMultiplicativeSource` and `continuousMulEquivOfAdditiveTarget` convert between topological additive and multiplicative equivalences through `Additive` and `Multiplicative`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PadicLinearOfContinuous.lean`: the Lean file is the source byte for byte (SHA-256 `cd572fb79b7c28505817b16bc28725fc564dac3d260797e1bb47fb372cb91f05`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
