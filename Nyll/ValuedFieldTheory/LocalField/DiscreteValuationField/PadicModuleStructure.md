# Compact finitely generated ℤ_p-modules with cyclic torsion

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicModuleStructure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file gives the module-theoretic step of the mixed-characteristic structure theorem for the unit group of a local field: a compact, finitely generated ℤ_p-module whose torsion is finite cyclic is topologically a cyclic group times a free module.

`chosenPadicModuleContinuousAddEquivZModProdFinPi` constructs a topological additive isomorphism `ZMod (p^a) × (Fin d → ℤ_p) ≃ₜ+ M`. Hypotheses on `M`: a compact Hausdorff, finitely generated ℤ_p-module with continuous addition and scalar multiplication, whose torsion submodule is finite and cyclic of order `p^a`, and whose quotient by torsion has rank `d`.

The quotient by torsion is free, so a lift of the quotient map splits `M` as torsion times free part. Continuity holds on the finite factor, which is discrete, and on the free factor by `continuous_padicInt_finPi_linearMap`; a continuous bijection from a compact to a Hausdorff space is a homeomorphism.

Watch for: the isomorphism depends on a choice of lift and basis, and it is stated only as additive, not as ℤ_p-linear. Finiteness and cyclicity of the torsion are hypotheses, not conclusions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PadicModuleStructure.lean`: the Lean file is the source byte for byte (SHA-256 `a61322f3f3e4a1b7c91822a4420f4f124d7cfd1de26cca12c0c8b234cefb7118`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
