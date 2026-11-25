# Continuity of reduction ℤ_p → ℤ/p^n

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.PadicReductionContinuous`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Two facts about the reduction map `PadicInt.toZModPow n : ℤ_[p] → ZMod (p ^ n)` for a prime p, used to show that p-adic scalar actions on finite discrete groups are continuous.

- `isOpen_ker_padicIntToZModPow`: the kernel of reduction modulo p^n is open in ℤ_p. It is the ideal p^n ℤ_p, which equals the closed ball of radius p^(−n) about 0, and closed balls of nonzero radius are open in an ultrametric space.
- `Internal.continuous_padicIntToZModPow`: reduction modulo p^n is continuous when ℤ/p^n carries the discrete topology. A ring homomorphism is continuous once it is continuous at 0, and the open kernel is a neighbourhood of 0.

The discrete topology on `ZMod (p ^ n)` is passed explicitly in the statement, not taken from an instance. The file depends only on Mathlib, although it sits in the namespace of the principal-unit files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnitPadicAction/PadicReductionContinuous.lean`: the Lean file is the source byte for byte (SHA-256 `7d719c321464edb3e7f7379aa16ae9bca8711364a05cddac10bf1a92c5bfab0a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
