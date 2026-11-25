# The ring of integers of a mixed-characteristic local field as a ℤ_p-lattice

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.IntegralLattice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field `F` on a field `K` of characteristic zero, with residue characteristic `p`, the file uses the canonical copy of `ℚ_p` inside `K` (built in the library's classification of local fields) to show that the ring of integers `O_K` is the integral closure of `ℤ_p` in `K`, hence free of rank `d = [K : ℚ_p]`. It then sets up `ℤ_p`-module structures on the higher principal units `U^r`, used for the structure of `U^1`.

## Main definitions and results

- `MixedQPadicContext F`: a `Prop`-valued class holding primality of `p`; with it in scope, instances give `Algebra ℚ_p K` (the canonical `qpadicNumbersAlgebra`) and `FiniteDimensional ℚ_p K`. `MixedIntegralAlgebraContext`, `MixedIntegralLatticeContext` and `MixedMaximalIdealPowContext` likewise switch on the `ℤ_p`-algebra, finiteness and freeness instances below.
- `qpadicNumbersAlgebra_mem_valuationSubring_iff`: `x ∈ ℚ_p` lands in `O_K` exactly when `‖x‖ ≤ 1`. Consequently `qpadicDVRValuation_hasExtension`: the valuation of `K` extends the discrete valuation of `ℚ_p`.
- Over the valuation ring of the library's model `Examples.Qp.padicCompleteDVF p`: `O_K` is its integral closure in `K`, finite, free, of rank `[K : ℚ_p]`.
- `padicIntToValuationSubring : ℤ_p →+* O_K`, the algebra structures `padicIntValuationSubringAlgebra`, `padicIntFieldAlgebra` and their scalar tower.
- Over Mathlib's `ℤ_p`: `valuationSubring_isIntegralClosure_over_padicInt`, `mixed_valuationSubring_moduleFinite`, `mixed_valuationSubring_moduleFree`, `mixed_valuationSubring_finrank`; a basis `mixed_integralBasis` indexed by `Fin d`. Each power `m^n` of the maximal ideal is finite free of rank `d` (`mixed_maximalIdealPow_finrank`), with coordinates `mixed_maximalIdealPowLinearEquivPi`.
- `higherPrincipalUnitPadicModule`: the `ℤ_p`-module structure on `U^r` (`r ≥ 1`, written additively) restricted from the library's action on `U^1`; natural numbers act by powers. `higherPrincipalUnitPadicSubmodule` is `U^r` as a submodule of `U^1`.
- `principalUnitQuotientProjectionLinear`: the linear projection `U^1 → U^1/U^(n+1)`, with kernel `U^(n+1)` (`principalUnitQuotientProjectionLinear_ker`); the quotient is a torsion module and a `p`-group of order `p^(f·n)`, `f` the residue degree.

## Proofs

`ℤ_p` maps into `O_K` because `ℕ` is dense in `ℤ_p` and `O_K` is closed; the converse uses `m_(ℤ_p) = pℤ_p` and `v(p) < 1`. Integral closure and finiteness come from imported results for finite separable extensions of complete discretely valued fields; freeness follows from finiteness and torsion-freeness over the principal ideal domain `ℤ_p`.

## Points to watch

- The algebra structures are definitions activated through the `Prop`-valued context classes, which the statements install locally with `letI`; they are not unconditional global instances.
- `mixed_integralBasis` and the coordinates on `m^n` are chosen by `Module.finBasisOfFinrankEq`, not a specific integral basis.
- The `ℤ_p`-action on `U^1` and the quotient type `DiscretePrincipalUnitQuotient` are the library's own constructions, imported here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/MixedCharacteristicStructure/IntegralLattice.lean`: the Lean file is the source byte for byte (SHA-256 `93afa2f2f8c2bbd5b3b41729839729766e98f7f412d53ef746b31786846968c3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
