# Integral closures of discrete valuation rings in finite extensions

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.IntegralClosure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `O_K` be the valuation ring of a complete (or, in a second part, Henselian) discretely valued field `K`, and `L/K` a finite extension carrying a valuation of the same kind that extends the one of `K`. The file studies Mathlib's integral closure `A` of `O_K` in `L` and compares it with the valuation ring `O_L`. It reduces the question whether `A` is local to idempotent lifting in the fiber of `A` over the maximal ideal `m_K`, and proves the Henselian input in the complete case.

## Commutative algebra

- `primeSpectrum_subsingleton_of_isArtinianRing_of_idempotents_trivial`: an Artinian ring whose only idempotents are 0 and 1 has at most one prime.
- For `R` local and `S` an `R`-algebra, the map `S → m_R.Fiber S` is surjective with kernel `m_R S`; `residueField_tensor_includeRight_ker_eq_maximalIdeal_map` gives the same kernel for `S → κ(R) ⊗ S`.

## Complete base (`ValuedExtension`)

- `A ⊆ O_L` always, giving an injective ring map; if `O_L` is module-finite over `O_K` it is bijective (`integralClosureRingEquivTargetValuationSubringOfModuleFinite`, with an `O_K`-algebra version) and `O_L` is an integral closure of `O_K` in `L`. For `L/K` separable, `target_valuationSubring_isIntegralClosure_iff_moduleFinite` makes the two conditions equivalent.
- If `O_L` is integral (for instance module-finite, or an integral closure) over `O_K`, its maximal ideal is the only prime over `m_K`.
- `integralClosureIntegers base target` names `A`; it is integral, faithful, and, for separable `L/K`, module-finite, quasi-finite, Dedekind, with Artinian fiber over `m_K` and finitely many, at least one, primes over `m_K`.
- `integralClosure_base_maximal_map_henselianRing`: for separable `L/K`, `A` is Henselian along `m_K A`.
- Chain of criteria: Henselian along `m_K A` ⇒ idempotents of the fiber lift (they are 0 or 1 in the domain `A`) ⇒ the fiber has at most one prime (separable case) ⇒ one prime of `A` over `m_K` ⇒ `A` local ⇒ `A` a valuation ring (separable case, via Dedekind theory) ⇒ every `z : L` has `z ∈ A` or `z⁻¹ ∈ A`.
- `O_K` has fraction field `K` and is integrally closed and noetherian.

## Henselian base (`ValuedExtension.Henselian`)

The same chain is repeated for a `HenselianDVF` base, and `integralClosure_base_maximal_map_le_jacobson_bot` puts `m_K A` in the Jacobson radical of `A` for separable `L/K`.

## Caveats

- For a Henselian base the file does not prove that `A` is Henselian along `m_K A`, nor that `A` is local: the localness statements there take idempotent lifting, a subsingleton fiber or a single prime over `m_K` as hypothesis; a Henselian kernel yields only the lifting and fiber conditions.
- Module-finiteness, Dedekindness and the valuation-ring conclusion assume `L/K` separable.
- The map `A → O_L` needs the instance `IsScalarTower O_K O_L L`. The `target` argument of `integralClosureIntegers` is not used by its definition.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/IntegralClosure.lean`: the Lean file is the source byte for byte (SHA-256 `fc0919c60b9eb5b88267b2eafcf7e71115fedc3052d36ccf55cc4d645c9b62e4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
