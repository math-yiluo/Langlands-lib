# Transport of lattice chains between integer rings with equal carriers

Internal helper module for the proof of BK93 (2.2.8) (`RefinementProof`). In the refinement
statement, the derived stratum `D` and the simple stratum `C` live over `E`, with lattice chains
over the integral closure `subfieldIntegers F E`. Applying the Library's T1 and T2 over `E`
requires a chain over `𝒪[E]` for a local-field structure on `E`. This module supplies the
change of integer ring. All filtration notions involved depend only on the underlying lattices.

## Carrier congruence

For two lattice chains `𝓛` (over `O`) and `𝓛'` (over `O'`) in the same `K`-space `V`, assume
their lattices agree as sets. Then they have:

- the same filtration `End^n` (`mem_endFiltration_congr`);
- the same adjoint and centralizer lattices (`mem_adjointLattice_congr`,
  `mem_centralizerLattice_congr`);
- the same critical index set and critical exponent (`criticalIndexSet_congr`,
  `criticalExponent_congr`);
- the same valuation (`valuation_congr`) and stabilizer (`mem_stabilizer_congr`).

`mem_adjointLattice_iff_mul` and `mem_centralizerLattice_iff_mul` unfold the two lattices in
terms of `βx - xβ`.

## Transfer along a ring isomorphism

Let `φ : O ≃+* O'` be compatible with the two algebra maps to `K`.

- `transferLattice` views each lattice as an `O'`-submodule.
- `transfer` assembles these into a `LatticeChain O' K V`. Finite generation and spanning are
  inherited. Periodicity is transported through `φ`, which maps Jacobson radicals to Jacobson
  radicals (`mem_jacobson_map`, `transferLattice_smul`).
- `transfer_lattice`: the transferred chain has the same lattices as sets.

In `RefinementProof` this is used with `φ = subfieldIntegerEquiv F E`, the Library's
identification of `subfieldIntegers F E` with `𝒪[E]` for the spectral valuation on `E`.
