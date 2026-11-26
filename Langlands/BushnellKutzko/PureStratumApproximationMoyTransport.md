# Moy's reduction in the centralizer of a field

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`. The proof of (2.4.5), printed p. 68 (PDF p. 80), applies (2.3.1), printed p. 57, in `B = End_E(V)` to the hereditary `𝔬_E`-order of a chain normalized by `E`, with the new order compatible with the old one in the sense of (1.1.9). This module derives that application from `LatticeChain.exists_latticeChain_of_isNilpotent_sandwiched` (module `MoyReductionSandwich`).

## Results

- `period_eq_of_coe_lattice_eq`: two lattice chains with the same lattices, over discrete valuation rings with uniformizers having the same image in the field, have the same period. Both periods are read from `LatticeChain.lattice_add_period_uniformizer`.
- `exists_compatible_chain_of_isNilpotent`: let `𝓛` be an `𝔬_F`-chain normalized by `E` and let `z, y ∈ End_E(V)` with `z ∈ 𝔓^j(𝓛)`, `y` nilpotent and `y − z ∈ 𝔓^{j+1}(𝓛)`. Then there are a chain `𝓜` normalized by `E` and `j'` with the following properties:
  - every `E`-linear `w` with `w − z ∈ 𝔓^{j+1}(𝓛)` lies in `𝔓^{j'}(𝓜)`;
  - `j e(𝓜) < j' e(𝓛)`;
  - every lattice of `𝓜` lies between two consecutive lattices of `𝓛`.

## Proof

Give `E` its spectral local-field structure. Transport `𝓛.subfieldChain` along `subfieldIntegerEquiv` to a chain over `𝒪[E]`, and along the coordinate isomorphism `f : V ≃ (Fin d → E)` given by `Module.finBasis`. Conjugation by `f` (`LinearEquiv.conjAlgEquiv`) carries the filtration of `𝓛` on `E`-linear maps to the filtration of the transported chain and preserves nilpotence. Apply the sandwiched Moy reduction there. Transport the resulting chain back along `f⁻¹` and `subfieldIntegerEquiv⁻¹`, and lift it to `𝔬_F` with `liftChain`; it is normalized by `liftChain_normalized`. The coset inclusion and the sandwich property transport lattice by lattice.

For the inequality, all transports preserve periods: `period_eq_of_coe_lattice_eq` for the change of integer ring, `LatticeChain.period_unique` with `Submodule.map_smul''` for `f`. Over `𝔬_F` the periods are `e(E|F)` times the periods over `𝔬_E` (`liftChain_period`, and `LatticeChain.subfieldChain_period_eq_shift` with `fieldShift_uniformizer_mul_ramification` for `𝓛`). The inequality over `E` multiplies by `e(E|F) > 0`.
