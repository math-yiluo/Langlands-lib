# Herbrand quotients in short exact sequences, across universes

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.UniverseFiniteness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite cyclic group G with generator σ and a short exact sequence `1 → A → B → C → 1` of commutative groups with G-actions and equivariant maps, the file states the two-out-of-three property for the definedness of Herbrand quotients, the cardinality identity of the hexagon of Tate groups, and multiplicativity of the Herbrand quotient. Its point is that G, A, B and C may live in four different universes: the library's versions of these results, which need fewer universes, are applied after lifting with `ULift`.

## Main results

All are in the namespace `CyclicCohomology.ProfiniteCohomology.Herbrand.Universe`. The hypotheses are: `i : A →* B` injective, `j : B →* C` surjective, both equivariant, exactness `j b = 1 ↔ ∃ a, i a = b`, and `hgen : ∀ g, g ∈ Subgroup.zpowers σ`.

- `herbrandQuotientDefined_anyTwo`: if two of the three Herbrand quotients are defined (both Tate groups finite), so is the third. `herbrandQuotientDefined_right_of_left_middle`, `herbrandQuotientDefined_middle_of_left_right` and `herbrandQuotientDefined_left_of_middle_right` are the three cases.
- `herbrand_exact_cardinality_identity`: when all six Tate groups are finite, `|Ĥ⁰(B)|·|Ĥ⁻¹(A)|·|Ĥ⁻¹(C)| = |Ĥ⁰(A)|·|Ĥ⁰(C)|·|Ĥ⁻¹(B)|`.
- `herbrandQuotient_multiplicative_of_shortExact`: under the same finiteness, `h(B) = h(A)·h(C)`.

## Proof

Private helpers lift homomorphisms to `ULift` into the common universe `max v w x` and check that injectivity, surjectivity, exactness and equivariance survive. The library's theorems of the same names in `CyclicCohomology.ProfiniteCohomology.Herbrand` apply there, and equivariant isomorphisms `ULift A ≃* A` carry the Tate groups and their cardinalities back. Multiplicativity is then rearranged from the cardinality identity in ℚ.

## Watch for

- The names repeat those of the underlying library theorems; the versions here are distinguished only by the namespace `…Herbrand.Universe`.
- Groups are written multiplicatively, and the Herbrand quotient is the library's `herbrandQuotient σ`, the ratio of the orders of the degree 0 and degree −1 Tate groups.
- Cyclicity is the explicit hypothesis `hgen` with a chosen generator σ.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/UniverseFiniteness.lean`: the Lean file is the source byte for byte (SHA-256 `c5053d9d8825c34c24a6b4f471e23ebf7fa368f19dc0715df1cc5b182170fae9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
