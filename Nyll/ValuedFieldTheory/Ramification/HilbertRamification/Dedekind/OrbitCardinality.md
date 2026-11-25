# Orbits and cardinalities of decomposition and inertia groups

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a group `G` acting on a ring `B` over `A` and a prime `P` of `B` over `p`, the file proves the orbit facts behind the statement that `P` does not split over the decomposition and inertia fields, and the cardinality formulas `|G_P| = e·f`, `|I_P| = e`, `|G_P/I_P| = f` for the chosen prime `P`.

## Main results

- `dedekindTower_decompositionGroup_orbit_eq_singleton`, `dedekindRamification_inertiaGroup_orbit_eq_singleton`: the orbit of `P` under `G_P`, and under `I_P`, is `{P}`; the `_ncard_eq_one` versions count it.
- `dedekindRamification_inertiaGroup_decompositionGroup_eq_top`, `dedekindRamification_inertiaGroup_inertiaGroup_eq_top`: with `I_P` itself as the acting group, its decomposition and inertia groups at `P` are all of `I_P`.
- With `A`, `B` Dedekind, `B` finite and torsion-free over `A`, `p` maximal and nonzero, and `G` a finite Galois group of `B/A`:
  - `dedekindTower_decomposition_card_eq_ramificationIdx_mul_inertiaDeg`: `|G_P| = e(P|p)·f(P|p)`;
  - `dedekindTower_ramificationIdx_mul_inertiaDeg_eq_card_of_nonsplit` (and the `In` form): if `P` is the only prime over `p`, then `e·f = |G|`;
  - `inertia_card_eq_ramificationIdx` and `dedekindRamification_separable_residue_cardinalities`: if `B/P` is separable over `A/p`, then `|I_P| = e(P|p)` and `|G_P/I_P| = f(P|p)`.

The cardinality statements restate those of the Dedekind layer, which use the invariants `ramificationIdxIn`, `inertiaDegIn`, for the chosen prime `P` via Mathlib's equalities `ramificationIdxIn_eq_ramificationIdx` and `inertiaDegIn_eq_inertiaDeg`.

The formulas for `|I_P|` and `|G_P/I_P|` assume a separable residue extension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/OrbitCardinality.lean`: the Lean file is the source byte for byte (SHA-256 `7856bf481448981436a7e3a18fed135b8cd7ce34d330cc2057a6ba47fa814f19`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
