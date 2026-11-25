# Elements of finite order preserve the valuation

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteOrderValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `A` be a valuation subring of `L`, `L/K` a field extension, and `D` the decomposition group of `A` (the `K`-automorphisms stabilizing `A`). The file shows that an element of finite order in `D` preserves the valuation of `A` exactly, not only its valuation ring, so that finite inertia lies in the value-trivial subgroup on which the inertia character is defined.

- `valuation_decomposition_apply_eq_of_isOfFinOrder`: if `σ ∈ D` has finite order, then `v_A(σx) = v_A(x)` for all `x ∈ L`.
- `mem_valueTrivialInertiaGroup_of_isOfFinOrder`: an inertia element of finite order lies in `valueTrivialInertiaGroup` (`σx/x` is a unit of `A` for every `x ≠ 0`).
- `valueTrivialInertiaGroup_eq_top_of_finite`: if the inertia group is finite, it equals its value-trivial subgroup; no finiteness of the whole automorphism group is needed.

The proof uses that `σ` induces a monotone map on the value group of `A`; a monotone map some positive iterate of which is the identity is itself the identity.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FiniteOrderValuation.lean`: the Lean file is the source byte for byte (SHA-256 `fc5539481541f5fdcda2e21f2baa14f3f9c0bdede210e48a674e5bf15f685614`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
