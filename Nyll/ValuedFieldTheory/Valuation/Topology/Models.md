# Topology on Mathlib's `WithTopology` copies

Module `Nyll.ValuedFieldTheory.Valuation.Topology.Models`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Mathlib's `WithTopology α t` is a copy of a type `α` carrying the topology `t`. This file adds two facts about it.

- `WithTopology.homeomorph`: the canonical homeomorphism from `WithTopology α t` to `α` with the topology `t`.
- `WithTopology.tendsto_nhds_iff`: a function into `WithTopology X t` converges to `x` along a filter exactly when the underlying points converge to the underlying point of `x` for the topology `t`; it follows from the homeomorphism being an embedding.

No algebraic structure is put on `WithTopology` here; according to the file, such structure is installed only on particular copies, elsewhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Topology/Models.lean`: the Lean file is the source byte for byte (SHA-256 `d53e2a465651223723e5e1c2a62f0bb12bbb7db7e14148638cb58dd49ec3ca9b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
