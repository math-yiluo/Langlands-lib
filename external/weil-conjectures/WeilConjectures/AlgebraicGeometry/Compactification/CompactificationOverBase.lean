/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.Compactification.Dense

/-!
# Compactifications over a quasi-compact quasi-separated base

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-def-sfb-dc-setting/lem-sfb-compactification-over-base.md`, node order 1775
(blueprint: remark-compactifications--1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every morphism between schemes over a quasi-compact, quasi-separated base,
with separated finite-type source and separated quasi-compact target over that base,
has a compactification with quasi-compact open immersion.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-def-sfb-dc-setting/lem-sfb-compactification-over-base.md`, node order 1775
(blueprint: remark-compactifications--1).

Proof, following the source proof:
1. Write the structure morphisms `X ↘ S` and `Y ↘ S`; `f.IsOver S` identifies
their composite with `f` (`def-weil-scheme-over-base`). Finite type means locally
of finite type and quasi-compact (`def-weil-finite-type-morphism`). Separatedness
of `Y ↘ S` implies quasi-separatedness (`lem-pc-separated-quasi-separated`).
Clause (2) of `lem-weil-pbc-qcqs-morphism-permanence` gives quasi-compactness of
both `X` and `Y` from quasi-compactness of their structure maps and of `S`, and
quasi-separatedness of `Y` from that of its structure map and of `S`.
2. Clause (b) of `lem-weil-pbc-separated-cancellation` gives separatedness of
`f` from that of `X ↘ S`. Clause (f) of `lem-weil-pbc-proper-fp-permanence`
gives local finite type of `f` from that of `X ↘ S`. Clause (1) of
`lem-weil-pbc-qcqs-morphism-permanence` gives quasi-compactness of `f` because
`X` is quasi-compact and `Y` is quasi-separated. Thus `f` is of finite type.
3. Apply `theorem-nagata-s-compactification-theorem--1` to `f` over the qcqs base `Y` to get
a dense compactification. Its open immersion is quasi-compact, its structure
map is proper, and their composite is `f` (`definition-compactification-refinement`). Forget
density to obtain an object of `BoundaryCompactification f`.
The argument uses the statement dependencies `definition-compactification-refinement`,
`def-weil-scheme-over-base`, `def-weil-finite-type-morphism`,
`def-weil-proper-morphism`, `def-weil-quasi-separated-morphism`, and
`def-weil-pbc-quasi-compact-scheme`, and the proof dependencies
`lem-pc-separated-quasi-separated`, `lem-weil-pbc-qcqs-morphism-permanence`,
`lem-weil-pbc-separated-cancellation`, `lem-weil-pbc-proper-fp-permanence`, and
`theorem-nagata-s-compactification-theorem--1`.
-/
theorem compactification_over_base {S X Y : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S]
    [IsSeparated (X ↘ S)] [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [IsSeparated (Y ↘ S)] [QuasiCompact (Y ↘ S)] :
    Nonempty (Compactification.BoundaryCompactification f) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ S)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ S)
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ S)
  have : IsSeparated (f ≫ (Y ↘ S)) := by
    rw [comp_over f S]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (Y ↘ S)
  have : LocallyOfFiniteType (f ≫ (Y ↘ S)) := by
    rw [comp_over f S]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ S)
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  obtain ⟨c, _⟩ := exists_isDense_compactification f
  exact ⟨⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩⟩

end AlgebraicGeometry
