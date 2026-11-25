/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Field extensions and towers

Source: blueprint `sec-picard-framework/sk-thm-picard-rr/def-pc-field-tower.md`
(blueprint: def-pc-field-tower); Stacks Project, Fields, Tags 09FV, 09GC, 09H1,
09HE, and 09GS.

## Main definitions

* `FieldExtension.degree` is the vector-space degree, with `⊤` for an infinite
  dimensional extension.
The other clauses in the blueprint are recorded by Mathlib's existing notions:
`Module.Finite k K`, `Algebra.IsAlgebraic k K`,
`Module.Finite k K ∧ Algebra.IsSeparable k K`,
`IsPurelyInseparable k K`, and `IsAlgClosure k K`, respectively.
-/

@[expose] public section

universe u v

namespace FieldExtension

/-- (blueprint: def-pc-field-tower) The degree `[K : k]`, equal to `∞` when `K` is not
finite-dimensional over `k`.

This is `Module.finrank k K` in the finite-dimensional case and `⊤` otherwise.
(Stacks, Tag 09G3). -/
noncomputable def degree (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] :
    WithTop ℕ := by
  classical
  exact if Module.Finite k K then (Module.finrank k K : WithTop ℕ) else ⊤

end FieldExtension
