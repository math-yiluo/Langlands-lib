/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure

/-!
# The separable closure of a field in a separably closed extension

The relative separable closure `separableClosure F E` of `F` in `E` consists of the elements of
`E` which are separable over `F`; when `E` is separably closed it is a separable closure of `F`.
-/

@[expose] public section

namespace IsSepClosed

/-- **Separable algebraic closure inside an extension.** The separable closure
`separableClosure F E` of `F` in an extension `E` consists of the elements of `E` separable over
`F`; if `E` is separably closed, then it is a separable closure of `F`.

(blueprint: `def-weil-pbc-relative-separable-closure`) -/
theorem isSepClosure_separableClosure (F E : Type*) [Field F] [Field E] [Algebra F E]
    [IsSepClosed E] : IsSepClosure F (separableClosure F E) ∧
      ∀ x : E, x ∈ separableClosure F E ↔ IsSeparable F x :=
  ⟨separableClosure.isSepClosure F E, fun _ ↦ mem_separableClosure_iff⟩

end IsSepClosed
