/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Set

Ported from the `proetale` package (`Proetale.Mathlib.Order.BooleanAlgebra.Set`).
-/

@[expose] public section

lemma Set.codisjoint_iff {α : Type*} {s t : Set α} : Codisjoint s t ↔ s ∪ t = .univ := by
  simp [_root_.codisjoint_iff]
