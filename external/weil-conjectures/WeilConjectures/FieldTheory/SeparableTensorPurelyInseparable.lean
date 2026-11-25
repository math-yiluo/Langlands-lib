/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Separable tensor purely inseparable field extensions

Source: literature/stacks-project/algebra.tex, Lemma Tag 07QH (blueprint:
lem-weil-pbc-separable-tensor-purely-inseparable-field)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/--
The tensor product of a separable algebraic field extension with a finite purely
inseparable extension is a field and is finite purely inseparable over the first
field, with the expected dimension.

Source: literature/stacks-project/algebra.tex, Lemma Tag 07QH, proof first
paragraph (blueprint: lem-weil-pbc-separable-tensor-purely-inseparable-field).
The common-overfield criterion and linear disjointness of separable and purely
inseparable images prove fieldness. A Frobenius-power argument proves pure
inseparability, and base change preserves finiteness and dimension.
-/
theorem separableTensor_purelyInseparable_isField
    (k : Type u) (k' : Type v) (L : Type w) [Field k] [Field k'] [Field L]
    [Algebra k k'] [Algebra k L] [Algebra.IsSeparable k k']
    [IsPurelyInseparable k L] [Module.Finite k L] :
    IsField (k' ⊗[k] L) ∧
      IsPurelyInseparable k' (k' ⊗[k] L) ∧
      Module.Finite k' (k' ⊗[k] L) ∧
      Module.finrank k' (k' ⊗[k] L) = Module.finrank k L := by
  classical
  have hfield : IsField (k' ⊗[k] L) := by
    apply IntermediateField.LinearDisjoint.isField_of_forall k k' L
    intro Ω _ _ f g
    have : Algebra.IsSeparable k f.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjective f f.injective)
    have : IsPurelyInseparable k g.fieldRange :=
      (AlgEquiv.ofInjective g g.injective).isPurelyInseparable
    exact f.fieldRange.linearDisjoint_of_isPurelyInseparable_of_isSeparable g.fieldRange
  let : Field (k' ⊗[k] L) := hfield.toField
  have hpure : IsPurelyInseparable k' (k' ⊗[k] L) := by
    obtain ⟨q, _⟩ := ExpChar.exists k
    have : ExpChar k' q := expChar_of_injective_algebraMap (algebraMap k k').injective q
    apply (isPurelyInseparable_iff_pow_mem k' q).2
    exact IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar q
  exact ⟨hfield, hpure, inferInstance, Module.finrank_baseChange⟩
