/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Finite extensions of separably closed fields

A finite extension of a separably closed field is purely inseparable and separably closed.
-/

@[expose] public section

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsSepClosed K]

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`: a finite extension
`L / K` of a separably closed field `K` is purely inseparable.

Proof: the maximal separable subextension is a finite separable extension of `K`, hence
trivial; Mathlib proves this for any algebraic extension. -/
theorem IsSepClosed.isPurelyInseparable_of_finite [FiniteDimensional K L] :
    IsPurelyInseparable K L :=
  Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`: a finite extension `L` of a
separably closed field `K` is separably closed.

Proof: an algebraic closure of `L` is purely inseparable over `K`, hence over `L`; Mathlib
proves this for any algebraic extension. -/
theorem IsSepClosed.of_finite [FiniteDimensional K L] : IsSepClosed L :=
  Algebra.IsAlgebraic.isSepClosed (F := K)
