/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Etale.Field

/-! # Algebraic separable extensions are unions of étale subalgebras

An algebraic separable field extension `L / K` is the filtered union of its finite separable
subextensions, which are finite étale, hence smooth, `K`-algebras
(`Algebra.exists_smooth_subalgebra_of_isSeparable`, blueprint
`corollary-open-direct-image-over-field--2`). The general separable case is
`FieldTheory.separable_extension_is_filtered_colimit_smooth`.
-/

@[expose] public section

namespace Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Blueprint `corollary-open-direct-image-over-field--2`: an algebraic separable extension `L / K`
is the filtered union of its finite separable subextensions, which are finite étale, hence
smooth, `K`-algebras: every finite subset of `L` lies in a finite type smooth (indeed étale)
`K`-subalgebra of `L`.

Proof: for a finite `s ⊆ L`, the field `K(s)` is finite and separable over `K`, hence étale
over `K`. -/
theorem exists_smooth_subalgebra_of_isSeparable [Algebra.IsSeparable K L] (s : Finset L) :
    ∃ S : Subalgebra K L, Smooth K S ∧ FiniteType K S ∧ (s : Set L) ⊆ S := by
  let F := IntermediateField.adjoin K (s : Set L)
  have : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsSeparable.isSeparable K x).isIntegral
  have : Algebra.IsSeparable K F := .of_algHom K L F.val
  have : FormallyEtale K F := .of_isSeparable K F
  have : FinitePresentation K F := FinitePresentation.of_finiteType.mp inferInstance
  have : Etale K F := ⟨inferInstance, inferInstance⟩
  exact ⟨F.toSubalgebra, inferInstanceAs (Smooth K F), inferInstanceAs (FiniteType K F),
    IntermediateField.subset_adjoin K _⟩

end Algebra
