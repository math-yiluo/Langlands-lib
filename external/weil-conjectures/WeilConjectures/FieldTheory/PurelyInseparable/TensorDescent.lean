/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Descending finite purely inseparable extensions along a field extension

Let `L / K` be a field extension and `B` a commutative `K`-algebra such that `L ⊗[K] B` is a
field, finite and purely inseparable over `L`. Then `B` is a field, finite and purely
inseparable over `K`, of the same degree.

## Main results

- `Algebra.TensorProduct.isField_finite_isPurelyInseparable_of_tensorProduct`
-/

@[expose] public section

open TensorProduct Module

/-- **A finite purely inseparable extension descends along a field extension.** Let `L / K` be
a field extension and `B` a commutative `K`-algebra. If `L ⊗[K] B` is a field which, as an
`L`-algebra via `l ↦ l ⊗ 1`, is finite and purely inseparable over `L`, then `B` is a field,
finite and purely inseparable over `K`, and `dim_K B = dim_L (L ⊗[K] B)`.

(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem Algebra.TensorProduct.isField_finite_isPurelyInseparable_of_tensorProduct
    {K L B : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (hfield : IsField (L ⊗[K] B)) [Module.Finite L (L ⊗[K] B)]
    [IsPurelyInseparable L (L ⊗[K] B)] :
    IsField B ∧ Module.Finite K B ∧ IsPurelyInseparable K B ∧
      finrank K B = finrank L (L ⊗[K] B) := by
  let := hfield.toField
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  have : IsDomain B := hinj.isDomain _
  have hfin : Module.Finite K B := by
    have h1 := Module.rank_baseChange (R := L) (S := K) (M' := B)
    have h2 : Module.rank L (L ⊗[K] B) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [h1, Cardinal.lift_lt_aleph0] at h2
    exact Module.rank_lt_aleph0_iff.mp h2
  refine ⟨(Algebra.IsIntegral.isField_iff_isField (algebraMap K B).injective).mp
    (Field.toIsField K), hfin, ?_, Module.finrank_baseChange.symm⟩
  -- a `K`-linear retraction `φ : L → K` of `K → L` gives `ψ : L ⊗[K] B → B`, `l ⊗ b ↦ φ l • b`
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hφ1 : ∀ k : K, φ (algebraMap K L k) = k := fun k => LinearMap.congr_fun hφ k
  let ψ : L ⊗[K] B →ₗ[K] B := (TensorProduct.lid K B).toLinearMap ∘ₗ _root_.TensorProduct.map φ .id
  have hψ : ∀ l b, ψ (l ⊗ₜ b) = φ l • b := fun l b => by simp [ψ]
  set q := ringExpChar K
  have : ExpChar L q := expChar_of_injective_algebraMap (algebraMap K L).injective q
  rw [isPurelyInseparable_iff_pow_mem K q]
  intro b
  obtain ⟨n, l, hl⟩ := IsPurelyInseparable.pow_mem L q
    (Algebra.TensorProduct.includeRight (R := K) (A := L) b)
  refine ⟨n, φ l, ?_⟩
  have := congrArg ψ hl
  rw [← map_pow, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hψ, hψ,
    show (1 : L) = algebraMap K L 1 from (map_one _).symm, hφ1, one_smul] at this
  rw [← this, Algebra.algebraMap_eq_smul_one]
