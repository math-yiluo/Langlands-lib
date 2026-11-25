/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.Field.IsField
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.Basic

/-!
# Descent of finite purely inseparable field extensions

Source: Stacks Project, Tag 07QG, the finite purely inseparable extension asserted in its proof;
Tag 09HE for purely inseparable extensions
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- A finite purely inseparable field extension descends along extension of scalars.
Source: Stacks Project, Tag 07QG (implicit in its proof), and Tag 09HE
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof:
1. Mathlib's `Module.finrank_baseChange` gives the finrank equality. The tensor
   product is nontrivial and finite dimensional, so its finrank is positive;
   the equality and `Module.finite_of_finrank_pos` give finiteness of `B`.
2. `includeRight_injective` embeds `B` into the tensor-product field. Therefore
   `B` is a domain, and `fieldOfFiniteDimensional K B` makes it a field.
3. Choose a `K`-linear functional `f : L →ₗ[K] K` with `f 1 = 1` using
   `Module.Projective.exists_dual_eq_one`. Tensoring `f` with the identity and
   applying `TensorProduct.lid` gives a map sending `l ⊗ b` to `f l • b`.
4. Choose the exponential characteristic `q` of `K`, also that of `L`.
   Pure inseparability gives `(1 ⊗ b)^(q^n) = l ⊗ 1`. Apply the linear map
   from step 3 to obtain `b^(q^n) = f l • 1`, in the image of `K`.
   `isPurelyInseparable_iff_pow_mem` proves the remaining conclusion. For
   characteristic zero, `q = 1`, so the same argument applies. -/
theorem finite_purelyInseparable_of_tensorProduct
    (K : Type u) (L : Type v) (B : Type w)
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (hfield : IsField (L ⊗[K] B))
    [Module.Finite L (L ⊗[K] B)] [IsPurelyInseparable L (L ⊗[K] B)] :
    IsField B ∧ Module.Finite K B ∧ IsPurelyInseparable K B ∧
      Module.finrank K B = Module.finrank L (L ⊗[K] B) := by
  classical
  let : IsDomain (L ⊗[K] B) := hfield.isDomain
  have hdim : Module.finrank K B = Module.finrank L (L ⊗[K] B) :=
    (Module.finrank_baseChange (R := L) (S := K) (M' := B)).symm
  let : Module.Finite K B := Module.finite_of_finrank_pos (by
    rw [hdim]
    exact Module.finrank_pos)
  have hi : Function.Injective (includeRight : B →ₐ[K] L ⊗[K] B) :=
    includeRight_injective (algebraMap K L).injective
  let : IsDomain B := hi.isDomain (includeRight : B →ₐ[K] L ⊗[K] B)
  have hB : IsField B := by
    let := fieldOfFiniteDimensional K B
    exact Field.toIsField B
  refine ⟨hB, inferInstance, ?_, hdim⟩
  obtain ⟨q, hq⟩ := ExpChar.exists K
  let := hq
  let : ExpChar L q := expChar_of_injective_algebraMap (algebraMap K L).injective q
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  let π : L ⊗[K] B →ₗ[K] B :=
    (_root_.TensorProduct.lid K B).toLinearMap.comp (f.rTensor B)
  have hπ (l : L) (b : B) : π (l ⊗ₜ[K] b) = f l • b := by
    simp [π]
  apply (isPurelyInseparable_iff_pow_mem K q).2
  intro b
  obtain ⟨n, l, hl⟩ := IsPurelyInseparable.pow_mem L q ((1 : L) ⊗ₜ[K] b)
  refine ⟨n, f l, ?_⟩
  have hp : ((1 : L) ⊗ₜ[K] b) ^ q ^ n = (1 : L) ⊗ₜ[K] (b ^ q ^ n) := by
    simpa only [includeRight_apply] using
      (map_pow (includeRight : B →ₐ[K] L ⊗[K] B) b (q ^ n)).symm
  have he : l ⊗ₜ[K] (1 : B) = (1 : L) ⊗ₜ[K] (b ^ q ^ n) := by
    simpa only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, hp] using hl
  have := congrArg π he
  simpa only [hπ, hf, one_smul, Algebra.algebraMap_eq_smul_one] using this

end Algebra.TensorProduct
