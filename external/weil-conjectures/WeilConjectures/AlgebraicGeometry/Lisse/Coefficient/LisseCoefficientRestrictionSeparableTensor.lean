/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
import WeilConjectures.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite

/-! An integral multiple of the finite separability tensor.

## References

* Deligne, Weil II (1.1.1) d), pp. 146-147
* Stacks Project, Algebra, finite separable diagonal
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe d
open scoped TensorProduct nonZeroDivisors
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
  (E L : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The integer tensor square contains a central tensor with nonzero multiplication. -/
theorem lisseIntegerInclusion_separability_tensor :
    let R := Padic.coefficientExtensionIntegers l E
    let S := Padic.coefficientExtensionIntegers l L
    let : Algebra R S := (lisseIntegerInclusion l E L ι).toAlgebra
    ∃ t : TensorProduct R S S,
      Algebra.TensorProduct.lmul' R t ≠ 0 ∧
      ∀ s : S, (TensorProduct.tmul R s 1 - TensorProduct.tmul R 1 s) * t = 0 := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let f := lisseIntegerInclusion l E L ι
  let : Algebra E L := ι.toRingHom.toAlgebra
  let : Algebra R L := (ι.toRingHom.comp R.subtype).toAlgebra
  let : Algebra R S := f.toAlgebra
  have : IsScalarTower ℚ_[l] E L := IsScalarTower.of_algHom ι
  have : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun x ↦
    ((lisseIntegerInclusion_exists l E L ι).choose_spec x).symm
  have : FiniteDimensional E L := FiniteDimensional.right ℚ_[l] E L
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have : Algebra.IsSeparable E L := inferInstance
  have hd := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsFractionRing R E := hd.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing R := hd.2.2.2.2.2.2.2.2.1
  have : IsIntegralClosure S R L :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := by
        intro x
        change x ∈ integralClosure R L ↔ ∃ y : S, (y : L) = x
        rw [← Padic.padic_integers_integralClosure l E L ι x]
        exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩ }
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R E L
  have : Module.Free R S := IsIntegralClosure.module_free R E L S
  have : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization_of_isSeparable R E L S
  let j := (IsScalarTower.toAlgHom R S L).toLinearMap
  have : IsLocalizedModule R⁰ j := inferInstance
  let j₂ := TensorProduct.map j j
  have : IsLocalizedModule R⁰ j₂ := inferInstance
  have : Module.Free R (TensorProduct R S S) := inferInstance
  have hj₂ : Function.Injective j₂ := by
    apply (IsLocalizedModule.injective_iff_isRegular R⁰ j₂).mpr
    intro c
    exact (IsRegular.of_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp c.property)).isSMulRegular
  have : Algebra.FormallyUnramified E L := Algebra.FormallyUnramified.of_isSeparable E L
  obtain ⟨t, htc, htm⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct
    (R := E) (S := L)).mp inferInstance
  let e := IsLocalization.algebraTensorEquiv R⁰ E L L
  obtain ⟨⟨u, a⟩, hua⟩ := IsLocalizedModule.surj R⁰ j₂ (e t)
  let J := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S L)
    (IsScalarTower.toAlgHom R S L)
  have hJ (v : TensorProduct R S S) : J v = j₂ v := rfl
  have he (x y : L) : e (TensorProduct.tmul E x y) = TensorProduct.tmul R x y := rfl
  have hem (v : TensorProduct E L L) :
      Algebra.TensorProduct.lmul' R (e v) = Algebra.TensorProduct.lmul' E v := by
    induction v using TensorProduct.inductionOn with
    | tmul x y => rw [he, Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmul (v : TensorProduct R S S) :
      Algebra.TensorProduct.lmul' R (J v) =
        algebraMap S L (Algebra.TensorProduct.lmul' R v) := by
    induction v using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [J, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hμ : algebraMap S L (Algebra.TensorProduct.lmul' R u) =
      (a : R) • (1 : L) := by
    rw [← hmul, hJ, ← hua]
    change Algebra.TensorProduct.lmul' R ((a : R) • e t) = _
    rw [map_smul, hem, htm]
  refine ⟨u, ?_, ?_⟩
  · intro h0
    have hu0 : Algebra.TensorProduct.lmul' R u = 0 := h0
    rw [hu0, map_zero] at hμ
    have ha : (a : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a.property
    have hinj : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R E L]
      exact (algebraMap E L).injective.comp (IsFractionRing.injective R E)
    apply ha
    apply hinj
    simpa only [map_zero, Algebra.smul_def, mul_one] using hμ.symm
  · intro s
    have hc :
        (TensorProduct.tmul R (algebraMap S L s) 1 -
          TensorProduct.tmul R 1 (algebraMap S L s)) * e t = 0 := by
      have ht : (TensorProduct.tmul E (algebraMap S L s) 1 -
          TensorProduct.tmul E 1 (algebraMap S L s)) * t = 0 := by
        rw [← neg_sub, neg_mul, htc, neg_zero]
      simpa only [map_mul, map_sub, he, map_zero] using congrArg e ht
    apply hj₂
    change J ((TensorProduct.tmul R s 1 - TensorProduct.tmul R 1 s) * u) = J 0
    rw [map_mul, map_sub, map_zero, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul]
    change (TensorProduct.tmul R (algebraMap S L s) 1 -
      TensorProduct.tmul R 1 (algebraMap S L s)) * j₂ u = 0
    rw [← hua]
    change (TensorProduct.tmul R (algebraMap S L s) 1 -
      TensorProduct.tmul R 1 (algebraMap S L s)) * ((a : R) • e t) = 0
    rw [mul_smul_comm, hc, smul_zero]

end AlgebraicGeometry.Scheme
