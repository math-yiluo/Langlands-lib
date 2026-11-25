import Langlands.ClassFieldTheory.Global.ArchimedeanNormPowerApproximation
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-! # Conjugation and norm-one units of a quadratic tensor algebra -/

noncomputable section

universe u

open NumberField
open scoped TensorProduct NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.ClassFieldTheory.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.Algebra.SeparableTensor
open Langlands.GroupScheme.SU3Root Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B S : Type u} [Field F] [Field B] [Algebra F B]
  [_root_.Algebra.IsQuadraticExtension F B] [Algebra.IsSeparable F B] [CommRing S] [Algebra F S]

local instance : FiniteDimensional F B :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F B]; decide)

/-- The involution on a quadratic tensor algebra obtained from its left factor. -/
def quadraticTensorConjugation : B ⊗[F] S ≃ₐ[F] B ⊗[F] S :=
  let e := Algebra.TensorProduct.comm F B S
  e.trans (((tensorConjugation F B S).restrictScalars F).trans e.symm)

@[simp]
theorem quadraticTensorConjugation_tmul (b : B) (s : S) :
    quadraticTensorConjugation (b ⊗ₜ[F] s) = conjugation F B b ⊗ₜ[F] s := rfl

theorem quadraticTensorConjugation_involutive :
    Function.Involutive (quadraticTensorConjugation (F := F) (B := B) (S := S)) := by
  intro x
  let e := Algebra.TensorProduct.comm F B S
  let t := tensorConjugation F B S
  change e.symm (t (e (e.symm (t (e x))))) = x
  rw [e.apply_symm_apply, tensorConjugation_involutive, e.symm_apply_apply]

/-- Quadratic conjugation on the actual tensor unit group. -/
def quadraticTensorUnitConjugation : (B ⊗[F] S)ˣ ≃* (B ⊗[F] S)ˣ :=
  Units.mapEquiv quadraticTensorConjugation.toMulEquiv

/-- Conjugating an extended unit agrees with extending its conjugate. -/
theorem quadraticTensorUnitConjugation_left {K : Type u} [Field K] [Algebra F K] (t : Bˣ) :
    quadraticTensorUnitConjugation (leftTensorUnit (F := F) (L := K) t) =
      leftTensorUnit (Units.map (conjugation F B).toMonoidHom t) := by
  apply Units.ext
  rfl

/-- The embedded determinant norm is the product of an element and its conjugate. -/
theorem includeRight_tensorNorm_quadratic (x : B ⊗[F] S) :
    (Algebra.TensorProduct.includeRight : S →ₐ[F] B ⊗[F] S) (tensorNorm F B S x) =
      x * quadraticTensorConjugation x := by
  classical
  let i : S →ₐ[F] B ⊗[F] S := Algebra.TensorProduct.includeRight
  let j := IsScalarTower.toAlgHom F B (B ⊗[F] S)
  let y := Algebra.TensorProduct.lTensor (S := B) B i x
  have hs (b : B) : ((minpoly F b).map (algebraMap F B)).Splits :=
    (inferInstance : Normal F B).splits b
  have hcoord (σ : B ≃ₐ[F] B) (z : B ⊗[F] S) :
      tensorCoordinate j σ.toAlgHom (Algebra.TensorProduct.lTensor (S := B) B i z) =
        Algebra.TensorProduct.congr σ (AlgEquiv.refl : S ≃ₐ[F] S) z := by
    induction z using TensorProduct.inductionOn with
    | tmul b s =>
      change j (σ b) * i s = σ b ⊗ₜ[F] s
      change (σ b ⊗ₜ[F] (1 : S)) * ((1 : B) ⊗ₜ[F] s) = _
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hconj :
      Algebra.TensorProduct.congr (conjugation F B) (AlgEquiv.refl : S ≃ₐ[F] S) x =
        quadraticTensorConjugation x := by
    induction x using TensorProduct.inductionOn with
    | tmul b s => rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  calc
    i (tensorNorm F B S x) = tensorNorm F B (B ⊗[F] S) y :=
      (tensorNorm_naturality i x).symm
    _ = ∏ φ : B →ₐ[F] B, tensorCoordinate j φ y :=
      separableEmbedding_tensorNorm F B B hs (B ⊗[F] S) y
    _ = ∏ σ : B ≃ₐ[F] B, tensorCoordinate j σ.toAlgHom y :=
      (Fintype.prod_equiv (algEquivEquivAlgHom F B).toEquiv _ _ (fun _ => rfl)).symm
    _ = x * quadraticTensorConjugation x := by
      rw [quadratic_aut_univ F B, Finset.prod_insert, Finset.prod_singleton]
      · rw [hcoord, hcoord, hconj]
        change Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B)
          (AlgEquiv.refl : S ≃ₐ[F] S) x * quadraticTensorConjugation x = _
        rw [Algebra.TensorProduct.congr_refl]
        rfl
      · simp [Ne.symm (conjugation_ne_one F B)]

/-- The corresponding norm-conjugation formula on units. -/
theorem scalarTensorUnit_tensorNormUnits_quadratic (x : (B ⊗[F] S)ˣ) :
    scalarTensorUnit (tensorNormUnits F B S x) = x * quadraticTensorUnitConjugation x := by
  apply Units.ext
  exact includeRight_tensorNorm_quadratic (x : B ⊗[F] S)

/-- Determinant norm is invariant under quadratic conjugation of tensor units. -/
theorem tensorNormUnits_quadraticTensorUnitConjugation (x : (B ⊗[F] S)ˣ) :
    tensorNormUnits F B S (quadraticTensorUnitConjugation x) = tensorNormUnits F B S x := by
  apply Units.ext
  let e := Algebra.TensorProduct.comm F B S
  let t := tensorConjugation F B S
  change Algebra.norm S (e (e.symm (t (e (x : B ⊗[F] S))))) = Algebra.norm S (e (x : B ⊗[F] S))
  rw [e.apply_symm_apply, Algebra.norm_eq_of_algEquiv t]

section Hilbert90

variable {K : Type u} [Field K] [Algebra F K] [IsReduced (B ⊗[F] K)]

/-- Hilbert 90 for determinant norm-one units in a reduced quadratic tensor over a field. -/
theorem exists_quadraticTensorUnit_div_conjugate (x : (B ⊗[F] K)ˣ)
    (hx : tensorNormUnits F B K x = 1) :
    ∃ t : (B ⊗[F] K)ˣ, x = t / quadraticTensorUnitConjugation t := by
  classical
  let τ := quadraticTensorConjugation (F := F) (B := B) (S := K)
  by_cases hneg : (x : B ⊗[F] K) = -1
  · obtain ⟨b, hb⟩ : ∃ b : B, conjugation F B b ≠ b := by
      by_contra! h
      exact conjugation_ne_one F B (AlgEquiv.ext h)
    let a := Units.mk0 (b - conjugation F B b) (sub_ne_zero.mpr hb.symm)
    refine ⟨leftTensorUnit a, eq_div_iff_mul_eq'.mpr (Units.ext ?_)⟩
    change (x : B ⊗[F] K) * τ (((a : Bˣ) : B) ⊗ₜ[F] (1 : K)) = (a : B) ⊗ₜ[F] (1 : K)
    rw [hneg, show τ ((a : B) ⊗ₜ[F] (1 : K)) = -((a : B) ⊗ₜ[F] (1 : K)) from ?_]
    · simp
    · change conjugation F B (b - conjugation F B b) ⊗ₜ[F] (1 : K) =
        -((b - conjugation F B b) ⊗ₜ[F] (1 : K))
      rw [map_sub, conjugation_involutive, ← TensorProduct.neg_tmul, neg_sub]
  · have hxτ : τ (x : B ⊗[F] K) = ↑x⁻¹ := by
      have h := scalarTensorUnit_tensorNormUnits_quadratic x
      rw [hx, map_one] at h
      exact Units.eq_inv_of_mul_eq_one_left (congrArg Units.val h.symm)
    let y := 1 + (x : B ⊗[F] K)
    have hyτ : τ y = y * ↑x⁻¹ := by
      simp [y, hxτ, add_mul, add_comm]
    have hyN : tensorNorm F B K y ≠ 0 := by
      intro hz
      have hzero : y * τ y = 0 := by
        rw [← includeRight_tensorNorm_quadratic, hz, map_zero]
      have hsq : y ^ 2 = 0 := calc
        y ^ 2 = (y * τ y) * (x : B ⊗[F] K) := by simp [hyτ, pow_two, mul_assoc]
        _ = 0 := by rw [hzero, zero_mul]
      have hz' : 1 + (x : B ⊗[F] K) = 0 := isNilpotent_iff_eq_zero.mp ⟨2, hsq⟩
      exact hneg (eq_neg_of_add_eq_zero_right hz')
    let i : K →ₐ[F] B ⊗[F] K := Algebra.TensorProduct.includeRight
    have hyprod : y * (τ y * i ((tensorNorm F B K y)⁻¹)) = 1 := by
      rw [← mul_assoc, ← includeRight_tensorNorm_quadratic]
      change i (tensorNorm F B K y) * i ((tensorNorm F B K y)⁻¹) = 1
      rw [← map_mul, mul_inv_cancel₀ hyN, map_one]
    let t := Units.mkOfMulEqOne y (τ y * i ((tensorNorm F B K y)⁻¹)) hyprod
    refine ⟨t, eq_div_iff_mul_eq'.mpr (Units.ext ?_)⟩
    change (x : B ⊗[F] K) * τ y = y
    rw [hyτ, mul_left_comm, Units.mul_inv, mul_one]

end Hilbert90

open Langlands.Global.AdelicFunctoriality in
/-- The reduced quadratic tensor Hilbert 90 applies to the full archimedean completion. -/
theorem exists_archimedeanTensorUnit_div_conjugate [NumberField F] [NumberField B]
    (v : InfinitePlace F) (x : (B ⊗[F] v.Completion)ˣ)
    (hx : tensorNormUnits F B v.Completion x = 1) :
    ∃ t : (B ⊗[F] v.Completion)ˣ, x = t / quadraticTensorUnitConjugation t := by
  let e := (Algebra.TensorProduct.comm F B v.Completion).toRingEquiv.trans
    (infiniteTensorEquiv (L := B) v).toRingEquiv
  let : IsReduced (B ⊗[F] v.Completion) := isReduced_of_injective e e.injective
  exact exists_quadraticTensorUnit_div_conjugate x hx

end Langlands.ClassFieldTheory.Global.TensorUnitShapiro
