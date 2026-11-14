import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.GroupScheme.SpecialLinearInnerForm.GaloisDescent
import Langlands.LinearAlgebra.MatrixUnitConjugation
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.IndexNormal

/-! # Splitting the twisted matrix algebra of a unitary projective cocycle -/

noncomputable section

universe u

namespace Langlands.LinearAlgebra.UnitaryTwistedDescent

open Matrix

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  {m : Type} [Fintype m] [DecidableEq m]

open Classical in
/-- The semilinear action of `σ` on matrices twisted by `x σ`: conjugation of `σ(N)` by
`x σ` when `σ` lies in `H`, and conjugation of the transpose of `σ(N)` otherwise. -/
def twistedAct (H : Subgroup (M ≃ₐ[K] M)) (x : (M ≃ₐ[K] M) → GL m M)
    (σ : M ≃ₐ[K] M) (N : Matrix m m M) : Matrix m m M :=
  if σ ∈ H then (x σ : Matrix m m M) * N.map σ * ((x σ)⁻¹ : GL m M)
  else (x σ : Matrix m m M) * (N.map σ)ᵀ * ((x σ)⁻¹ : GL m M)

omit [Fintype m] [DecidableEq m] in
theorem map_map_mul (σ τ : M ≃ₐ[K] M) (N : Matrix m m M) :
    (N.map τ).map σ = N.map (σ * τ) := by
  ext i j
  simp

omit [Fintype m] in
theorem map_one_alg (σ : M ≃ₐ[K] M) : (1 : Matrix m m M).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

/-- Conjugation by a unit equal to a scalar multiple of `A` is conjugation by `A`
and a right inverse of `A`. -/
theorem conj_eq_of_eq_smul (X : GL m M) (c : Mˣ) {A A' : Matrix m m M} (hA : A * A' = 1)
    (h : (X : Matrix m m M) = (c : M) • A) (N : Matrix m m M) :
    (X : Matrix m m M) * N * ((X⁻¹ : GL m M) : Matrix m m M) = A * N * A' := by
  have h1 : (X : Matrix m m M) * (((c⁻¹ : Mˣ) : M) • A') = 1 := by
    rw [h, smul_mul_smul_comm, hA, Units.mul_inv, one_smul]
  have hinv : ((X⁻¹ : GL m M) : Matrix m m M) = ((c⁻¹ : Mˣ) : M) • A' := by
    calc ((X⁻¹ : GL m M) : Matrix m m M)
        = ((X⁻¹ : GL m M) : Matrix m m M) * ((X : Matrix m m M) * (((c⁻¹ : Mˣ) : M) • A')) := by
          rw [h1, mul_one]
      _ = ((c⁻¹ : Mˣ) : M) • A' := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hinv, h, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv,
    one_smul]

/-- The right inverse of an inner product `X σ(Y)`. -/
theorem inner_mul_inv (σ : M ≃ₐ[K] M) (X Y : GL m M) :
    ((X : Matrix m m M) * (Y : Matrix m m M).map σ) *
      ((((Y⁻¹ : GL m M) : Matrix m m M).map σ) * ((X⁻¹ : GL m M) : Matrix m m M)) = 1 := by
  rw [mul_assoc, ← mul_assoc ((Y : Matrix m m M).map σ), ← Matrix.map_mul, Units.mul_inv,
    map_one_alg, one_mul, Units.mul_inv]

/-- The right inverse of an outer product `X θ(σ(Y))`. -/
theorem outer_mul_inv (σ : M ≃ₐ[K] M) (X Y : GL m M) :
    ((X : Matrix m m M) * ((((Y⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ)) *
      (((Y : Matrix m m M).map σ)ᵀ * ((X⁻¹ : GL m M) : Matrix m m M)) = 1 := by
  rw [mul_assoc, ← mul_assoc (((((Y⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ)), ← transpose_mul,
    ← Matrix.map_mul, Units.mul_inv, map_one_alg, transpose_one, one_mul, Units.mul_inv]

variable {H : Subgroup (M ≃ₐ[K] M)} {x : (M ≃ₐ[K] M) → GL m M}

/-- The twisted actions compose, given the twisted projective cocycle law and index two. -/
theorem twistedAct_mul (hH : H.index = 2)
    (hin : ∀ σ ∈ H, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ H, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ))
    (σ τ : M ≃ₐ[K] M) (N : Matrix m m M) :
    twistedAct H x (σ * τ) N = twistedAct H x σ (twistedAct H x τ N) := by
  have hmem := Subgroup.mul_mem_iff_of_index_two hH (a := σ) (b := τ)
  by_cases hσ : σ ∈ H <;> by_cases hτ : τ ∈ H
  · have hστ : σ * τ ∈ H := hmem.mpr (iff_of_true hσ hτ)
    obtain ⟨c, hc⟩ := hin σ hσ τ
    simp only [twistedAct, ite_eq_left hσ, ite_eq_left hτ, ite_eq_left hστ]
    rw [conj_eq_of_eq_smul _ c (inner_mul_inv σ (x σ) (x τ)) hc]
    simp only [Matrix.map_mul, map_map_mul, mul_assoc]
  · have hστ : σ * τ ∉ H := fun h => hτ ((hmem.mp h).mp hσ)
    obtain ⟨c, hc⟩ := hin σ hσ τ
    simp only [twistedAct, ite_eq_left hσ, ite_eq_right hτ, ite_eq_right hστ]
    rw [conj_eq_of_eq_smul _ c (inner_mul_inv σ (x σ) (x τ)) hc]
    simp only [Matrix.map_mul, transpose_map, map_map_mul, mul_assoc]
  · have hστ : σ * τ ∉ H := fun h => hσ ((hmem.mp h).mpr hτ)
    obtain ⟨c, hc⟩ := hout σ hσ τ
    simp only [twistedAct, ite_eq_right hσ, ite_eq_left hτ, ite_eq_right hστ]
    rw [conj_eq_of_eq_smul _ c (outer_mul_inv σ (x σ) (x τ)) hc]
    simp only [Matrix.map_mul, transpose_mul, map_map_mul, mul_assoc]
  · have hστ : σ * τ ∈ H := hmem.mpr (iff_of_false hσ hτ)
    obtain ⟨c, hc⟩ := hout σ hσ τ
    simp only [twistedAct, ite_eq_right hσ, ite_eq_right hτ, ite_eq_left hστ]
    rw [conj_eq_of_eq_smul _ c (outer_mul_inv σ (x σ) (x τ)) hc]
    simp only [Matrix.map_mul, transpose_mul, transpose_map, map_map_mul, transpose_transpose,
      mul_assoc]

theorem twistedAct_of_mem {σ : M ≃ₐ[K] M} (hσ : σ ∈ H) (N : Matrix m m M) :
    twistedAct H x σ N = (x σ : Matrix m m M) * N.map σ * ((x σ)⁻¹ : GL m M) := by
  simp only [twistedAct, ite_eq_left hσ]

theorem twistedAct_of_not_mem {σ : M ≃ₐ[K] M} (hσ : σ ∉ H) (N : Matrix m m M) :
    twistedAct H x σ N = (x σ : Matrix m m M) * (N.map σ)ᵀ * ((x σ)⁻¹ : GL m M) := by
  simp only [twistedAct, ite_eq_right hσ]

theorem algebraMap_map (σ : M ≃ₐ[K] M) (l : M) :
    (algebraMap M (Matrix m m M) l).map σ = algebraMap M (Matrix m m M) (σ l) := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero σ)]
  rfl

theorem conj_algebraMap (X : GL m M) (l : M) :
    (X : Matrix m m M) * algebraMap M (Matrix m m M) l * ((X⁻¹ : GL m M) : Matrix m m M) =
      algebraMap M (Matrix m m M) l := by
  rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

/-- The twisted action is `σ`-semilinear on scalar matrices. -/
theorem twistedAct_algebraMap (σ : M ≃ₐ[K] M) (l : M) :
    twistedAct H x σ (algebraMap M (Matrix m m M) l) = algebraMap M (Matrix m m M) (σ l) := by
  by_cases hσ : σ ∈ H
  · rw [twistedAct_of_mem hσ, algebraMap_map, conj_algebraMap]
  · rw [twistedAct_of_not_mem hσ, algebraMap_map, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_transpose, ← Matrix.algebraMap_eq_diagonal, conj_algebraMap]

theorem twistedAct_add (σ : M ≃ₐ[K] M) (N N' : Matrix m m M) :
    twistedAct H x σ (N + N') = twistedAct H x σ N + twistedAct H x σ N' := by
  by_cases hσ : σ ∈ H
  · simp only [twistedAct_of_mem hσ, Matrix.map_add _ (map_add σ), mul_add, add_mul]
  · simp only [twistedAct_of_not_mem hσ, Matrix.map_add _ (map_add σ), transpose_add, mul_add,
      add_mul]

/-- An outer twisted action reverses products. -/
theorem twistedAct_mul_of_not_mem {σ : M ≃ₐ[K] M} (hσ : σ ∉ H) (N N' : Matrix m m M) :
    twistedAct H x σ (N * N') = twistedAct H x σ N' * twistedAct H x σ N := by
  simp only [twistedAct_of_not_mem hσ, Matrix.map_mul, transpose_mul]
  have h : ((x σ)⁻¹ : GL m M) * (x σ : Matrix m m M) = 1 := Units.inv_mul _
  calc (x σ : Matrix m m M) * ((N'.map σ)ᵀ * (N.map σ)ᵀ) * ((x σ)⁻¹ : GL m M)
      = (x σ : Matrix m m M) * (N'.map σ)ᵀ * (((x σ)⁻¹ : GL m M) * (x σ : Matrix m m M)) *
          (N.map σ)ᵀ * ((x σ)⁻¹ : GL m M) := by rw [h, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- The inner twisted action of `σ` as a ring endomorphism of the matrix ring. -/
def innerRingHom (X : GL m M) (σ : M ≃ₐ[K] M) : Matrix m m M →+* Matrix m m M where
  toFun N := (X : Matrix m m M) * N.map σ * ((X⁻¹ : GL m M) : Matrix m m M)
  map_one' := by rw [map_one_alg, mul_one, Units.mul_inv]
  map_mul' N N' := by
    have h : ((X⁻¹ : GL m M) : Matrix m m M) * (X : Matrix m m M) = 1 := Units.inv_mul _
    rw [Matrix.map_mul]
    calc (X : Matrix m m M) * (N.map σ * N'.map σ) * ((X⁻¹ : GL m M) : Matrix m m M)
        = (X : Matrix m m M) * N.map σ * (((X⁻¹ : GL m M) : Matrix m m M) * X) * N'.map σ *
            ((X⁻¹ : GL m M) : Matrix m m M) := by rw [h, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' N N' := by simp only [Matrix.map_add _ (map_add σ), mul_add, add_mul]

theorem innerRingHom_apply (X : GL m M) (σ : M ≃ₐ[K] M) (N : Matrix m m M) :
    innerRingHom X σ N = (X : Matrix m m M) * N.map σ * ((X⁻¹ : GL m M) : Matrix m m M) := rfl

omit [Fintype m] [DecidableEq m] in
theorem map_one_aut (N : Matrix m m M) : N.map (1 : M ≃ₐ[K] M) = N := by
  ext i j
  rfl

/-- Cancelling a conjugation. -/
theorem conj_cancel (X : GL m M) (A : Matrix m m M) :
    ((X⁻¹ : GL m M) : Matrix m m M) * ((X : Matrix m m M) * A * ((X⁻¹ : GL m M) : Matrix m m M)) *
      (X : Matrix m m M) = A := by
  rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]

/-- The twisted action of the identity is the identity. -/
theorem twistedAct_one (hH : H.index = 2)
    (hin : ∀ σ ∈ H, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ H, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ))
    (N : Matrix m m M) : twistedAct H x 1 N = N := by
  have key := twistedAct_mul hH hin hout 1 1 N
  rw [one_mul] at key
  simp only [twistedAct_of_mem H.one_mem, map_one_aut] at key ⊢
  have e1 := conj_cancel (x 1) N
  rw [key, conj_cancel] at e1
  exact e1

section Descent

open IntermediateField

/-- An automorphism over an intermediate field `F` fixes `F` pointwise. -/
theorem restrictScalars_mem (F : IntermediateField K M) (σ : M ≃ₐ[F] M) :
    σ.restrictScalars K ∈ F.fixingSubgroup :=
  (mem_fixingSubgroup_iff F _).mpr fun y hy => σ.commutes ⟨y, hy⟩

/-- The twisted action of `Gal(M/F)` on `Matrix m m M`, where `F` is the fixed field of the
index-two subgroup `H` of inner automorphisms. -/
def galoisAction (F : IntermediateField K M) (hH : F.fixingSubgroup.index = 2)
    (hin : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ)) :
    Langlands.CentralSimple.SemilinearGaloisAction F M (Matrix m m M) where
  act σ := innerRingHom (x (σ.restrictScalars K)) (σ.restrictScalars K)
  act_algebraMap σ l := by
    rw [innerRingHom_apply, algebraMap_map, conj_algebraMap]
    rfl
  act_one N := by
    have h1 : (1 : M ≃ₐ[F] M).restrictScalars K = 1 := AlgEquiv.ext fun _ => rfl
    rw [innerRingHom_apply, h1, ← twistedAct_of_mem F.fixingSubgroup.one_mem]
    exact twistedAct_one hH hin hout N
  act_mul σ τ N := by
    have hrs : (σ * τ).restrictScalars K = σ.restrictScalars K * τ.restrictScalars K :=
      AlgEquiv.ext fun _ => rfl
    have h := twistedAct_mul hH hin hout (σ.restrictScalars K) (τ.restrictScalars K) N
    rw [twistedAct_of_mem (restrictScalars_mem F τ), twistedAct_of_mem (restrictScalars_mem F σ),
      ← hrs, twistedAct_of_mem (restrictScalars_mem F (σ * τ))] at h
    simp only [innerRingHom_apply]
    exact h

/-- An element fixed by the descent action is fixed by the twisted action of every
automorphism in the fixing subgroup of `F`. -/
theorem twistedAct_of_mem_fixed (F : IntermediateField K M) (hH : F.fixingSubgroup.index = 2)
    (hin : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ))
    {σ : M ≃ₐ[K] M} (hσ : σ ∈ F.fixingSubgroup) {b : Matrix m m M}
    (hb : b ∈ (galoisAction F hH hin hout).fixed) :
    twistedAct F.fixingSubgroup x σ b = b := by
  have heq : (fixingSubgroupEquiv F ⟨σ, hσ⟩).restrictScalars K = σ :=
    AlgEquiv.ext fun _ => rfl
  have h := ((galoisAction F hH hin hout).mem_fixed.mp hb) (fixingSubgroupEquiv F ⟨σ, hσ⟩)
  change innerRingHom _ _ b = b at h
  rw [heq, innerRingHom_apply] at h
  rw [twistedAct_of_mem hσ]
  exact h

/-- The twisted action of any automorphism preserves the descended algebra. -/
theorem twistedAct_mem_fixed (F : IntermediateField K M) (hH : F.fixingSubgroup.index = 2)
    (hin : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ))
    (r : M ≃ₐ[K] M) {b : Matrix m m M} (hb : b ∈ (galoisAction F hH hin hout).fixed) :
    twistedAct F.fixingSubgroup x r b ∈ (galoisAction F hH hin hout).fixed := by
  rw [Langlands.CentralSimple.SemilinearGaloisAction.mem_fixed]
  intro σ'
  have hs := restrictScalars_mem F σ'
  change innerRingHom _ _ _ = _
  rw [innerRingHom_apply, ← twistedAct_of_mem hs, ← twistedAct_mul hH hin hout]
  have hconj : σ'.restrictScalars K * r = r * (r⁻¹ * σ'.restrictScalars K * r) := by group
  have hmem : r⁻¹ * σ'.restrictScalars K * r ∈ F.fixingSubgroup := by
    have hN : F.fixingSubgroup.Normal := Subgroup.normal_of_index_eq_two hH
    simpa using hN.conj_mem _ hs r⁻¹
  rw [hconj, twistedAct_mul hH hin hout, twistedAct_of_mem_fixed F hH hin hout hmem hb]

/-- The involution of the descended algebra induced by the twisted action of `r`. -/
def outerInvolution (F : IntermediateField K M) (hH : F.fixingSubgroup.index = 2)
    (hin : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ))
    (r : M ≃ₐ[K] M) :
    (galoisAction F hH hin hout).fixed → (galoisAction F hH hin hout).fixed :=
  fun b => ⟨twistedAct F.fixingSubgroup x r b, twistedAct_mem_fixed F hH hin hout r b.2⟩

theorem coe_outerInvolution (F : IntermediateField K M) (hH : F.fixingSubgroup.index = 2)
    (hin : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ))
    (r : M ≃ₐ[K] M) (b : (galoisAction F hH hin hout).fixed) :
    (outerInvolution F hH hin hout r b : Matrix m m M) = twistedAct F.fixingSubgroup x r b :=
  rfl

/-- For `r` outside the fixing subgroup of the quadratic extension `F`, the induced map is a
unitary involution relative to the restriction of `r` to `F`. -/
theorem isUnitaryInvolution_outerInvolution (F : IntermediateField K M) [Normal K F]
    (hH : F.fixingSubgroup.index = 2)
    (hin : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ))
    {r : M ≃ₐ[K] M} (hr : r ∉ F.fixingSubgroup) :
    IsUnitaryInvolution (⇑(r.restrictNormal F)) (outerInvolution F hH hin hout r) := by
  refine ⟨fun a b => Subtype.ext ?_, fun a b => Subtype.ext ?_, fun a => Subtype.ext ?_,
    fun l => Subtype.ext ?_⟩
  · change twistedAct F.fixingSubgroup x r ((a : Matrix m m M) + (b : Matrix m m M)) =
      twistedAct F.fixingSubgroup x r a + twistedAct F.fixingSubgroup x r b
    exact twistedAct_add (H := F.fixingSubgroup) (x := x) r (a : Matrix m m M) (b : Matrix m m M)
  · change twistedAct F.fixingSubgroup x r ((a : Matrix m m M) * (b : Matrix m m M)) =
      twistedAct F.fixingSubgroup x r b * twistedAct F.fixingSubgroup x r a
    exact twistedAct_mul_of_not_mem (x := x) hr (a : Matrix m m M) (b : Matrix m m M)
  · rw [coe_outerInvolution, coe_outerInvolution, ← twistedAct_mul hH hin hout]
    exact twistedAct_of_mem_fixed F hH hin hout
      ((Subgroup.mul_mem_iff_of_index_two hH).mpr (iff_of_false hr hr)) a.2
  · rw [coe_outerInvolution]
    change twistedAct F.fixingSubgroup x r (algebraMap F (Matrix m m M) l) =
      algebraMap F (Matrix m m M) (r.restrictNormal F l)
    rw [IsScalarTower.algebraMap_apply F M (Matrix m m M),
      IsScalarTower.algebraMap_apply F M (Matrix m m M), twistedAct_algebraMap,
      AlgEquiv.restrictNormal_commutes]

/-- **Splitting a twisted unitary cocycle.** Let `M/K` be finite Galois, `F` an intermediate
field quadratic over `K`, and `x` a family of invertible matrices satisfying the twisted
projective cocycle law relative to `H = Gal(M/F)`. If every central simple algebra with a
unitary involution over a separable quadratic extension of `K` is split, there is `P` with
`P⁻¹ x(σ) σ(P)` scalar for every `σ ∈ H`. -/
theorem exists_conj_eq_scalar (hK : UnitaryInvolutionSplitting K) [FiniteDimensional K M]
    [IsGalois K M] [Nonempty m] (F : IntermediateField K M) [Algebra.IsQuadraticExtension K F]
    (hin : ∀ σ ∈ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * (x τ : Matrix m m M).map σ))
    (hout : ∀ σ ∉ F.fixingSubgroup, ∀ τ, ∃ c : Mˣ, (x (σ * τ) : Matrix m m M) =
      (c : M) • ((x σ : Matrix m m M) * ((((x τ)⁻¹ : GL m M) : Matrix m m M).map σ)ᵀ)) :
    ∃ P : GL m M, ∀ σ ∈ F.fixingSubgroup, ∃ c : Mˣ,
      P⁻¹ * x σ * GeneralLinearGroup.map σ.toRingHom P = GeneralLinearGroup.scalar m c := by
  have hH : F.fixingSubgroup.index = 2 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  obtain ⟨r, hr⟩ : ∃ r, r ∉ F.fixingSubgroup := by
    by_contra h
    push Not at h
    have htop : F.fixingSubgroup = ⊤ := eq_top_iff.mpr fun r _ => h r
    rw [htop, Subgroup.index_top] at hH
    exact absurd hH (by norm_num)
  set ρ := galoisAction F hH hin hout with hρ
  have : Algebra.IsSeparable K F := Algebra.isSeparable_tower_bot_of_isSeparable K F M
  have : FiniteDimensional F ρ.fixed := ρ.finiteDimensional_fixed
  have : IsSimpleRing ρ.fixed := ρ.isSimpleRing_fixed
  have : Algebra.IsCentral F ρ.fixed := ρ.isCentral_fixed
  have hσF : r.restrictNormal F ≠ 1 := by
    intro h1
    apply hr
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have h2 := AlgEquiv.restrictNormal_commutes r F ⟨y, hy⟩
    rw [h1] at h2
    simpa using h2.symm
  obtain ⟨k, ⟨e⟩⟩ := hK F (r.restrictNormal F) hσF ρ.fixed (outerInvolution F hH hin hout r)
    (isUnitaryInvolution_outerInvolution F hH hin hout hr)
  have hk : Fintype.card m = k := by
    have h1 := ρ.descentEquiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, e.toLinearEquiv.finrank_eq, Module.finrank_matrix,
      Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, Module.finrank_self,
      mul_one, mul_one] at h1
    exact (Nat.mul_self_inj.mp h1).symm
  let f : ρ.fixed ≃ₐ[F] Matrix m m F :=
    e.trans (Matrix.reindexAlgEquiv F F (Fintype.equivFinOfCardEq hk).symm)
  obtain ⟨E, hEdef⟩ : ∃ E : m → m → Matrix m m M,
      E = fun a b => ((f.symm (single a b 1) : ρ.fixed) : Matrix m m M) := ⟨_, rfl⟩
  have hEmem : ∀ a b : m, E a b ∈ ρ.fixed := by
    intro a b
    rw [hEdef]
    exact (f.symm (single a b 1)).2
  have hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    rw [hEdef]
    dsimp only
    rw [← Subalgebra.coe_mul, ← map_mul]
    split_ifs with hjk
    · rw [hjk, single_mul_single_same, one_mul]
    · rw [single_mul_single_of_ne (h := hjk), map_zero]
      rfl
  obtain ⟨p⟩ := ‹Nonempty m›
  have hp : E p p ≠ 0 := by
    intro h0
    rw [hEdef] at h0
    have h1 : f.symm (single p p 1) = 0 := Subtype.ext h0
    rw [map_eq_zero_iff _ f.symm.injective] at h1
    have h2 := congrFun (congrFun h1 p) p
    simp at h2
  obtain ⟨P, hP⟩ := MatrixUnitConjugation.exists_mul_single_eq E hE p hp
  refine ⟨P, fun σ hσ => ?_⟩
  have hXX : (((x σ)⁻¹ : GL m M) : Matrix m m M) * (x σ : Matrix m m M) = 1 := Units.inv_mul _
  have hPP : ((P⁻¹ : GL m M) : Matrix m m M) * (P : Matrix m m M) = 1 := Units.inv_mul _
  have hPP' : (P : Matrix m m M) * ((P⁻¹ : GL m M) : Matrix m m M) = 1 := Units.mul_inv _
  have hEσ : ∀ a b : m, (x σ : Matrix m m M) * (E a b).map σ = E a b * (x σ : Matrix m m M) := by
    intro a b
    have h := twistedAct_of_mem_fixed F hH hin hout hσ (hEmem a b)
    rw [twistedAct_of_mem hσ] at h
    calc (x σ : Matrix m m M) * (E a b).map σ
        = (x σ : Matrix m m M) * (E a b).map σ * (((x σ)⁻¹ : GL m M) : Matrix m m M) *
            (x σ : Matrix m m M) := by rw [mul_assoc _ _ (x σ : Matrix m m M), hXX, mul_one]
      _ = E a b * (x σ : Matrix m m M) := by rw [h]
  have hS : ∀ a b : m, (single a b (1 : M)).map σ = single a b 1 := by
    intro a b
    rw [Matrix.map_single, map_one]
  have hPσ : ∀ a b : m, (P : Matrix m m M).map σ * single a b 1 =
      (E a b).map σ * (P : Matrix m m M).map σ := by
    intro a b
    rw [← hS a b, ← Matrix.map_mul, hP a b, Matrix.map_mul]
  have hP' : ∀ a b : m, single a b (1 : M) * ((P⁻¹ : GL m M) : Matrix m m M) =
      ((P⁻¹ : GL m M) : Matrix m m M) * E a b := by
    intro a b
    calc single a b (1 : M) * ((P⁻¹ : GL m M) : Matrix m m M)
        = ((P⁻¹ : GL m M) : Matrix m m M) * ((P : Matrix m m M) * single a b 1) *
            ((P⁻¹ : GL m M) : Matrix m m M) := by
          rw [← mul_assoc _ (P : Matrix m m M), hPP, one_mul]
      _ = ((P⁻¹ : GL m M) : Matrix m m M) * (E a b * (P : Matrix m m M)) *
            ((P⁻¹ : GL m M) : Matrix m m M) := by rw [hP a b]
      _ = ((P⁻¹ : GL m M) : Matrix m m M) * E a b := by simp only [mul_assoc, hPP', mul_one]
  have hA : ((P⁻¹ * x σ * GeneralLinearGroup.map σ.toRingHom P : GL m M) : Matrix m m M) =
      ((P⁻¹ : GL m M) : Matrix m m M) * (x σ : Matrix m m M) * (P : Matrix m m M).map σ := rfl
  have hcomm : ∀ a b : m, Commute (single a b (1 : M))
      (((P⁻¹ : GL m M) : Matrix m m M) * (x σ : Matrix m m M) * (P : Matrix m m M).map σ) := by
    intro a b
    change single a b (1 : M) * (((P⁻¹ : GL m M) : Matrix m m M) * (x σ : Matrix m m M) *
        (P : Matrix m m M).map σ) = (((P⁻¹ : GL m M) : Matrix m m M) * (x σ : Matrix m m M) *
        (P : Matrix m m M).map σ) * single a b (1 : M)
    calc single a b (1 : M) * (((P⁻¹ : GL m M) : Matrix m m M) * (x σ : Matrix m m M) *
          (P : Matrix m m M).map σ)
        = (single a b (1 : M) * ((P⁻¹ : GL m M) : Matrix m m M)) * (x σ : Matrix m m M) *
          (P : Matrix m m M).map σ := by simp only [mul_assoc]
      _ = ((P⁻¹ : GL m M) : Matrix m m M) * (E a b * (x σ : Matrix m m M)) *
          (P : Matrix m m M).map σ := by rw [hP' a b]; simp only [mul_assoc]
      _ = ((P⁻¹ : GL m M) : Matrix m m M) * (x σ : Matrix m m M) *
          ((E a b).map σ * (P : Matrix m m M).map σ) := by
          rw [← hEσ a b]; simp only [mul_assoc]
      _ = _ := by rw [← hPσ a b]; simp only [mul_assoc]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr hcomm
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, ← hA] at hc
    exact Units.ne_zero _ hc.symm
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, hA, ← hc]

end Descent

end Langlands.LinearAlgebra.UnitaryTwistedDescent
