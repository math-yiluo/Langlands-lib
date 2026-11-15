import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Conjugacy of nilpotent matrices

* `exists_conj_strictUpper`: a nilpotent matrix is conjugate to a strictly upper triangular one.
* `exists_conj_of_regular`: two strictly upper triangular matrices whose superdiagonal entries
  are all nonzero are conjugate.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

open Module

section Triangular

universe u

variable {K : Type*} [Field K]

/-- A nilpotent endomorphism of a finite-dimensional vector space of dimension `d` has an ordered
basis `b` with `f (b q) ∈ span {b p | p < q}`. -/
theorem exists_basis_strictUpper (d : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = d → ∀ f : V →ₗ[K] V, IsNilpotent f →
      ∃ b : Basis (Fin d) K V, ∀ q : Fin d, f (b q) ∈ Submodule.span K (b '' Set.Iio q) := by
  induction d with
  | zero =>
    intro V _ _ _ hV f _
    exact ⟨finBasisOfFinrankEq K V hV, fun q => q.elim0⟩
  | succ d ih =>
    intro V _ _ _ hV f hf
    obtain ⟨k, hk⟩ := hf
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    -- a nonzero kernel vector
    have hker : LinearMap.ker f ≠ ⊥ := by
      intro h
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp h
      have hinjk : Function.Injective (f ^ k) := by
        rw [Module.End.coe_pow]
        exact hinj.iterate k
      rw [hk] at hinjk
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      exact hx (hinjk (by simp))
    obtain ⟨y, hyker, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hfy : f y = 0 := hyker
    set S : Submodule K V := K ∙ y with hS
    obtain ⟨W, hSW⟩ := Submodule.exists_isCompl S
    have hWS : IsCompl W S := hSW.symm
    have hWrank : finrank K W = d := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hSW
      rw [finrank_span_singleton hy, hV] at h1
      omega
    -- f kills S
    have hfS : ∀ s ∈ S, f s = 0 := by
      intro s hs
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
      rw [map_smul, hfy, smul_zero]
    let P : V →ₗ[K] W := W.projectionOnto S hWS
    have hsub : ∀ x : V, x - (P x : V) ∈ S := fun x => Submodule.sub_projection_mem hWS x
    have hfP : ∀ x : V, f x = f (P x : V) := by
      intro x
      have := hfS _ (hsub x)
      rw [map_sub, sub_eq_zero] at this
      exact this
    let g : W →ₗ[K] W := P ∘ₗ f ∘ₗ W.subtype
    have hgpow : ∀ j : ℕ, ∀ w : W, (g ^ j) w = P ((f ^ j) (w : V)) := by
      intro j
      induction j with
      | zero =>
        intro w
        simp [P, Submodule.projectionOnto_apply_left]
      | succ j ihj =>
        intro w
        rw [pow_succ', Module.End.mul_apply, ihj, pow_succ', Module.End.mul_apply]
        simp only [g, LinearMap.comp_apply, Submodule.subtype_apply]
        rw [← hfP]
    have hg : IsNilpotent g := by
      refine ⟨k, LinearMap.ext fun w => ?_⟩
      rw [hgpow, hk]
      simp
    obtain ⟨b', hb'⟩ := ih W hWrank g hg
    have hli : ∀ (c : K), ∀ x ∈ W, c • y + x = 0 → c = 0 := by
      intro c x hx hcx
      have hcy : c • y ∈ W := by
        rw [eq_neg_of_add_eq_zero_left hcx]
        exact W.neg_mem hx
      have hcyS : c • y ∈ S := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
      have h0 : c • y = 0 := (Submodule.disjoint_def.mp hWS.disjoint) _ hcy hcyS
      exact (smul_eq_zero.mp h0).resolve_right hy
    have hsp : ∀ z : V, ∃ c : K, z + c • y ∈ W := by
      intro z
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hsub z)
      refine ⟨-a, ?_⟩
      have : z + (-a) • y = (P z : V) := by
        rw [neg_smul, ha]
        abel
      rw [this]
      exact (P z).2
    let B : Basis (Fin (d + 1)) K V := Basis.mkFinCons y b' hli hsp
    have hB0 : B 0 = y := by simp [B, Basis.coe_mkFinCons]
    have hBs : ∀ p : Fin d, B p.succ = (b' p : V) := by
      intro p
      simp [B, Basis.coe_mkFinCons]
    refine ⟨B, fun q => ?_⟩
    refine Fin.cases ?_ (fun q => ?_) q
    · rw [hB0, hfy]
      exact Submodule.zero_mem _
    · rw [hBs]
      have hyB : y ∈ Submodule.span K (B '' Set.Iio q.succ) := by
        apply Submodule.subset_span
        exact ⟨0, Fin.succ_pos q, hB0⟩
      have hgB : ((g (b' q) : W) : V) ∈ Submodule.span K (B '' Set.Iio q.succ) := by
        have h1 : ((g (b' q) : W) : V) ∈ (Submodule.span K (b' '' Set.Iio q)).map W.subtype :=
          Submodule.mem_map_of_mem (hb' q)
        rw [Submodule.map_span] at h1
        refine Submodule.span_mono ?_ h1
        rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p.succ, Fin.succ_lt_succ_iff.mpr hp, hBs p⟩
      have hdecomp : f (b' q : V) = ((g (b' q) : W) : V) + (f (b' q : V) - (P (f (b' q : V)) : V)) := by
        simp [g]
      rw [hdecomp]
      refine Submodule.add_mem _ hgB ?_
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hsub (f (b' q : V)))
      rw [← ha]
      exact Submodule.smul_mem _ _ hyB

/-- Over a field, a nilpotent square matrix is conjugate to a strictly upper triangular one. -/
theorem exists_conj_strictUpper_field {m : ℕ} (M : Matrix (Fin m) (Fin m) K) (hM : IsNilpotent M) :
    ∃ g : (Matrix (Fin m) (Fin m) K)ˣ, ∀ p q : Fin m, q ≤ p →
      ((g : Matrix (Fin m) (Fin m) K) * M * (↑g⁻¹ : Matrix (Fin m) (Fin m) K)) p q = 0 := by
  let f : (Fin m → K) →ₗ[K] (Fin m → K) := Matrix.toLinAlgEquiv' M
  have hf : IsNilpotent f := IsNilpotent.map hM (Matrix.toLinAlgEquiv' (R := K) (n := Fin m))
  obtain ⟨b, hb⟩ := exists_basis_strictUpper (K := K) m (Fin m → K) (finrank_fin_fun K) f hf
  let e := Pi.basisFun K (Fin m)
  let g : (Matrix (Fin m) (Fin m) K)ˣ :=
    ⟨b.toMatrix e, e.toMatrix b, b.toMatrix_mul_toMatrix_flip e, e.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨g, fun p q hqp => ?_⟩
  have hconj : (g : Matrix (Fin m) (Fin m) K) * M * (↑g⁻¹ : Matrix (Fin m) (Fin m) K) =
      LinearMap.toMatrix b b f := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b) (c := b) (b' := e)
      (c' := e) (f := f)]
    congr 2
    rw [LinearMap.toMatrix_eq_toMatrix']
    exact (LinearMap.toMatrix'_toLin' M).symm
  rw [hconj, LinearMap.toMatrix_apply]
  have hsupp := (Basis.mem_span_image b).mp (hb q)
  by_contra hne
  have hp : p ∈ ((b.repr (f (b q))).support : Set (Fin m)) := by
    simpa using hne
  have := hsupp hp
  simp only [Set.mem_Iio] at this
  exact absurd hqp (not_le.mpr this)

/-- A nilpotent complex matrix is conjugate to a strictly upper triangular one. -/
theorem exists_conj_strictUpper {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : IsNilpotent M) :
    ∃ g : (Matrix (Fin m) (Fin m) ℂ)ˣ, ∀ p q : Fin m, q ≤ p →
      ((g : Matrix (Fin m) (Fin m) ℂ) * M * (↑g⁻¹ : Matrix (Fin m) (Fin m) ℂ)) p q = 0 :=
  exists_conj_strictUpper_field M hM

end Triangular

section Regular

variable {K : Type*} [Field K] {m : ℕ}

/-- Entries of `U ^ k` vanish below the `k`-th superdiagonal when `U` is strictly upper
triangular. -/
theorem strictUpper_pow_apply_eq_zero (U : Matrix (Fin m) (Fin m) K)
    (hU : ∀ p q : Fin m, q ≤ p → U p q = 0) (k : ℕ) :
    ∀ p q : Fin m, (q : ℕ) < p + k → (U ^ k) p q = 0 := by
  induction k with
  | zero =>
    intro p q h
    rw [pow_zero, Matrix.one_apply_ne]
    intro hpq
    rw [hpq] at h
    omega
  | succ k ih =>
    intro p q h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : (r : ℕ) < p + k
    · rw [ih p r hr, zero_mul]
    · rw [hU r q (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]

/-- Entries of `U ^ k` on the `k`-th superdiagonal are nonzero when `U` is strictly upper
triangular with nonzero superdiagonal entries. -/
theorem regular_pow_apply_ne_zero (U : Matrix (Fin m) (Fin m) K)
    (hU : ∀ p q : Fin m, q ≤ p → U p q = 0) (hU' : ∀ p q : Fin m, (q : ℕ) = p + 1 → U p q ≠ 0)
    (k : ℕ) : ∀ p q : Fin m, (q : ℕ) = p + k → (U ^ k) p q ≠ 0 := by
  induction k with
  | zero =>
    intro p q h
    have hpq : p = q := Fin.ext (by omega)
    rw [hpq, pow_zero, Matrix.one_apply_eq]
    exact one_ne_zero
  | succ k ih =>
    intro p q h
    let r : Fin m := ⟨p + k, by omega⟩
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single r]
    · exact mul_ne_zero (ih p r rfl) (hU' r q (by simp [r]; omega))
    · intro r' _ hr'
      by_cases h1 : (r' : ℕ) < p + k
      · rw [strictUpper_pow_apply_eq_zero U hU k p r' h1, zero_mul]
      · have h2 : (r' : ℕ) ≠ p + k := fun h' => hr' (Fin.ext h')
        rw [hU r' q (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ r) h'

variable {n : ℕ}

/-- The standard regular nilpotent matrix: ones on the superdiagonal. -/
def superdiagOne (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun p q => if (q : ℕ) = p + 1 then 1 else 0

/-- The cyclic-vector matrix of `U`: its column `q` is `U ^ (n - q) e_last`. -/
def cyclicMatrix (U : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of fun p q => (U ^ (n - (q : ℕ))) p (Fin.last n)

theorem cyclicMatrix_mul (U : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hU : ∀ p q : Fin (n + 1), q ≤ p → U p q = 0) :
    U * cyclicMatrix U = cyclicMatrix U * superdiagOne (n + 1) := by
  ext p q
  have hL : (U * cyclicMatrix U) p q = (U ^ (n - (q : ℕ) + 1)) p (Fin.last n) := by
    rw [pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    rfl
  rw [hL, Matrix.mul_apply]
  by_cases hq : (q : ℕ) = 0
  · rw [strictUpper_pow_apply_eq_zero U hU _ p _ (by simp; omega)]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    simp [superdiagOne, hq]
  · let r0 : Fin (n + 1) := ⟨q - 1, by omega⟩
    rw [Finset.sum_eq_single r0]
    · have hcond : (q : ℕ) = (r0 : ℕ) + 1 := by simp only [r0]; omega
      have hexp : n - (q : ℕ) + 1 = n - (r0 : ℕ) := by simp only [r0]; omega
      rw [hexp]
      simp [cyclicMatrix, superdiagOne, hcond]
    · intro r _ hr
      have : (q : ℕ) ≠ r + 1 := fun h => hr (Fin.ext (by simp [r0]; omega))
      simp [superdiagOne, this]
    · intro h
      exact absurd (Finset.mem_univ r0) h

theorem isUnit_cyclicMatrix (U : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hU : ∀ p q : Fin (n + 1), q ≤ p → U p q = 0)
    (hU' : ∀ p q : Fin (n + 1), (q : ℕ) = p + 1 → U p q ≠ 0) :
    IsUnit (cyclicMatrix U) := by
  have htri : (cyclicMatrix U).IsUpperTriangular := by
    intro p q hqp
    simp only [cyclicMatrix, Matrix.of_apply]
    have : (q : ℕ) < p := hqp
    exact strictUpper_pow_apply_eq_zero U hU _ p _ (by simp; omega)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular htri, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  intro q _
  simp only [cyclicMatrix, Matrix.of_apply]
  exact regular_pow_apply_ne_zero U hU hU' _ q _ (by simp; omega)

/-- A strictly upper triangular matrix with nonzero superdiagonal is conjugate to the standard
one. -/
theorem exists_conj_superdiagOne (U : Matrix (Fin m) (Fin m) K)
    (hU : ∀ p q : Fin m, q ≤ p → U p q = 0) (hU' : ∀ p q : Fin m, (q : ℕ) = p + 1 → U p q ≠ 0) :
    ∃ g : (Matrix (Fin m) (Fin m) K)ˣ,
      (g : Matrix (Fin m) (Fin m) K) * U * (↑g⁻¹ : Matrix (Fin m) (Fin m) K) = superdiagOne m := by
  cases m with
  | zero => exact ⟨1, Subsingleton.elim _ _⟩
  | succ n =>
    have hC := isUnit_cyclicMatrix U hU hU'
    refine ⟨hC.unit⁻¹, ?_⟩
    rw [inv_inv, IsUnit.unit_spec, mul_assoc, cyclicMatrix_mul U hU, ← mul_assoc,
      IsUnit.val_inv_mul, one_mul]

/-- Over a field, two strictly upper triangular matrices with nonzero superdiagonal entries are
conjugate. -/
theorem exists_conj_of_regular_field (U V : Matrix (Fin m) (Fin m) K)
    (hU : ∀ p q : Fin m, q ≤ p → U p q = 0) (hU' : ∀ p q : Fin m, (q : ℕ) = p + 1 → U p q ≠ 0)
    (hV : ∀ p q : Fin m, q ≤ p → V p q = 0) (hV' : ∀ p q : Fin m, (q : ℕ) = p + 1 → V p q ≠ 0) :
    ∃ g : (Matrix (Fin m) (Fin m) K)ˣ,
      (g : Matrix (Fin m) (Fin m) K) * U * (↑g⁻¹ : Matrix (Fin m) (Fin m) K) = V := by
  obtain ⟨gU, hgU⟩ := exists_conj_superdiagOne U hU hU'
  obtain ⟨gV, hgV⟩ := exists_conj_superdiagOne V hV hV'
  refine ⟨gV⁻¹ * gU, ?_⟩
  calc ((gV⁻¹ * gU : (Matrix (Fin m) (Fin m) K)ˣ) : Matrix (Fin m) (Fin m) K) * U *
        (↑(gV⁻¹ * gU)⁻¹ : Matrix (Fin m) (Fin m) K)
      = (↑gV⁻¹ : Matrix (Fin m) (Fin m) K) * ((gU : Matrix (Fin m) (Fin m) K) * U *
          (↑gU⁻¹ : Matrix (Fin m) (Fin m) K)) * (gV : Matrix (Fin m) (Fin m) K) := by
        simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]
    _ = (↑gV⁻¹ : Matrix (Fin m) (Fin m) K) * ((gV : Matrix (Fin m) (Fin m) K) * V *
          (↑gV⁻¹ : Matrix (Fin m) (Fin m) K)) * (gV : Matrix (Fin m) (Fin m) K) := by
        rw [hgU, hgV]
    _ = V := by
        simp only [mul_assoc, Units.inv_mul, mul_one]
        rw [← mul_assoc, Units.inv_mul, one_mul]

/-- Two complex strictly upper triangular matrices with nonzero superdiagonal entries are
conjugate. -/
theorem exists_conj_of_regular {m : ℕ} (U V : Matrix (Fin m) (Fin m) ℂ)
    (hU : ∀ p q : Fin m, q ≤ p → U p q = 0) (hU' : ∀ p q : Fin m, (q : ℕ) = p + 1 → U p q ≠ 0)
    (hV : ∀ p q : Fin m, q ≤ p → V p q = 0) (hV' : ∀ p q : Fin m, (q : ℕ) = p + 1 → V p q ≠ 0) :
    ∃ g : (Matrix (Fin m) (Fin m) ℂ)ˣ,
      (g : Matrix (Fin m) (Fin m) ℂ) * U * (↑g⁻¹ : Matrix (Fin m) (Fin m) ℂ) = V :=
  exists_conj_of_regular_field U V hU hU' hV hV'

end Regular

end Langlands.Archimedean.Kostant
