import Langlands.LinearAlgebra.EpsilonHermitian.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The determinant of an `ε`-Hermitian space over a field with involution

GKT §4.5.1: the determinant `det(ρ) ∈ E^× / 𝒩_{E/F}(E^×)` of a non-degenerate `ε`-Hermitian space
(4.12), the norm map `𝒩_{E/F}(a) = a a^τ` (4.13), and the second assertion of Lemma 4.34
(`det(ρ)^τ = ε^n det(ρ)`), for a commutative `D = E` (a field `K` with an involution `τ`, `r = 1`).
Also an abstract form of Lemma 4.29: automorphisms of two spaces in non-degenerate
`τ`-sesquilinear duality have determinants `d, d'` with `d' d^τ = 1`.
-/

noncomputable section

open Matrix

namespace Langlands

open Module

namespace RingInvo

variable {K : Type*} [Field K] (τ : _root_.RingInvo K)

/-- For a field, `d ↦ d^τ` is a ring endomorphism (an automorphism of order `≤ 2`). -/
def conjRingHom : K →+* K where
  toFun := conj τ
  map_one' := conj_one τ
  map_mul' a b := by rw [RingInvo.conj_mul, mul_comm]
  map_zero' := conj_zero τ
  map_add' := conj_add τ

@[simp] theorem conjRingHom_apply (a : K) : conjRingHom τ a = conj τ a := rfl

/-- The norm map `𝒩_{E/F} : a ↦ a a^τ` on units (GKT (4.13)). -/
def normHom : Kˣ →* Kˣ := MonoidHom.id Kˣ * Units.map (conjRingHom τ).toMonoidHom

@[simp] theorem coe_normHom (a : Kˣ) : (normHom τ a : K) = a * conj τ a := rfl

/-- The norm subgroup `𝒩_{E/F}(E^×)` of `E^×`: the norms if `[E : F] = 2`, the squares if `τ = id`
(GKT (4.13)). -/
def normSubgroup : Subgroup Kˣ := (normHom τ).range

theorem normHom_mem (a : Kˣ) : normHom τ a ∈ normSubgroup τ := ⟨a, rfl⟩

@[simp] theorem mk_normHom (a : Kˣ) :
    (QuotientGroup.mk (normHom τ a) : Kˣ ⧸ normSubgroup τ) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (normHom_mem τ a)

/-- Modulo norms, `a^τ ≡ a⁻¹`. -/
theorem mk_map_conj (a : Kˣ) :
    (QuotientGroup.mk (Units.map (conjRingHom τ).toMonoidHom a) : Kˣ ⧸ normSubgroup τ) =
      (QuotientGroup.mk a)⁻¹ := by
  rw [← QuotientGroup.mk_inv, QuotientGroup.eq]
  have : (Units.map (conjRingHom τ).toMonoidHom a)⁻¹ * a⁻¹ = (normHom τ a)⁻¹ := by
    rw [← mul_inv, mul_comm]; rfl
  rw [this]
  exact inv_mem (normHom_mem τ a)

theorem mk_eq_mk_of_coe_eq_mul_norm {a b c : Kˣ} (H : (a : K) = b * (c * conj τ c)) :
    (QuotientGroup.mk a : Kˣ ⧸ normSubgroup τ) = QuotientGroup.mk b := by
  have : a = b * normHom τ c := Units.ext (by rw [Units.val_mul, coe_normHom, H])
  rw [QuotientGroup.eq, this, _root_.mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem (normHom_mem τ c)

end RingInvo

namespace EpsilonHermitianForm

open Langlands.RingInvo (conj conjRingHom conjRingHom_apply)

variable {K : Type*} [Field K] {τ : _root_.RingInvo K} {ε : ℤˣ}
  {U : Type*} [AddCommGroup U] [Module K U] (k : EpsilonHermitianForm τ ε U)

/-! ### The Gram matrix -/

/-- The Gram matrix `((xᵢ, xⱼ))` of a form in a basis (GKT (4.12)). -/
def gramMatrix {ι : Type*} (b : Basis ι K U) : Matrix ι ι K := Matrix.of fun i j => k (b i) (b j)

@[simp] theorem gramMatrix_apply {ι : Type*} (b : Basis ι K U) (i j : ι) :
    k.gramMatrix b i j = k (b i) (b j) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Change of basis: `G' = Mᵀ G M^τ` for `M` the matrix of the new basis in the old one. -/
theorem gramMatrix_eq_mul (b b' : Basis ι K U) :
    k.gramMatrix b' = (b.toMatrix b')ᵀ * k.gramMatrix b * (b.toMatrix b').map (conjRingHom τ) := by
  ext i j
  simp only [gramMatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Basis.toMatrix_apply, conjRingHom_apply]
  conv_lhs => rw [← b.sum_repr (b' i), ← b.sum_repr (b' j)]
  rw [k.map_sum_left]
  simp only [k.map_smul_left, k.map_sum_right, k.map_smul_right, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]
  exact Finset.sum_comm

theorem det_gramMatrix_eq (b b' : Basis ι K U) :
    (k.gramMatrix b').det =
      (b.toMatrix b').det * conj τ (b.toMatrix b').det * (k.gramMatrix b).det := by
  rw [k.gramMatrix_eq_mul b b', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, conjRingHom_apply]
  ring

/-- The Gram matrix of a non-degenerate form is invertible. -/
theorem det_gramMatrix_ne_zero (hk : k.Nondegenerate) (b : Basis ι K U) :
    (k.gramMatrix b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  apply hv
  have hx : ∑ i, v i • b i = 0 := by
    apply hk
    intro y
    rw [← b.sum_repr y, k.map_sum_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [k.map_smul_right, k.map_sum_left]
    have := congrFun hv0 j
    simp only [Matrix.vecMul, dotProduct, gramMatrix_apply, Pi.zero_apply] at this
    simp only [k.map_smul_left]
    rw [this, zero_mul]
  funext i
  exact Fintype.linearIndependent_iff.1 b.linearIndependent v hx i

omit [Fintype ι] [DecidableEq ι] in
/-- `G^τ = ε Gᵀ`. -/
theorem gramMatrix_map_conj (b : Basis ι K U) :
    (k.gramMatrix b).map (conjRingHom τ) = ((ε : ℤ) : K) • (k.gramMatrix b)ᵀ := by
  ext i j
  simp only [Matrix.map_apply, gramMatrix_apply, conjRingHom_apply, k.conj_apply,
    Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]

/-- GKT Lemma 4.34 (second assertion), for commutative `D` (`r = 1`): `det(ρ)^τ = ε^n det(ρ)`. -/
theorem conj_det_gramMatrix (b : Basis ι K U) :
    conj τ (k.gramMatrix b).det = ((ε : ℤ) : K) ^ Fintype.card ι * (k.gramMatrix b).det := by
  rw [← conjRingHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, gramMatrix_map_conj,
    Matrix.det_smul, Matrix.det_transpose]

/-- The determinant of the Gram matrix of a non-degenerate form, as a unit. -/
def detUnit (hk : k.Nondegenerate) (b : Basis ι K U) : Kˣ :=
  Units.mk0 (k.gramMatrix b).det (k.det_gramMatrix_ne_zero hk b)

@[simp] theorem coe_detUnit (hk : k.Nondegenerate) (b : Basis ι K U) :
    (k.detUnit hk b : K) = (k.gramMatrix b).det := rfl

/-! ### The determinant modulo norms -/

/-- The determinant `det(ρ) ∈ E^× / 𝒩_{E/F}(E^×)` of a non-degenerate `ε`-Hermitian space
(GKT (4.12)), computed in `Module.finBasis`; any basis gives the same class (`det_eq_mk`). -/
def det [FiniteDimensional K U] (hk : k.Nondegenerate) : Kˣ ⧸ RingInvo.normSubgroup τ :=
  QuotientGroup.mk (k.detUnit hk (Module.finBasis K U))

omit [Fintype ι] [DecidableEq ι] in
private theorem mk_detUnit_eq_of_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hk : k.Nondegenerate) (b : Basis ι K U) (b' : Basis κ K U) (σ : ι ≃ κ) [Fintype ι]
    [DecidableEq ι] (hb : b' = b.reindex σ) :
    (QuotientGroup.mk (k.detUnit hk b') : Kˣ ⧸ RingInvo.normSubgroup τ) =
      QuotientGroup.mk (k.detUnit hk b) := by
  congr 1
  apply Units.ext
  rw [coe_detUnit, coe_detUnit, hb]
  have : k.gramMatrix (b.reindex σ) = (k.gramMatrix b).submatrix σ.symm σ.symm := by
    ext i j; simp [Basis.reindex_apply]
  rw [this, Matrix.det_submatrix_equiv_self]

/-- Any basis computes `det(ρ)`: the class is independent of the basis (GKT §4.5.1). -/
theorem det_eq_mk [FiniteDimensional K U] (hk : k.Nondegenerate) (b : Basis ι K U) :
    k.det hk = QuotientGroup.mk (k.detUnit hk b) := by
  set b₀ := Module.finBasis K U
  set σ := b.indexEquiv b₀
  rw [det, ← k.mk_detUnit_eq_of_reindex hk b (b.reindex σ) σ rfl]
  set b' := b.reindex σ
  have hM : (b₀.toMatrix b').det ≠ 0 := by
    rw [← Basis.det_apply]; exact b₀.isUnit_det b' |>.ne_zero
  refine (RingInvo.mk_eq_mk_of_coe_eq_mul_norm τ (c := Units.mk0 _ hM) ?_).symm
  rw [coe_detUnit, coe_detUnit, k.det_gramMatrix_eq b₀ b', Units.val_mk0]
  ring

/-- Isometric spaces have the same determinant. -/
theorem IsometryEquiv.det_eq {U' : Type*} [AddCommGroup U'] [Module K U'] [FiniteDimensional K U]
    [FiniteDimensional K U'] {k : EpsilonHermitianForm τ ε U} {k' : EpsilonHermitianForm τ ε U'}
    (φ : IsometryEquiv k k') (hk : k.Nondegenerate) (hk' : k'.Nondegenerate) :
    k.det hk = k'.det hk' := by
  set b := Module.finBasis K U
  rw [k.det_eq_mk hk b, k'.det_eq_mk hk' (b.map φ.toLinearEquiv)]
  congr 1
  apply Units.ext
  rw [coe_detUnit, coe_detUnit]
  congr 1
  ext i j
  simp only [gramMatrix_apply, Basis.map_apply, coe_toLinearEquiv, φ.map_app]

/-! ### Automorphisms in duality (abstract GKT Lemma 4.29) -/

omit [Fintype ι] [DecidableEq ι] in
/-- Automorphisms `f` of `A` and `f'` of `B` preserving a `τ`-sesquilinear pairing `β : A × B → K`
that is non-degenerate on the left, with `dim A = dim B`, satisfy `det f' · (det f)^τ = 1`
(the computation of GKT Lemma 4.29: `det(a^∨) = (det a)^{-τ}`). -/
theorem det_mul_conj_det_eq_one {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B]
    [Module K B] [FiniteDimensional K A] [FiniteDimensional K B]
    (β : A →ₗ[K] B →ₛₗ[conjRingHom τ] K) (hβ : ∀ a, (∀ b, β a b = 0) → a = 0)
    (hd : finrank K A = finrank K B) (f : A →ₗ[K] A) (f' : B →ₗ[K] B)
    (H : ∀ a b, β (f a) (f' b) = β a b) : LinearMap.det f' * conj τ (LinearMap.det f) = 1 := by
  set n := finrank K A
  set bA := Module.finBasisOfFinrankEq K A (rfl : finrank K A = n)
  set bB := Module.finBasisOfFinrankEq K B hd.symm
  set P : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => β (bA i) (bB j)
  have hP : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv
    have hx : ∑ i, v i • bA i = 0 := by
      apply hβ
      intro y
      rw [← bB.sum_repr y, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smulₛₗ, map_sum, LinearMap.sum_apply]
      have := congrFun hv0 j
      simp only [Matrix.vecMul, dotProduct, P, Matrix.of_apply, Pi.zero_apply] at this
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [this, mul_zero]
    funext i
    exact Fintype.linearIndependent_iff.1 bA.linearIndependent v hx i
  set MA := LinearMap.toMatrix bA bA f
  set MB := LinearMap.toMatrix bB bB f'
  have key : P = MAᵀ * P * MB.map (conjRingHom τ) := by
    ext i j
    have e1 : f (bA i) = ∑ m, MA m i • bA m := by
      simp only [MA, LinearMap.toMatrix_apply]; exact (bA.sum_repr _).symm
    have e2 : f' (bB j) = ∑ l, MB l j • bB l := by
      simp only [MB, LinearMap.toMatrix_apply]; exact (bB.sum_repr _).symm
    have e3 : P i j = β (f (bA i)) (f' (bB j)) := (H _ _).symm
    rw [e3, e1, e2]
    simp only [P, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hdet : MA.det * conj τ MB.det = 1 := by
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, conjRingHom_apply] at this
    have h2 : P.det * (MA.det * conj τ MB.det) = P.det * 1 := by
      calc P.det * (MA.det * conj τ MB.det) = MA.det * P.det * conj τ MB.det := by ring
        _ = P.det * 1 := by rw [mul_one]; exact this.symm
    exact mul_left_cancel₀ hP h2
  rw [← LinearMap.det_toMatrix bA, ← LinearMap.det_toMatrix bB]
  have := congrArg (conj τ) hdet
  rw [RingInvo.conj_mul, RingInvo.conj_conj, RingInvo.conj_one] at this
  exact this

end EpsilonHermitianForm

end Langlands
