import Langlands.GroupScheme.Quaternionic.RankOneReducedNorm
import Langlands.GroupScheme.Quaternionic.SymplecticPoints
import Langlands.GroupScheme.Quaternionic.KneserThreeUnits
import Langlands.GroupScheme.Quaternionic.NormOneIsometryAffinePoints
import Langlands.GroupScheme.Quaternionic.QuadraticFormIdentities
import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Langlands.GroupScheme.AffinePoints

/-! # Rotations of a nondegenerate quaternionic line -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Matrices

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (σ : FirstKindInvolution F D) {n : ℕ} (q : σ.QuadraticForms (Fin n)) (x : Fin n → D)
  (R : Type u) [CommRing R] [Algebra F R]

local notation "c" => σ.sesqForm (σ.polar q) x x
local notation "ι" => (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D)

/-- The column `P σ(x)` of the polar Gram matrix `P` applied to `σ(x)`, over `R ⊗ D`. -/
def lineColumn : Fin n → R ⊗[F] D := fun i => ι ((σ.polar q *ᵥ (σ ∘ x)) i)

/-- The row `c⁻¹ (1 - t) x` over `R ⊗ D`, where `c = h(x, x)`. -/
def lineRow (t : R ⊗[F] D) : Fin n → R ⊗[F] D := fun j => ι c⁻¹ * (1 - t) * ι (x j)

/-- The matrix of `v ↦ v - h(v, x) c⁻¹ (1 - t) x` on row vectors over `R ⊗ D`. When `c ≠ 0`,
it acts by `a x ↦ a t x` on the line and fixes the orthogonal complement. -/
def lineRotationMatrix (t : R ⊗[F] D) : Matrix (Fin n) (Fin n) (R ⊗[F] D) :=
  1 - vecMulVec (σ.lineColumn q x R) (σ.lineRow q x R t)

theorem lineRow_dotProduct_lineColumn (t : R ⊗[F] D) :
    σ.lineRow q x R t ⬝ᵥ σ.lineColumn q x R = ι c⁻¹ * (1 - t) * ι c := by
  have h : ∑ j, ι (x j) * ι ((σ.polar q *ᵥ (σ ∘ x)) j) = ι c := by
    rw [σ.sesqForm_eq_dotProduct, dotProduct, _root_.map_sum]
    simp only [_root_.map_mul]
  simp only [dotProduct, lineRow, lineColumn, mul_assoc, ← Finset.mul_sum, h]

theorem vecMulVec_mul_vecMulVec' {m : Type*} [Fintype m] {A : Type*} [Ring A] (a b c' d : m → A) :
    vecMulVec a b * vecMulVec c' d = vecMulVec a ((b ⬝ᵥ c') • d) := by
  ext i k
  simp only [mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]

theorem lineRotationMatrix_mul (hc : c ≠ 0) (s t : R ⊗[F] D) :
    σ.lineRotationMatrix q x R s * σ.lineRotationMatrix q x R t =
      σ.lineRotationMatrix q x R (s * t) := by
  have hcc : ι c * ι c⁻¹ = 1 := by rw [← _root_.map_mul, mul_inv_cancel₀ hc, _root_.map_one]
  have hrow : σ.lineRow q x R s + σ.lineRow q x R t -
      (σ.lineRow q x R s ⬝ᵥ σ.lineColumn q x R) • σ.lineRow q x R t =
        σ.lineRow q x R (s * t) := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      lineRow_dotProduct_lineColumn, lineRow]
    have e : ι c⁻¹ * (1 - s) * ι c * (ι c⁻¹ * (1 - t) * ι (x j)) =
        ι c⁻¹ * (1 - s) * (1 - t) * ι (x j) := by
      rw [show ι c⁻¹ * (1 - s) * ι c * (ι c⁻¹ * (1 - t) * ι (x j)) =
        ι c⁻¹ * (1 - s) * (ι c * ι c⁻¹) * (1 - t) * ι (x j) by noncomm_ring, hcc, mul_one]
    rw [e]
    noncomm_ring
  simp only [lineRotationMatrix, sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec']
  rw [← hrow]
  ext i k
  simp only [Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub]
  abel

theorem lineRotationMatrix_one : σ.lineRotationMatrix q x R 1 = 1 := by
  ext i j
  simp [lineRotationMatrix, lineRow, vecMulVec_apply]

theorem vecMulVec_mul' {m : Type*} [Fintype m] {A : Type*} [Ring A] (a b : m → A)
    (P : Matrix m m A) : vecMulVec a b * P = vecMulVec a (b ᵥ* P) := by
  ext i k
  simp only [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem mul_vecMulVec' {m : Type*} [Fintype m] {A : Type*} [Ring A] (a b : m → A)
    (P : Matrix m m A) : P * vecMulVec a b = vecMulVec (P *ᵥ a) b := by
  ext i k
  simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem baseChange_includeRight (y : D) : σ.baseChange R (ι y) = ι (σ y) := by
  simp only [Algebra.TensorProduct.includeRight_apply, baseChange_tmul]

theorem map_sesqForm_polar_self_inv : σ c⁻¹ = c⁻¹ := by
  have hσc : σ c = c := σ.sesqForm_polar_swap q x x
  rcases eq_or_ne c 0 with h | h
  · rw [h, _root_.inv_zero, FirstKindInvolution.map_zero]
  · apply eq_inv_of_mul_eq_one_left
    calc σ c⁻¹ * c = σ c⁻¹ * σ c := by rw [hσc]
      _ = σ (c * c⁻¹) := (FirstKindInvolution.map_mul σ c c⁻¹).symm
      _ = 1 := by rw [mul_inv_cancel₀ h, FirstKindInvolution.map_one]

/-- For `c ≠ 0`, the rotation preserves the polar Gram matrix when `t` satisfies
`t c σ(t) = c` over the coefficient algebra. -/
theorem lineRotationMatrix_polar (hc : c ≠ 0) (t : R ⊗[F] D)
    (ht : t * ι c * σ.baseChange R t = ι c) :
    σ.lineRotationMatrix q x R t * (σ.polar q).map ι *
        (σ.baseChange R).matrix (Fin n) (σ.lineRotationMatrix q x R t) =
      (σ.polar q).map ι := by
  set σR := σ.baseChange R with hσR
  set a := σ.lineColumn q x R with ha
  set b := σ.lineRow q x R t with hb
  set Pm := (σ.polar q).map ι with hPm
  set u := ι c with hu
  set v := ι c⁻¹ with hv
  set r : Fin n → R ⊗[F] D := fun k => ι ((x ᵥ* σ.polar q) k) with hr
  have huv : u * v = 1 := by rw [hu, hv, ← _root_.map_mul, mul_inv_cancel₀ hc, _root_.map_one]
  have hvu : v * u = 1 := by rw [hu, hv, ← _root_.map_mul, inv_mul_cancel₀ hc, _root_.map_one]
  have hσv : σR v = v := by rw [hv, baseChange_includeRight, map_sesqForm_polar_self_inv]
  have hPσx : σ ∘ (x ᵥ* σ.polar q) = σ.polar q *ᵥ (σ ∘ x) := by
    rw [σ.map_vecMul, σ.matrix_polar]
  have hra : σR ∘ a = r := by
    funext k
    change σR (ι ((σ.polar q *ᵥ (σ ∘ x)) k)) = ι ((x ᵥ* σ.polar q) k)
    rw [baseChange_includeRight, ← hPσx, Function.comp_apply, FirstKindInvolution.apply_apply]
  have hσb : σR ∘ b = fun i => ι (σ (x i)) * ((1 - σR t) * v) := by
    funext i
    change σR (v * (1 - t) * ι (x i)) = _
    rw [FirstKindInvolution.map_mul, FirstKindInvolution.map_mul, hσv, baseChange_includeRight,
      FirstKindInvolution.map_sub, FirstKindInvolution.map_one]
  have hA : σR.matrix (Fin n) (vecMulVec a b) = vecMulVec (σR ∘ b) (σR ∘ a) := by
    ext i k
    simp only [matrix_apply, vecMulVec_apply, Function.comp_apply, FirstKindInvolution.map_mul]
  have hbP : b ᵥ* Pm = fun k => v * (1 - t) * r k := by
    funext k
    simp only [vecMul, dotProduct, hb, lineRow, hPm, Matrix.map_apply, hr, mul_assoc,
      ← Finset.mul_sum, ← _root_.map_mul, ← _root_.map_sum]
    rfl
  have hPb : Pm *ᵥ (σR ∘ b) = fun i => a i * ((1 - σR t) * v) := by
    rw [hσb]
    funext i
    simp only [mulVec, dotProduct, hPm, Matrix.map_apply, ha, lineColumn, ← mul_assoc,
      ← Finset.sum_mul, ← _root_.map_mul, ← _root_.map_sum, Function.comp_apply]
  have hbPb : b ⬝ᵥ (Pm *ᵥ (σR ∘ b)) = v * (1 - t) * u * ((1 - σR t) * v) := by
    rw [hPb]
    have h := σ.lineRow_dotProduct_lineColumn q x R t
    simp only [dotProduct] at h ⊢
    simp only [← mul_assoc, ← Finset.sum_mul]
    rw [show (∑ i, b i * a i) = v * (1 - t) * u from h]
  have hX : v * (1 - t) + (1 - σR t) * v - v * (1 - t) * u * ((1 - σR t) * v) = 0 := by
    have e1 : v * (1 - t) * u * ((1 - σR t) * v) =
        (v * u) * v - (v * u) * (σR t * v) - v * t * (u * v) + v * (t * u * σR t) * v := by
      noncomm_ring
    rw [e1, hvu, huv, ht, hvu]
    noncomm_ring
  simp only [lineRotationMatrix, FirstKindInvolution.map_sub, FirstKindInvolution.map_one]
  change (1 - vecMulVec a b) * Pm * (1 - σR.matrix (Fin n) (vecMulVec a b)) = Pm
  rw [hA, hra]
  have expand : (1 - vecMulVec a b) * Pm * (1 - vecMulVec (σR ∘ b) r) =
      Pm - vecMulVec a b * Pm - Pm * vecMulVec (σR ∘ b) r +
        vecMulVec a b * (Pm * vecMulVec (σR ∘ b) r) := by
    noncomm_ring
  rw [expand, vecMulVec_mul' a b Pm, hbP, mul_vecMulVec' (σR ∘ b) r Pm,
    vecMulVec_mul_vecMulVec' a b (Pm *ᵥ (σR ∘ b)) r, hbPb, hPb]
  ext i k
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply, vecMulVec_apply, vecMulVec_apply,
    vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have : a i * (v * (1 - t) * r k) + a i * ((1 - σR t) * v) * r k -
      a i * (v * (1 - t) * u * ((1 - σR t) * v) * r k) =
        a i * (v * (1 - t) + (1 - σR t) * v - v * (1 - t) * u * ((1 - σR t) * v)) * r k := by
    noncomm_ring
  rw [hX, mul_zero, zero_mul] at this
  rw [← sub_eq_zero, show ∀ p A B C : R ⊗[F] D, p - A - B + C - p = -(A + B - C) from
    fun p A B C => by abel, this, neg_zero]

/-- For a nondegenerate line, the reduced norm of the rotation matrix is the reduced norm
of its parameter `t`. -/
theorem matrixReducedNorm_lineRotationMatrix [FiniteDimensional F D] [Algebra.IsCentral F D]
    [NeZero n] (hc : c ≠ 0) (t : R ⊗[F] D) :
    matrixReducedNorm R (σ.lineRotationMatrix q x R t) = CentralSimple.reducedNorm F D R t := by
  have huv : ι c * ι c⁻¹ = 1 := by rw [← _root_.map_mul, mul_inv_cancel₀ hc, _root_.map_one]
  have hvu : ι c⁻¹ * ι c = 1 := by rw [← _root_.map_mul, inv_mul_cancel₀ hc, _root_.map_one]
  rw [lineRotationMatrix, matrixReducedNorm_one_sub_vecMulVec, lineRow_dotProduct_lineColumn]
  have e : 1 - ι c⁻¹ * (1 - t) * ι c = ι c⁻¹ * t * ι c := by
    rw [show ι c⁻¹ * (1 - t) * ι c = ι c⁻¹ * ι c - ι c⁻¹ * t * ι c by noncomm_ring, hvu]
    abel
  rw [e, _root_.map_mul, _root_.map_mul, mul_comm (CentralSimple.reducedNorm F D R (ι c⁻¹)),
    mul_assoc, ← _root_.map_mul, hvu, _root_.map_one, mul_one]

/-- Coefficient changes act on the entries. -/
theorem map_lineRotationMatrix {S : Type u} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (t : R ⊗[F] D) :
    (σ.lineRotationMatrix q x R t).map (Algebra.TensorProduct.map f (AlgHom.id F D)) =
      σ.lineRotationMatrix q x S (Algebra.TensorProduct.map f (AlgHom.id F D) t) := by
  ext i j
  simp only [lineRotationMatrix, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    vecMulVec_apply, lineRow, lineColumn, _root_.map_sub, _root_.map_mul,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, _root_.map_one,
    AlgHom.id_apply]
  split_ifs <;> simp

/-- The matrix of `v ↦ v - 2 h(v, x) c⁻¹ x`. When `c ≠ 0`, it negates `D x` and fixes its
orthogonal complement. -/
def lineReflection : Matrix (Fin n) (Fin n) D :=
  1 - vecMulVec (σ.polar q *ᵥ (σ ∘ x)) (fun j => c⁻¹ * 2 * x j)

theorem map_lineReflection :
    (σ.lineReflection q x).map ι = σ.lineRotationMatrix q x R (-1) := by
  ext i j
  simp only [lineReflection, lineRotationMatrix, Matrix.map_apply, Matrix.sub_apply,
    Matrix.one_apply, vecMulVec_apply, lineRow, lineColumn, sub_neg_eq_add]
  rw [show (1 : R ⊗[F] D) + 1 = ι 2 by rw [_root_.map_ofNat, one_add_one_eq_two]]
  simp only [← _root_.map_mul]
  split_ifs <;> simp only [_root_.map_sub, _root_.map_one, _root_.map_zero]

/-- The line negation differs from the identity over any extension field of a characteristic-zero
ground field, provided `c ≠ 0`. -/
theorem lineRotationMatrix_neg_one_ne_one [CharZero F] {K : Type u} [Field K] [Algebra F K]
    (hc : c ≠ 0) : σ.lineRotationMatrix q x K (-1) ≠ 1 := by
  intro h
  have hV : vecMulVec (σ.lineColumn q x K) (σ.lineRow q x K (-1)) = 0 := by
    have h' := congrArg (fun M => 1 - M) h
    simpa [lineRotationMatrix] using h'
  have hι : Function.Injective (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hsum : ∑ i, (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) (x i) *
      σ.lineColumn q x K i = (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) c := by
    rw [σ.sesqForm_eq_dotProduct, dotProduct, _root_.map_sum]
    simp only [lineColumn, _root_.map_mul]
  have hx : x = 0 := by
    funext j
    have hij : ∀ i, σ.lineColumn q x K i * σ.lineRow q x K (-1) j = 0 := fun i => by
      have h0 := congrFun (congrFun hV i) j
      rwa [vecMulVec_apply, Matrix.zero_apply] at h0
    have h1 : ∑ i, (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) (x i) *
        (σ.lineColumn q x K i * σ.lineRow q x K (-1) j) = 0 := by
      simp only [hij, mul_zero, Finset.sum_const_zero]
    simp only [← mul_assoc, ← Finset.sum_mul, hsum, lineRow, sub_neg_eq_add] at h1
    rw [show (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) c *
        (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) c⁻¹ * (1 + 1) *
          (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) (x j) =
        (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) (c * c⁻¹ * 2 * x j) by
      rw [_root_.map_mul, _root_.map_mul, _root_.map_mul, _root_.map_ofNat, one_add_one_eq_two],
      mul_inv_cancel₀ hc, one_mul] at h1
    have h2 : (2 : D) * x j = 0 := hι (by rw [h1, _root_.map_zero])
    have h2D : (2 : D) ≠ 0 := by
      rw [← _root_.map_ofNat (algebraMap F D) 2]
      exact (map_ne_zero_iff _ (algebraMap F D).injective).mpr two_ne_zero
    exact (mul_eq_zero.mp h2).resolve_left h2D
  apply hc
  simp [hx, sesqForm]

end Matrices

section Points

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) {n : ℕ} [NeZero n] (q : σ.QuadraticForms (Fin n))
  (x : Fin n → D) (R : Type u) [CommRing R] [Algebra F R]

local notation "c" => σ.sesqForm (σ.polar q) x x
local notation "ι" => (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D)
local notation "Rₐ" => (CommAlgCat.of F R : CommAlgCat (CommRingCat.of F))

omit [CharZero F] [NeZero n] in
/-- The subgroup of units `t` of `R ⊗ D` with `t c σ(t) = c` and reduced norm one. When `c ≠ 0`,
these parameters give reduced-norm-one rotations of the line `D x`. -/
def lineTorus : Subgroup (R ⊗[F] D)ˣ where
  carrier := {t | (t : R ⊗[F] D) * ι c * σ.baseChange R t = ι c ∧
    CentralSimple.reducedNorm F D R t = 1}
  mul_mem' {s t} hs ht := by
    refine ⟨?_, ?_⟩
    · change (s : R ⊗[F] D) * t * ι c * σ.baseChange R (s * t) = ι c
      rw [FirstKindInvolution.map_mul, show (s : R ⊗[F] D) * t * ι c *
        (σ.baseChange R t * σ.baseChange R s) =
          s * (t * ι c * σ.baseChange R t) * σ.baseChange R s by noncomm_ring, ht.1, hs.1]
    · change CentralSimple.reducedNorm F D R ((s : R ⊗[F] D) * t) = 1
      rw [_root_.map_mul, hs.2, ht.2, one_mul]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · change (1 : R ⊗[F] D) * ι c * σ.baseChange R 1 = ι c
      rw [FirstKindInvolution.map_one, one_mul, mul_one]
    · exact _root_.map_one _
  inv_mem' {t} ht := by
    have hσ : σ.baseChange R (t : R ⊗[F] D) * σ.baseChange R (↑t⁻¹ : R ⊗[F] D) = 1 := by
      rw [← FirstKindInvolution.map_mul, Units.inv_mul, FirstKindInvolution.map_one]
    refine ⟨?_, ?_⟩
    · change (↑t⁻¹ : R ⊗[F] D) * ι c * σ.baseChange R (↑t⁻¹ : R ⊗[F] D) = ι c
      calc (↑t⁻¹ : R ⊗[F] D) * ι c * σ.baseChange R (↑t⁻¹ : R ⊗[F] D) =
            ↑t⁻¹ * ((t : R ⊗[F] D) * ι c * σ.baseChange R t) *
              σ.baseChange R (↑t⁻¹ : R ⊗[F] D) := by rw [ht.1]
        _ = ι c * (σ.baseChange R (t : R ⊗[F] D) * σ.baseChange R (↑t⁻¹ : R ⊗[F] D)) := by
            simp only [← mul_assoc, Units.inv_mul, one_mul]
        _ = ι c := by rw [hσ, mul_one]
    · change CentralSimple.reducedNorm F D R (↑t⁻¹ : R ⊗[F] D) = 1
      have h := congrArg (CentralSimple.reducedNorm F D R) (Units.inv_mul t)
      rw [_root_.map_mul, ht.2, mul_one, _root_.map_one] at h
      exact h

omit [CharZero F] [NeZero n] in
theorem mem_lineTorus_iff {R : Type u} [CommRing R] [Algebra F R] (t : (R ⊗[F] D)ˣ) :
    t ∈ σ.lineTorus q x R ↔
      (t : R ⊗[F] D) * (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D) c *
          σ.baseChange R t = (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D) c ∧
        CentralSimple.reducedNorm F D R t = 1 :=
  Iff.rfl

omit [CharZero F] [FiniteDimensional F D] [Algebra.IsCentral F D] [NeZero n] in
private theorem polar_eq_out_add' :
    σ.polar q = Quotient.out q + σ.matrix (Fin n) (Quotient.out q) := by
  have h := σ.polar_mk (Quotient.out q)
  rw [Submodule.Quotient.mk_out] at h
  exact h

variable (hc : σ.sesqForm (σ.polar q) x x ≠ 0)

omit [CharZero F] [NeZero n] in
/-- The rotation of the line in tensor coordinates, as a unit. -/
def lineRotationUnit (t : (R ⊗[F] D)ˣ) : (R ⊗[F] Matrix (Fin n) (Fin n) D)ˣ where
  val := (coefficientEquiv F D R).symm (σ.lineRotationMatrix q x R t)
  inv := (coefficientEquiv F D R).symm (σ.lineRotationMatrix q x R ↑t⁻¹)
  val_inv := by
    rw [← _root_.map_mul, lineRotationMatrix_mul σ q x R hc, Units.mul_inv,
      lineRotationMatrix_one, _root_.map_one]
  inv_val := by
    rw [← _root_.map_mul, lineRotationMatrix_mul σ q x R hc, Units.inv_mul,
      lineRotationMatrix_one, _root_.map_one]

omit [CharZero F] [NeZero n] [FiniteDimensional F D] [Algebra.IsCentral F D] in
theorem coefficientEquiv_lineRotationUnit (t : (R ⊗[F] D)ˣ) :
    coefficientEquiv F D R (σ.lineRotationUnit q x R hc t : R ⊗[F] Matrix (Fin n) (Fin n) D) =
      σ.lineRotationMatrix q x R t := by
  change coefficientEquiv F D R ((coefficientEquiv F D R).symm (σ.lineRotationMatrix q x R t)) = _
  exact (coefficientEquiv F D R).apply_symm_apply _

omit [CharZero F] [NeZero n] [FiniteDimensional F D] [Algebra.IsCentral F D] in
theorem lineRotationUnit_mul (s t : (R ⊗[F] D)ˣ) :
    σ.lineRotationUnit q x R hc (s * t) =
      σ.lineRotationUnit q x R hc s * σ.lineRotationUnit q x R hc t := by
  apply Units.ext
  apply (coefficientEquiv (m := Fin n) F D R).injective
  rw [Units.val_mul, _root_.map_mul, coefficientEquiv_lineRotationUnit,
    coefficientEquiv_lineRotationUnit, coefficientEquiv_lineRotationUnit, Units.val_mul,
    lineRotationMatrix_mul σ q x R hc]

omit [NeZero n] in
theorem lineRotationUnit_mem_isometry (t : σ.lineTorus q x R) :
    σ.lineRotationUnit q x R hc (t : (R ⊗[F] D)ˣ) ∈ σ.tensorIsometryGroup q R := by
  set Θ := (σ.matrix (Fin n)).baseChange R
  set U : R ⊗[F] Matrix (Fin n) (Fin n) D :=
    (σ.lineRotationUnit q x R hc (t : (R ⊗[F] D)ˣ) : R ⊗[F] Matrix (Fin n) (Fin n) D) with hU
  have hP : (1 : R) ⊗ₜ[F] Quotient.out q + Θ ((1 : R) ⊗ₜ[F] Quotient.out q) =
      (1 : R) ⊗ₜ[F] σ.polar q := by
    have h1 : Θ ((1 : R) ⊗ₜ[F] Quotient.out q) =
        (1 : R) ⊗ₜ[F] σ.matrix (Fin n) (Quotient.out q) :=
      (σ.matrix (Fin n)).baseChange_tmul (1 : R) _
    rw [h1, ← TensorProduct.tmul_add, ← polar_eq_out_add' σ q]
  have hpol : U * ((1 : R) ⊗ₜ[F] Quotient.out q + Θ ((1 : R) ⊗ₜ[F] Quotient.out q)) * Θ U =
      (1 : R) ⊗ₜ[F] Quotient.out q + Θ ((1 : R) ⊗ₜ[F] Quotient.out q) := by
    rw [hP]
    apply (coefficientEquiv (m := Fin n) F D R).injective
    rw [_root_.map_mul, _root_.map_mul, coefficientEquiv_matrix_baseChange, hU,
      coefficientEquiv_lineRotationUnit, coefficientEquiv_one_tmul_eq_map]
    exact σ.lineRotationMatrix_polar q x R hc _ t.2.1
  have hh : (2 : R) * algebraMap F R ((2 : F)⁻¹) = 1 := by
    rw [← _root_.map_ofNat (algebraMap F R) 2, ← _root_.map_mul, mul_inv_cancel₀ two_ne_zero,
      _root_.map_one]
  have hd := KneserThree.defect_mem_of_polar Θ hh hpol
  change IsometryCut.defect (σ.matrix (Fin n)) (Quotient.out q) U ∈
    ((σ.matrix (Fin n)).alternatingSubspace).baseChange R
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem]
  exact hd

omit [CharZero F] in
theorem reducedNorm_lineRotationUnit (t : σ.lineTorus q x R) :
    CentralSimple.reducedNorm F (Matrix (Fin n) (Fin n) D) R
      (σ.lineRotationUnit q x R hc (t : (R ⊗[F] D)ˣ) : R ⊗[F] Matrix (Fin n) (Fin n) D) = 1 := by
  have h := σ.matrixReducedNorm_lineRotationMatrix q x R hc
    (((t : (R ⊗[F] D)ˣ)) : R ⊗[F] D)
  rw [t.2.2] at h
  exact h

/-- The rotations of the line as points of the tensor norm-one isometry group. -/
def lineRotationTensorHom : σ.lineTorus q x R →* σ.tensorNormOneIsometryGroup q R where
  toFun t := ⟨⟨σ.lineRotationUnit q x R hc t, σ.lineRotationUnit_mem_isometry q x R hc t⟩, by
    change CentralSimple.reducedNormUnits F (Matrix (Fin n) (Fin n) D) R _ = 1
    apply Units.ext
    rw [CentralSimple.reducedNormUnits_val, Units.val_one]
    exact σ.reducedNorm_lineRotationUnit q x R hc t⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    apply Units.ext
    apply (coefficientEquiv (m := Fin n) F D R).injective
    change coefficientEquiv F D R (σ.lineRotationUnit q x R hc 1 :
      R ⊗[F] Matrix (Fin n) (Fin n) D) =
        coefficientEquiv (m := Fin n) F D R (1 : R ⊗[F] Matrix (Fin n) (Fin n) D)
    rw [coefficientEquiv_lineRotationUnit, Units.val_one, _root_.map_one,
      lineRotationMatrix_one]
  map_mul' s t := by
    apply Subtype.ext; apply Subtype.ext
    exact σ.lineRotationUnit_mul q x R hc s t

/-- The rotations of the line as affine points of the reduced-norm-one isometry group. -/
def lineRotationHom : σ.lineTorus q x R →* (σ.normOneIsometryGroup q).affinePoints Rₐ :=
  (σ.normOneIsometryAffinePointsEquiv q Rₐ).symm.toMonoidHom.comp
    (σ.lineRotationTensorHom q x R hc)

theorem lineRotationHom_val (t : σ.lineTorus q x R) :
    ((σ.normOneIsometryAffinePointsEquiv q Rₐ (σ.lineRotationHom q x R hc t)).val.val :
        (R ⊗[F] Matrix (Fin n) (Fin n) D)ˣ) = σ.lineRotationUnit q x R hc t := by
  change ((σ.normOneIsometryAffinePointsEquiv q Rₐ
    ((σ.normOneIsometryAffinePointsEquiv q Rₐ).symm _)).val.val : _) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

omit [CharZero F] [NeZero n] in
variable {R} in
/-- Coefficient change on the rotations of the line. -/
def lineTorusMap {S : Type u} [CommRing S] [Algebra F S] (f : R →ₐ[F] S) :
    σ.lineTorus q x R →* σ.lineTorus q x S where
  toFun t := ⟨Units.map (Algebra.TensorProduct.map f (AlgHom.id F D)).toMonoidHom t, by
    refine ⟨?_, ?_⟩
    · change Algebra.TensorProduct.map f (AlgHom.id F D) ((t : (R ⊗[F] D)ˣ) : R ⊗[F] D) *
          (Algebra.TensorProduct.includeRight : D →ₐ[F] S ⊗[F] D) c *
          σ.baseChange S (Algebra.TensorProduct.map f (AlgHom.id F D) ((t : (R ⊗[F] D)ˣ) : R ⊗[F] D)) =
        (Algebra.TensorProduct.includeRight : D →ₐ[F] S ⊗[F] D) c
      have hι : (Algebra.TensorProduct.includeRight : D →ₐ[F] S ⊗[F] D) c =
          Algebra.TensorProduct.map f (AlgHom.id F D)
            ((Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D) c) := by
        simp
      rw [← σ.map_baseChange f, hι, ← _root_.map_mul, ← _root_.map_mul, t.2.1]
    · change CentralSimple.reducedNorm F D S
          (Algebra.TensorProduct.map f (AlgHom.id F D) ((t : (R ⊗[F] D)ˣ) : R ⊗[F] D)) = 1
      rw [CentralSimple.reducedNorm_naturality, t.2.2, _root_.map_one]⟩
  map_one' := Subtype.ext (_root_.map_one _)
  map_mul' s t := Subtype.ext (_root_.map_mul _ _ _)

omit [CharZero F] [NeZero n] in
variable {R} in
@[simp] theorem coe_lineTorusMap {S : Type u} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (t : σ.lineTorus q x R) :
    ((σ.lineTorusMap q x f t : (S ⊗[F] D)ˣ) : S ⊗[F] D) =
      Algebra.TensorProduct.map f (AlgHom.id F D) ((t : (R ⊗[F] D)ˣ) : R ⊗[F] D) :=
  rfl

variable {R} in
/-- The rotations of the line commute with coefficient changes. -/
theorem lineRotationHom_naturality {S : Type u} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (t : σ.lineTorus q x R) :
    (σ.normOneIsometryGroup q).affinePointMap (CommAlgCat.ofHom f) (σ.lineRotationHom q x R hc t) =
      σ.lineRotationHom q x S hc (σ.lineTorusMap q x f t) := by
  apply (σ.normOneIsometryAffinePointsEquiv q
    (CommAlgCat.of F S : CommAlgCat (CommRingCat.of F))).injective
  apply Subtype.ext
  apply Subtype.ext
  rw [lineRotationHom_val]
  rw [σ.normOneIsometryAffinePointsEquiv_val q, GroupScheme.affinePointMap_apply, Category.assoc,
    FiniteAlgebraUnits.affinePointsEquiv_naturality, ← σ.normOneIsometryAffinePointsEquiv_val q,
    lineRotationHom_val]
  apply Units.ext
  apply (coefficientEquiv (m := Fin n) F D S).injective
  rw [Units.coe_map, coefficientEquiv_lineRotationUnit]
  change coefficientEquiv F D S (Algebra.TensorProduct.map f
    (AlgHom.id F (Matrix (Fin n) (Fin n) D))
      (σ.lineRotationUnit q x R hc (t : (R ⊗[F] D)ˣ) : R ⊗[F] Matrix (Fin n) (Fin n) D)) = _
  rw [coefficientEquiv_naturality, coefficientEquiv_lineRotationUnit, map_lineRotationMatrix,
    coe_lineTorusMap]

end Points

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
