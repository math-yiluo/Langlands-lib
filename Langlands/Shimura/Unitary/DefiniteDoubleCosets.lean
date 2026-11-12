import Langlands.LinearAlgebra.HermiteReduction
import Langlands.Global.RationalAdelicLattice
import Langlands.Shimura.Unitary.DefiniteTraceForm
import Langlands.Shimura.EquivariantFormsDoubleCoset

/-!
# Finiteness of definite double cosets for lattice stabilizers

Let `σ` be an involution of a finite-dimensional `ℚ`-algebra `A` whose real scalar extension is
positive, `GJ` its similitude group and `b` a `ℚ`-basis of `A`. The lattice level `K₀` is the
stabilizer in `GJ(𝔸_f)` of the lattice `⊕ Ẑ (1 ⊗ b_i)` with multiplier in `Ẑ^×`. This module
proves that `GJ(ℚ) \ GJ(𝔸_f) / K₀` is finite (`finite_doubleCosets_latticeLevel`).

For a point `g = (x, c)` with left multiplication matrix `X`, class number one of `ℚ` gives
`X = B W` with `B` rational and `W, W⁻¹` integral, and `c = r u` with `r > 0` rational and `u` a
unit of `Ẑ` (`IsReduction`). The integer matrix `S = (N / r) Bᵀ G B` (`G` the Gram matrix of the
trace form) is positive definite with determinant at most `|det (N G)|`, so after Hermite
reduction its entries are bounded. The integer matrices `N' B⁻¹ R_k B` (`R_k` the right
multiplication matrices) then have columns of bounded `S`-length, so all these data lie in a
finite set. Equal data give the same double coset (`mk_eq_of_isReduction`): `Γ = B' B⁻¹` commutes
with all `R_k`, hence is left multiplication by some `γ ∈ A`, and `Γᵀ G Γ = (r' / r) G` forces
`σ(γ) γ = r' / r`.
-/

noncomputable section

open scoped TensorProduct Matrix
open Module Matrix

namespace Langlands.Shimura

namespace DefiniteDoubleCosets

/-! ### Integer quadratic forms -/

section Integer

variable {n : ℕ}

theorem isSymm_toBilin' {S : Matrix (Fin n) (Fin n) ℤ} (hS : Sᵀ = S) :
    (Matrix.toBilin' S).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hS, dotProduct_comm]

theorem isPosDef_toBilin' {S : Matrix (Fin n) (Fin n) ℤ}
    (hpos : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ S *ᵥ v) :
    LinearAlgebra.Hermite.IsPosDef (Matrix.toBilin' S) := fun v hv => by
  rw [Matrix.toBilin'_apply']
  exact hpos v hv

/-- A positive definite integer quadratic form takes values at most `T` at finitely many
vectors. -/
theorem finite_setOf_dotProduct_mulVec_le {S : Matrix (Fin n) (Fin n) ℤ} (hS : Sᵀ = S)
    (hpos : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ S *ᵥ v) (T : ℤ) :
    {v : Fin n → ℤ | v ⬝ᵥ S *ᵥ v ≤ T}.Finite := by
  classical
  have hs := isSymm_toBilin' hS
  have hβ := isPosDef_toBilin' hpos
  have hd : 0 < S.det := by
    have h := LinearAlgebra.Hermite.det_pos (Pi.basisFun ℤ (Fin n)) hs hβ
    rwa [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h
  have hadjT : (adjugate S)ᵀ = adjugate S := by rw [adjugate_transpose, hS]
  refine (Set.Finite.pi (t := fun i => Set.Icc (-(|T| * |adjugate S i i|))
      (|T| * |adjugate S i i|)) fun i => Set.finite_Icc _ _).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  set y : Fin n → ℤ := adjugate S *ᵥ Pi.single i 1
  have hxy : v ⬝ᵥ S *ᵥ y = S.det * v i := by
    rw [Matrix.mulVec_mulVec, mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
  have hyy : y ⬝ᵥ S *ᵥ y = S.det * adjugate S i i := by
    rw [Matrix.mulVec_mulVec, mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
    simp [y]
  have hcs := LinearAlgebra.Hermite.sq_le_mul hs hβ v y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.toBilin'_apply', hxy, hyy] at hcs
  have hvv : 0 ≤ v ⬝ᵥ S *ᵥ v := by
    have := hβ.nonneg v
    rwa [Matrix.toBilin'_apply'] at this
  have hyy0 : 0 ≤ S.det * adjugate S i i := by
    have := hβ.nonneg y
    rwa [Matrix.toBilin'_apply', hyy] at this
  have hadj : 0 ≤ adjugate S i i := by
    by_contra h
    have h' := not_le.1 h
    nlinarith
  have key : v i ^ 2 ≤ T * adjugate S i i := by
    have h1 : S.det * (S.det * v i ^ 2) ≤ S.det * (v ⬝ᵥ S *ᵥ v * adjugate S i i) := by
      have e1 : (S.det * v i) ^ 2 = S.det * (S.det * v i ^ 2) := by ring
      have e2 : v ⬝ᵥ S *ᵥ v * (S.det * adjugate S i i) =
          S.det * (v ⬝ᵥ S *ᵥ v * adjugate S i i) := by ring
      linarith
    have h2 : S.det * v i ^ 2 ≤ v ⬝ᵥ S *ᵥ v * adjugate S i i := le_of_mul_le_mul_left h1 hd
    have h3 : v i ^ 2 ≤ S.det * v i ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hd
    have h5 : v ⬝ᵥ S *ᵥ v * adjugate S i i ≤ T * adjugate S i i :=
      mul_le_mul_of_nonneg_right hv hadj
    linarith
  have hvi : |v i| ≤ |T| * |adjugate S i i| := by
    have h4 : |v i| ≤ v i ^ 2 := by
      rcases eq_or_ne (v i) 0 with h | h
      · simp [h]
      · rw [← sq_abs]
        nlinarith [Int.one_le_abs h]
    calc |v i| ≤ v i ^ 2 := h4
      _ ≤ T * adjugate S i i := key
      _ ≤ |T * adjugate S i i| := le_abs_self _
      _ = |T| * |adjugate S i i| := abs_mul _ _
  exact abs_le.1 hvi

/-- **Hermite reduction in matrix form.** For every `n` and `Δ` there is `C` such that every
positive definite symmetric integer matrix `S` with `det S ≤ Δ` has an integrally equivalent
form `Pᵀ S P`, `P ∈ GL_n(ℤ)`, with entries bounded by `C`. -/
theorem exists_reduced_matrix (n : ℕ) (Δ : ℤ) : ∃ C : ℤ, ∀ S : Matrix (Fin n) (Fin n) ℤ,
    Sᵀ = S → (∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ S *ᵥ v) → S.det ≤ Δ →
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, P * Q = 1 ∧ Q * P = 1 ∧
      ∀ i j, |(Pᵀ * S * P) i j| ≤ C := by
  classical
  obtain ⟨C, hC⟩ := LinearAlgebra.Hermite.exists_reduced_basis.{0} n Δ
  refine ⟨C, fun S hS hpos hdet => ?_⟩
  have hdet' : (LinearMap.BilinForm.toMatrix (Pi.basisFun ℤ (Fin n)) (Matrix.toBilin' S)).det
      ≤ Δ := by
    rwa [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']
  obtain ⟨c, hc⟩ := hC (Fin n → ℤ) (Pi.basisFun ℤ (Fin n)) (Matrix.toBilin' S)
    (isSymm_toBilin' hS) (isPosDef_toBilin' hpos) hdet'
  refine ⟨(Pi.basisFun ℤ (Fin n)).toMatrix c, c.toMatrix (Pi.basisFun ℤ (Fin n)),
    Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _, fun i j => ?_⟩
  have h := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun ℤ (Fin n)) c
    (Matrix.toBilin' S)
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h
  rw [h, LinearMap.BilinForm.toMatrix_apply]
  exact hc i j

end Integer

/-! ### Lattice stabilizers -/

section Lattice

local notation "𝔸f" => Langlands.Global.FiniteAdeles ℚ
local notation "Ẑ" => Langlands.Global.integralFiniteAdeles ℚ
local notation "ϕ" => algebraMap ℚ (Langlands.Global.FiniteAdeles ℚ)

open Langlands.Global.RationalLattice (IsIntegral)

theorem isIntegral_smul {m o : Type*} {M : Matrix m o 𝔸f} (hM : IsIntegral M) {t : 𝔸f}
    (ht : t ∈ Ẑ) : IsIntegral (t • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ ht (hM i j)

theorem isIntegral_transpose {m o : Type*} {M : Matrix m o 𝔸f} (hM : IsIntegral M) :
    IsIntegral Mᵀ := fun i j => hM j i

theorem map_map_intCast {m o : Type*} (P : Matrix m o ℤ) :
    (P.map (Int.cast : ℤ → ℚ)).map ϕ = P.map (Int.cast : ℤ → 𝔸f) := by
  ext i j
  simp

theorem map_inv_of_isUnit {m : Type*} [Fintype m] [DecidableEq m] {B : Matrix m m ℚ}
    (hB : IsUnit B.det) : B⁻¹.map ϕ = (B.map ϕ)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hB, Matrix.map_one _ (map_zero ϕ) (map_one ϕ)]

theorem isUnit_det_map {m : Type*} [Fintype m] [DecidableEq m] {B : Matrix m m ℚ}
    (hB : IsUnit B.det) : IsUnit (B.map ϕ).det := by
  have h : (B.map ϕ).det = ϕ B.det := (RingHom.map_det ϕ B).symm
  rw [h]
  exact hB.map ϕ

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {σ : AlgebraInvolution ℚ A} {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ A)

/-- The matrix of left multiplication by the algebra component `x` of a finite adelic point
`(x, c)`, in the basis `1 ⊗ b_i` of `𝔸_f ⊗ A`. -/
def pointMatrix (g : σ.FiniteAdelicPoints) : Matrix ι ι 𝔸f :=
  Algebra.leftMulMatrix (Algebra.TensorProduct.basis 𝔸f b) (g.1.1 : 𝔸f ⊗[ℚ] A)

/-- The multiplier `c` of a finite adelic point `(x, c)`, as a finite adele. -/
def pointMultiplier (g : σ.FiniteAdelicPoints) : 𝔸f :=
  (g.1.2 : 𝔸f)

theorem pointMatrix_mul (g h : σ.FiniteAdelicPoints) :
    pointMatrix b (g * h) = pointMatrix b g * pointMatrix b h := by
  change Algebra.leftMulMatrix _ ((g.1.1 * h.1.1 : (𝔸f ⊗[ℚ] A)ˣ) : 𝔸f ⊗[ℚ] A) = _
  rw [Units.val_mul, map_mul]
  rfl

theorem pointMatrix_one : pointMatrix b (1 : σ.FiniteAdelicPoints) = 1 := by
  change Algebra.leftMulMatrix _ ((1 : (𝔸f ⊗[ℚ] A)ˣ) : 𝔸f ⊗[ℚ] A) = _
  rw [Units.val_one, map_one]

theorem pointMatrix_inv_mul (g : σ.FiniteAdelicPoints) :
    pointMatrix b g⁻¹ * pointMatrix b g = 1 := by
  rw [← pointMatrix_mul, inv_mul_cancel, pointMatrix_one]

theorem pointMatrix_mul_inv (g : σ.FiniteAdelicPoints) :
    pointMatrix b g * pointMatrix b g⁻¹ = 1 := by
  rw [← pointMatrix_mul, mul_inv_cancel, pointMatrix_one]

theorem isUnit_det_pointMatrix (g : σ.FiniteAdelicPoints) : IsUnit (pointMatrix b g).det :=
  Matrix.isUnit_det_of_left_inverse (pointMatrix_inv_mul b g)

theorem inv_pointMatrix (g : σ.FiniteAdelicPoints) :
    (pointMatrix b g)⁻¹ = pointMatrix b g⁻¹ :=
  Matrix.inv_eq_left_inv (pointMatrix_inv_mul b g)

theorem pointMultiplier_mul (g h : σ.FiniteAdelicPoints) :
    pointMultiplier (g * h) = pointMultiplier g * pointMultiplier h :=
  rfl

theorem pointMultiplier_inv_mul (g : σ.FiniteAdelicPoints) :
    pointMultiplier g⁻¹ * pointMultiplier g = 1 := by
  rw [← pointMultiplier_mul, inv_mul_cancel]
  rfl

theorem pointMatrix_finiteAdelicDiagonal (ρ : σ.similitudes) :
    pointMatrix b (σ.finiteAdelicDiagonal ρ) =
      (Algebra.leftMulMatrix b (ρ.1.1 : A)).map ϕ := by
  change Algebra.leftMulMatrix _ ((1 : 𝔸f) ⊗ₜ[ℚ] (ρ.1.1 : A)) = _
  exact AlgebraInvolution.leftMulMatrix_one_tmul 𝔸f b _

theorem pointMultiplier_finiteAdelicDiagonal (ρ : σ.similitudes) :
    pointMultiplier (σ.finiteAdelicDiagonal ρ) = ϕ (ρ.1.2 : ℚ) :=
  rfl

theorem pointMatrix_mul_rightMulMatrix (g : σ.FiniteAdelicPoints) (y : A) :
    pointMatrix b g * (AlgebraInvolution.rightMulMatrix b y).map ϕ =
      (AlgebraInvolution.rightMulMatrix b y).map ϕ * pointMatrix b g := by
  rw [← AlgebraInvolution.rightMulMatrix_one_tmul]
  exact AlgebraInvolution.leftMulMatrix_mul_rightMulMatrix _ _ _

variable (σ) in
/-- **The lattice level.** The stabilizer in `GJ(𝔸_f)` of the lattice `⊕ Ẑ (1 ⊗ b_i)` of
`𝔸_f ⊗ A` with unit multiplier: the points `(x, c)` such that the matrices of left multiplication
by `x` and `x⁻¹` are integral and `c, c⁻¹ ∈ Ẑ`. -/
def latticeLevel : Subgroup σ.FiniteAdelicPoints where
  carrier := {g | IsIntegral (pointMatrix b g) ∧ IsIntegral (pointMatrix b g⁻¹) ∧
    pointMultiplier g ∈ Ẑ ∧ pointMultiplier g⁻¹ ∈ Ẑ}
  mul_mem' := by
    rintro g h ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pointMatrix_mul]
      exact h1.mul h1'
    · rw [_root_.mul_inv_rev, pointMatrix_mul]
      exact h2'.mul h2
    · rw [pointMultiplier_mul]
      exact Subring.mul_mem _ h3 h3'
    · rw [_root_.mul_inv_rev, pointMultiplier_mul]
      exact Subring.mul_mem _ h4' h4
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pointMatrix_one]
      exact Langlands.Global.RationalLattice.isIntegral_one
    · rw [inv_one, pointMatrix_one]
      exact Langlands.Global.RationalLattice.isIntegral_one
    · exact Subring.one_mem _
    · exact Subring.one_mem _
  inv_mem' := by
    rintro g ⟨h1, h2, h3, h4⟩
    exact ⟨h2, by rwa [inv_inv], h4, by rwa [inv_inv]⟩

theorem mem_latticeLevel {g : σ.FiniteAdelicPoints} :
    g ∈ latticeLevel σ b ↔ IsIntegral (pointMatrix b g) ∧ IsIntegral (pointMatrix b g⁻¹) ∧
      pointMultiplier g ∈ Ẑ ∧ pointMultiplier g⁻¹ ∈ Ẑ :=
  Iff.rfl

/-- `B` and `r` reduce the point `g = (x, c)`: the matrix `X` of `x` factors as `X = B W` with `B`
rational and `W, W⁻¹ = X⁻¹ B` integral, and `c = r u` with `r > 0` rational and `u` a unit of
`Ẑ`. -/
structure IsReduction (g : σ.FiniteAdelicPoints) (B : Matrix ι ι ℚ) (r : ℚ) : Prop where
  isUnit_det : IsUnit B.det
  pos : 0 < r
  isIntegral_left : IsIntegral ((pointMatrix b g)⁻¹ * B.map ϕ)
  isIntegral_right : IsIntegral ((B.map ϕ)⁻¹ * pointMatrix b g)
  mem_left : pointMultiplier g * ϕ r⁻¹ ∈ Ẑ
  mem_right : ϕ r * pointMultiplier g⁻¹ ∈ Ẑ

/-- Every finite adelic point has a reduction (class number one of `ℚ`). -/
theorem exists_isReduction (g : σ.FiniteAdelicPoints) : ∃ B r, IsReduction b g B r := by
  obtain ⟨B, W, hB, hW, hV, hXW⟩ :=
    Langlands.Global.RationalLattice.exists_rat_mul_integral _ (isUnit_det_pointMatrix b g)
  obtain ⟨r, hr, u, u', hu, hu', huu, hcu⟩ :=
    Langlands.Global.RationalLattice.exists_pos_rat_mul_unit (pointMultiplier g)
      (g.1.2.isUnit)
  refine ⟨B, r, hB, hr, hV, ?_, ?_, ?_⟩
  · rw [hXW, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_map hB), Matrix.one_mul]
    exact hW
  · rw [hcu, mul_comm (ϕ r), mul_assoc, ← map_mul, mul_inv_cancel₀ hr.ne', map_one, mul_one]
    exact hu
  · have h1 := pointMultiplier_inv_mul g
    have : ϕ r * pointMultiplier g⁻¹ = u' := by
      calc ϕ r * pointMultiplier g⁻¹ = ϕ r * pointMultiplier g⁻¹ * (u * u') := by
            rw [huu, mul_one]
        _ = pointMultiplier g⁻¹ * (ϕ r * u) * u' := by ring
        _ = u' := by rw [← hcu, h1, one_mul]
    rw [this]
    exact hu'

/-- Reductions may be changed by integral unimodular matrices. -/
theorem IsReduction.mul_right {g : σ.FiniteAdelicPoints} {B : Matrix ι ι ℚ} {r : ℚ}
    (h : IsReduction b g B r) {P Q : Matrix ι ι ℤ} (hQP : Q * P = 1) :
    IsReduction b g (B * P.map (Int.cast : ℤ → ℚ)) r := by
  have hQP' : Q.map (Int.cast : ℤ → 𝔸f) * P.map (Int.cast : ℤ → 𝔸f) = 1 := by
    rw [show Q.map (Int.cast : ℤ → 𝔸f) * P.map (Int.cast : ℤ → 𝔸f) = (Q * P).map
      (Int.castRingHom 𝔸f) from (Matrix.map_mul (f := Int.castRingHom 𝔸f)).symm, hQP]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hQPq : Q.map (Int.cast : ℤ → ℚ) * P.map (Int.cast : ℤ → ℚ) = 1 := by
    rw [show Q.map (Int.cast : ℤ → ℚ) * P.map (Int.cast : ℤ → ℚ) = (Q * P).map
      (Int.castRingHom ℚ) from (Matrix.map_mul (f := Int.castRingHom ℚ)).symm, hQP]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨?_, h.pos, ?_, ?_, h.mem_left, h.mem_right⟩
  · rw [Matrix.det_mul]
    exact h.isUnit_det.mul (Matrix.isUnit_det_of_left_inverse hQPq)
  · rw [Matrix.map_mul, map_map_intCast, ← Matrix.mul_assoc]
    exact h.isIntegral_left.mul (Langlands.Global.RationalLattice.isIntegral_map_intCast P)
  · rw [Matrix.map_mul, map_map_intCast, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hQP',
      Matrix.mul_assoc]
    exact (Langlands.Global.RationalLattice.isIntegral_map_intCast Q).mul h.isIntegral_right

variable [Module.Finite ℚ A]

variable (σ) in
/-- The Gram matrix of the trace form of `σ` in the basis `b`. -/
abbrev gram : Matrix ι ι ℚ := LinearMap.BilinForm.toMatrix b σ.traceForm

/-- **Equal reduction data give equal double cosets.** If `(B, r)` reduces `g`, `(B', r')`
reduces `g'`, the scaled Gram matrices `r⁻¹ Bᵀ G B` and `r'⁻¹ B'ᵀ G B'` agree and the conjugated
right multiplication matrices `B⁻¹ R_k B` and `B'⁻¹ R_k B'` agree, then `g` and `g'` lie in the same
double coset `GJ(ℚ) g K₀`. -/
theorem mk_eq_of_isReduction (hpos : (σ.baseChange ℝ).IsPositive) {g g' : σ.FiniteAdelicPoints}
    {B B' : Matrix ι ι ℚ} {r r' : ℚ} (h : IsReduction b g B r) (h' : IsReduction b g' B' r')
    (hS : r⁻¹ • (Bᵀ * gram σ b * B) = r'⁻¹ • (B'ᵀ * gram σ b * B'))
    (hR : ∀ k, B⁻¹ * AlgebraInvolution.rightMulMatrix b (b k) * B =
      B'⁻¹ * AlgebraInvolution.rightMulMatrix b (b k) * B') :
    DoubleCoset.mk σ.finiteAdelicDiagonal.range (latticeLevel σ b) g =
      DoubleCoset.mk σ.finiteAdelicDiagonal.range (latticeLevel σ b) g' := by
  set G := gram σ b with hG
  have hB := h.isUnit_det
  have hB' := h'.isUnit_det
  have comm : ∀ C C' : Matrix ι ι ℚ, IsUnit C.det → IsUnit C'.det →
      (∀ k, C⁻¹ * AlgebraInvolution.rightMulMatrix b (b k) * C =
        C'⁻¹ * AlgebraInvolution.rightMulMatrix b (b k) * C') →
      ∀ k, C' * C⁻¹ * AlgebraInvolution.rightMulMatrix b (b k) =
        AlgebraInvolution.rightMulMatrix b (b k) * (C' * C⁻¹) := by
    intro C C' hC hC' hCC k
    set R := AlgebraInvolution.rightMulMatrix b (b k)
    calc C' * C⁻¹ * R = C' * C⁻¹ * R * (C * C⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hC, Matrix.mul_one]
      _ = C' * (C⁻¹ * R * C) * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = C' * (C'⁻¹ * R * C') * C⁻¹ := by rw [hCC k]
      _ = C' * C'⁻¹ * R * (C' * C⁻¹) := by simp only [Matrix.mul_assoc]
      _ = R * (C' * C⁻¹) := by rw [Matrix.mul_nonsing_inv _ hC', Matrix.one_mul]
  obtain ⟨γ, hγ⟩ := AlgebraInvolution.exists_leftMulMatrix_eq b (B' * B⁻¹) (comm B B' hB hB' hR)
  obtain ⟨δ, hδ⟩ := AlgebraInvolution.exists_leftMulMatrix_eq b (B * B'⁻¹)
    (comm B' B hB' hB fun k => (hR k).symm)
  have hΓ : B' * B⁻¹ * (B * B'⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB, Matrix.mul_nonsing_inv _ hB']
  have hΓ' : B * B'⁻¹ * (B' * B⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB', Matrix.mul_nonsing_inv _ hB]
  have hγδ : γ * δ = 1 :=
    Algebra.leftMulMatrix_injective b (by rw [map_mul, hγ, hδ, hΓ, map_one])
  have hδγ : δ * γ = 1 :=
    Algebra.leftMulMatrix_injective b (by rw [map_mul, hγ, hδ, hΓ', map_one])
  have hr := h.pos
  have hr' := h'.pos
  have hS' : B'ᵀ * G * B' = (r' / r) • (Bᵀ * G * B) := by
    have e := congrArg (fun M => r' • M) hS
    simp only [smul_smul, mul_inv_cancel₀ hr'.ne', one_smul] at e
    rw [← e, div_eq_mul_inv]
  have hgram : (Algebra.leftMulMatrix b γ)ᵀ * G * Algebra.leftMulMatrix b γ = (r' / r) • G := by
    rw [hγ, Matrix.transpose_mul]
    calc B⁻¹ᵀ * B'ᵀ * G * (B' * B⁻¹) = B⁻¹ᵀ * (B'ᵀ * G * B') * B⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (r' / r) • (B⁻¹ᵀ * (Bᵀ * G * B) * B⁻¹) := by
          rw [hS', Matrix.mul_smul, Matrix.smul_mul]
      _ = (r' / r) • G := by
          congr 1
          simp only [← Matrix.mul_assoc]
          rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hB, Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
  have hσγ := AlgebraInvolution.apply_mul_self_eq_of_gram σ hpos b hgram
  have ht : r' / r ≠ 0 := div_ne_zero hr'.ne' hr.ne'
  let γu : Aˣ := ⟨γ, δ, hγδ, hδγ⟩
  let tu : ℚˣ := Units.mk0 (r' / r) ht
  have hmem : (γu, tu) ∈ σ.similitudes := by
    rw [AlgebraInvolution.mem_similitudes_iff]
    change γ * σ γ = algebraMap ℚ A (r' / r)
    have hσ : σ γ = algebraMap ℚ A (r' / r) * δ := by
      calc σ γ = σ γ * (γ * δ) := by rw [hγδ, mul_one]
        _ = σ γ * γ * δ := by rw [mul_assoc]
        _ = _ := by rw [hσγ]
    rw [hσ, ← mul_assoc, ← Algebra.commutes, mul_assoc, hγδ, mul_one]
  set ρ : σ.similitudes := ⟨(γu, tu), hmem⟩
  set d := σ.finiteAdelicDiagonal ρ with hd
  have hdM : pointMatrix b d = (B' * B⁻¹).map ϕ := by
    rw [hd, pointMatrix_finiteAdelicDiagonal, ← hγ]
  have hdM' : pointMatrix b d⁻¹ = (B * B'⁻¹).map ϕ := by
    rw [hd, ← map_inv, pointMatrix_finiteAdelicDiagonal, ← hδ]
    rfl
  have hdc : pointMultiplier d = ϕ r' * ϕ r⁻¹ := by
    rw [hd, pointMultiplier_finiteAdelicDiagonal]
    change ϕ (r' / r) = _
    rw [div_eq_mul_inv, map_mul]
  have hdc' : pointMultiplier d⁻¹ = ϕ r * ϕ r'⁻¹ := by
    rw [hd, ← map_inv, pointMultiplier_finiteAdelicDiagonal]
    change ϕ ((tu⁻¹ : ℚˣ) : ℚ) = _
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_div, div_eq_mul_inv, map_mul]
  rw [DoubleCoset.eq]
  refine ⟨d, ⟨ρ, rfl⟩, g⁻¹ * d⁻¹ * g', ?_, by group⟩
  have hinv : (g⁻¹ * d⁻¹ * g')⁻¹ = g'⁻¹ * d * g := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : pointMatrix b (g⁻¹ * d⁻¹ * g') =
        ((pointMatrix b g)⁻¹ * B.map ϕ) * ((B'.map ϕ)⁻¹ * pointMatrix b g') := by
      rw [pointMatrix_mul, pointMatrix_mul, hdM', Matrix.map_mul, map_inv_of_isUnit hB',
        inv_pointMatrix]
      simp only [Matrix.mul_assoc]
    rw [e]
    exact h.isIntegral_left.mul h'.isIntegral_right
  · have e : pointMatrix b (g⁻¹ * d⁻¹ * g')⁻¹ =
        ((pointMatrix b g')⁻¹ * B'.map ϕ) * ((B.map ϕ)⁻¹ * pointMatrix b g) := by
      rw [hinv, pointMatrix_mul, pointMatrix_mul, hdM, Matrix.map_mul, map_inv_of_isUnit hB,
        inv_pointMatrix]
      simp only [Matrix.mul_assoc]
    rw [e]
    exact h'.isIntegral_left.mul h.isIntegral_right
  · have e : pointMultiplier (g⁻¹ * d⁻¹ * g') =
        (ϕ r * pointMultiplier g⁻¹) * (pointMultiplier g' * ϕ r'⁻¹) := by
      rw [pointMultiplier_mul, pointMultiplier_mul, hdc']
      ring
    rw [e]
    exact Subring.mul_mem _ h.mem_right h'.mem_left
  · have e : pointMultiplier (g⁻¹ * d⁻¹ * g')⁻¹ =
        (ϕ r' * pointMultiplier g'⁻¹) * (pointMultiplier g * ϕ r⁻¹) := by
      rw [hinv, pointMultiplier_mul, pointMultiplier_mul, hdc]
      ring
    rw [e]
    exact Subring.mul_mem _ h'.mem_right h.mem_left

omit [Module.Finite ℚ A] in
theorem gram_transpose : (gram σ b)ᵀ = gram σ b := by
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply]
  exact AlgebraInvolution.traceForm_comm σ _ _

theorem pointMatrix_transpose_mul_gram (g : σ.FiniteAdelicPoints) :
    (pointMatrix b g)ᵀ * (gram σ b).map ϕ * pointMatrix b g =
      pointMultiplier g • (gram σ b).map ϕ :=
  AlgebraInvolution.points_leftMulMatrix_transpose_mul_gram 𝔸f σ b g

omit [Module.Finite ℚ A] in
theorem map_smul_rat {m o : Type*} (q : ℚ) (M : Matrix m o ℚ) :
    (q • M).map ϕ = ϕ q • M.map ϕ := by
  ext i j
  simp

omit [Module.Finite ℚ A] [DecidableEq ι] in
theorem dotProduct_transpose_mul_mul_mulVec {R : Type*} [CommRing R] (B G : Matrix ι ι R)
    (v : ι → R) : v ⬝ᵥ (Bᵀ * G * B) *ᵥ v = (B *ᵥ v) ⬝ᵥ G *ᵥ (B *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

omit [Module.Finite ℚ A] [DecidableEq ι] in
theorem intCast_dotProduct_mulVec (S : Matrix ι ι ℤ) (v : ι → ℤ) :
    ((v ⬝ᵥ S *ᵥ v : ℤ) : ℚ) =
      (fun i => (v i : ℚ)) ⬝ᵥ S.map (Int.cast : ℤ → ℚ) *ᵥ (fun i => (v i : ℚ)) := by
  rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_dotProduct]
  congr 1
  ext i
  exact RingHom.map_mulVec _ _ _ i

omit [Module.Finite ℚ A] in
theorem det_mem_of_isIntegral {M : Matrix ι ι 𝔸f} (hM : IsIntegral M) : M.det ∈ Ẑ := by
  let M' : Matrix ι ι Ẑ := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have e : M = M'.map (Ẑ.subtype) := by
    ext i j
    rfl
  have e' : (M'.map (Ẑ.subtype)).det = Ẑ.subtype M'.det := (RingHom.map_det _ _).symm
  rw [e, e']
  exact M'.det.2

/-- For a point `g = (x, c)` with matrix `X`, a rational matrix `B` and `r ∈ ℚ`, the matrix
`(N / r) Bᵀ G B` becomes `(c / r) Vᵀ (N G) V` over `𝔸_f`, with `V = X⁻¹ B`. -/
theorem map_smul_gram (g : σ.FiniteAdelicPoints) (B : Matrix ι ι ℚ) (r : ℚ) (N : ℤ) :
    (((N : ℚ) / r) • (Bᵀ * gram σ b * B)).map ϕ =
      (pointMultiplier g * ϕ r⁻¹) • (((pointMatrix b g)⁻¹ * B.map ϕ)ᵀ *
        ((N : 𝔸f) • (gram σ b).map ϕ) * ((pointMatrix b g)⁻¹ * B.map ϕ)) := by
  set X := pointMatrix b g
  set V := X⁻¹ * B.map ϕ
  have hBV : B.map ϕ = X * V :=
    (Matrix.mul_nonsing_inv_cancel_left X _ (isUnit_det_pointMatrix b g)).symm
  rw [map_smul_rat, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hBV,
    Matrix.transpose_mul X V]
  have e : Vᵀ * Xᵀ * (gram σ b).map ϕ * (X * V) =
      Vᵀ * (Xᵀ * (gram σ b).map ϕ * X) * V := by
    simp only [Matrix.mul_assoc]
  rw [e, pointMatrix_transpose_mul_gram]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  rw [div_eq_mul_inv, map_mul, map_intCast]
  ring

theorem IsReduction.isIntegral_map_smul_gram {g : σ.FiniteAdelicPoints} {B : Matrix ι ι ℚ}
    {r : ℚ} (h : IsReduction b g B r) {N : ℤ} (hN : IsIntegral ((N : 𝔸f) • (gram σ b).map ϕ)) :
    IsIntegral ((((N : ℚ) / r) • (Bᵀ * gram σ b * B)).map ϕ) := by
  rw [map_smul_gram]
  exact isIntegral_smul (((isIntegral_transpose h.isIntegral_left).mul hN).mul
    h.isIntegral_left) h.mem_left

/-- **Determinants of reduced forms.** If `S = (N / r) Bᵀ G B` and `G₀ = N G` are integer
matrices and `det S ≠ 0`, then `det S` divides `det G₀`. -/
theorem IsReduction.exists_det_eq {g : σ.FiniteAdelicPoints} {B : Matrix ι ι ℚ} {r : ℚ}
    (h : IsReduction b g B r) {N : ℤ} {S G₀ : Matrix ι ι ℤ}
    (hS : S.map (Int.cast : ℤ → ℚ) = ((N : ℚ) / r) • (Bᵀ * gram σ b * B))
    (hG₀ : G₀.map (Int.cast : ℤ → ℚ) = (N : ℚ) • gram σ b) (hdet : S.det ≠ 0) :
    ∃ z : ℤ, G₀.det = z * S.det := by
  set X := pointMatrix b g
  set V := X⁻¹ * B.map ϕ
  set W := (B.map ϕ)⁻¹ * X
  have hX := isUnit_det_pointMatrix b g
  have hBϕ := isUnit_det_map h.isUnit_det
  have hVW : V * W = 1 := by
    simp only [V, W, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hBϕ, Matrix.nonsing_inv_mul _ hX]
  set u := pointMultiplier g * ϕ r⁻¹
  set u' := ϕ r * pointMultiplier g⁻¹
  have huu : u' * u = 1 := by
    have h1 := pointMultiplier_inv_mul g
    calc u' * u = (pointMultiplier g⁻¹ * pointMultiplier g) * (ϕ r * ϕ r⁻¹) := by ring
      _ = 1 := by rw [h1, ← map_mul, mul_inv_cancel₀ h.pos.ne', map_one, one_mul]
  set G₀ϕ := G₀.map (Int.cast : ℤ → 𝔸f)
  have hG₀ϕ : G₀ϕ = (N : 𝔸f) • (gram σ b).map ϕ := by
    rw [show G₀ϕ = (G₀.map (Int.cast : ℤ → ℚ)).map ϕ from (map_map_intCast G₀).symm, hG₀,
      map_smul_rat, map_intCast]
  have hSϕ : S.map (Int.cast : ℤ → 𝔸f) = u • (Vᵀ * G₀ϕ * V) := by
    rw [← map_map_intCast, hS, map_smul_gram, hG₀ϕ]
  have hWSW : Wᵀ * S.map (Int.cast : ℤ → 𝔸f) * W = u • G₀ϕ := by
    rw [hSϕ, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have e : Wᵀ * (Vᵀ * G₀ϕ * V) * W = (V * W)ᵀ * G₀ϕ * (V * W) := by
      rw [Matrix.transpose_mul V W]
      simp only [Matrix.mul_assoc]
    rw [e, hVW, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hdet' : (G₀.det : 𝔸f) = u' ^ Fintype.card ι * (W.det * W.det) * (S.det : 𝔸f) := by
    have e1 : (G₀.det : 𝔸f) = G₀ϕ.det := RingHom.map_det (Int.castRingHom 𝔸f) G₀
    have e2 : (S.det : 𝔸f) = (S.map (Int.cast : ℤ → 𝔸f)).det :=
      RingHom.map_det (Int.castRingHom 𝔸f) S
    have e3 := congrArg Matrix.det hWSW
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul] at e3
    rw [e1, e2]
    calc G₀ϕ.det = (u' * u) ^ Fintype.card ι * G₀ϕ.det := by rw [huu, one_pow, one_mul]
      _ = u' ^ Fintype.card ι * (u ^ Fintype.card ι * G₀ϕ.det) := by rw [mul_pow, mul_assoc]
      _ = _ := by rw [← e3]; ring
  have hS0 : (S.det : ℚ) ≠ 0 := Int.cast_ne_zero.2 hdet
  have hmem : ϕ ((G₀.det : ℚ) / S.det) ∈ Ẑ := by
    have e : ϕ ((G₀.det : ℚ) / S.det) = u' ^ Fintype.card ι * (W.det * W.det) := by
      have e4 : ϕ (S.det : ℚ) * ϕ ((S.det : ℚ)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hS0, map_one]
      rw [div_eq_mul_inv, map_mul, map_intCast, hdet', ← map_intCast ϕ S.det, mul_assoc,
        e4, mul_one]
    rw [e]
    have hW := det_mem_of_isIntegral h.isIntegral_right
    exact Subring.mul_mem _ (Subring.pow_mem _ h.mem_right _) (Subring.mul_mem _ hW hW)
  obtain ⟨z, hz⟩ := Langlands.Global.exists_intCast_eq_of_mem_integralFiniteAdeles hmem
  refine ⟨z, ?_⟩
  have : (G₀.det : ℚ) = z * S.det := by
    rw [hz, div_mul_cancel₀ _ hS0]
  exact_mod_cast this

/-- Reduced forms are positive definite. -/
theorem IsReduction.dotProduct_pos (hpos : (σ.baseChange ℝ).IsPositive)
    {g : σ.FiniteAdelicPoints} {B : Matrix ι ι ℚ} {r : ℚ} (h : IsReduction b g B r) {N : ℤ}
    (hN : 0 < N) {S : Matrix ι ι ℤ}
    (hS : S.map (Int.cast : ℤ → ℚ) = ((N : ℚ) / r) • (Bᵀ * gram σ b * B)) {v : ι → ℤ}
    (hv : v ≠ 0) : 0 < v ⬝ᵥ S *ᵥ v := by
  suffices h0 : (0 : ℚ) < ((v ⬝ᵥ S *ᵥ v : ℤ) : ℚ) by exact_mod_cast h0
  set w : ι → ℚ := fun i => (v i : ℚ)
  have hw : B *ᵥ w ≠ 0 := by
    intro h0
    apply hv
    have e : w = 0 := by
      rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul B h.isUnit_det, ← Matrix.mulVec_mulVec,
        h0, Matrix.mulVec_zero]
    funext i
    have e' := congrFun e i
    simp only [w, Pi.zero_apply] at e'
    exact_mod_cast e'
  rw [intCast_dotProduct_mulVec, hS, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_transpose_mul_mul_mulVec]
  exact mul_pos (div_pos (Int.cast_pos.2 hN) h.pos)
    (AlgebraInvolution.dotProduct_toMatrix_traceForm_mulVec_pos σ hpos b hw)

omit [Module.Finite ℚ A] in
theorem transpose_eq_of_map_eq {B : Matrix ι ι ℚ} {t : ℚ} {S : Matrix ι ι ℤ}
    (hS : S.map (Int.cast : ℤ → ℚ) = t • (Bᵀ * gram σ b * B)) : Sᵀ = S := by
  have hsym : (Bᵀ * gram σ b * B)ᵀ = Bᵀ * gram σ b * B := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, gram_transpose,
      Matrix.mul_assoc]
  ext i j
  have e1 : S.map (Int.cast : ℤ → ℚ) j i = (t • (Bᵀ * gram σ b * B)) j i := by rw [hS]
  have e2 : S.map (Int.cast : ℤ → ℚ) i j = (t • (Bᵀ * gram σ b * B)) i j := by rw [hS]
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
  have e3 : (Bᵀ * gram σ b * B) j i = (Bᵀ * gram σ b * B) i j := by
    rw [← Matrix.transpose_apply (Bᵀ * gram σ b * B) i j, hsym]
  rw [Matrix.transpose_apply]
  have : (S j i : ℚ) = S i j := by rw [e1, e2, e3]
  exact_mod_cast this

omit [Module.Finite ℚ A] in
/-- Under a reduction, `B⁻¹ R B` becomes `W R V` over `𝔸_f` for every right multiplication
matrix `R`. -/
theorem IsReduction.map_conj_rightMulMatrix {g : σ.FiniteAdelicPoints} {B : Matrix ι ι ℚ}
    {r : ℚ} (h : IsReduction b g B r) (y : A) :
    (B⁻¹ * AlgebraInvolution.rightMulMatrix b y * B).map ϕ =
      ((B.map ϕ)⁻¹ * pointMatrix b g) * (AlgebraInvolution.rightMulMatrix b y).map ϕ *
        ((pointMatrix b g)⁻¹ * B.map ϕ) := by
  set X := pointMatrix b g
  set R := (AlgebraInvolution.rightMulMatrix b y).map ϕ
  have hX := isUnit_det_pointMatrix b g
  rw [Matrix.map_mul, Matrix.map_mul, map_inv_of_isUnit h.isUnit_det]
  have hXR : X * R = R * X := pointMatrix_mul_rightMulMatrix b g y
  calc (B.map ϕ)⁻¹ * R * B.map ϕ = (B.map ϕ)⁻¹ * (R * X * X⁻¹) * B.map ϕ := by
        rw [Matrix.mul_nonsing_inv_cancel_right _ _ hX]
    _ = (B.map ϕ)⁻¹ * (X * R * X⁻¹) * B.map ϕ := by rw [hXR]
    _ = ((B.map ϕ)⁻¹ * X) * R * (X⁻¹ * B.map ϕ) := by simp only [Matrix.mul_assoc]

omit [Module.Finite ℚ A] in
theorem IsReduction.isIntegral_map_smul_conj {g : σ.FiniteAdelicPoints} {B : Matrix ι ι ℚ}
    {r : ℚ} (h : IsReduction b g B r) (y : A) {N : ℤ}
    (hN : IsIntegral ((N : 𝔸f) • (AlgebraInvolution.rightMulMatrix b y).map ϕ)) :
    IsIntegral (((N : ℚ) • (B⁻¹ * AlgebraInvolution.rightMulMatrix b y * B)).map ϕ) := by
  rw [map_smul_rat, h.map_conj_rightMulMatrix, map_intCast]
  have e : (N : 𝔸f) • ((B.map ϕ)⁻¹ * pointMatrix b g *
      (AlgebraInvolution.rightMulMatrix b y).map ϕ * ((pointMatrix b g)⁻¹ * B.map ϕ)) =
      (B.map ϕ)⁻¹ * pointMatrix b g * ((N : 𝔸f) • (AlgebraInvolution.rightMulMatrix b y).map ϕ) *
        ((pointMatrix b g)⁻¹ * B.map ϕ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact (h.isIntegral_right.mul hN).mul h.isIntegral_left

omit [Module.Finite ℚ A] in
/-- Conjugated right multiplications are bounded for the reduced form. -/
theorem conj_dotProduct_le {B : Matrix ι ι ℚ} (hB : IsUnit B.det) (R : Matrix ι ι ℚ) {C : ℕ}
    (hC : ∀ w : ι → ℚ, w ⬝ᵥ (Rᵀ * gram σ b * R) *ᵥ w ≤ C * (w ⬝ᵥ gram σ b *ᵥ w))
    (x : ι → ℚ) :
    ((B⁻¹ * R * B) *ᵥ x) ⬝ᵥ (Bᵀ * gram σ b * B) *ᵥ ((B⁻¹ * R * B) *ᵥ x) ≤
      C * (x ⬝ᵥ (Bᵀ * gram σ b * B) *ᵥ x) := by
  rw [dotProduct_transpose_mul_mul_mulVec, dotProduct_transpose_mul_mul_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB,
    Matrix.one_mul, ← Matrix.mulVec_mulVec, ← dotProduct_transpose_mul_mul_mulVec]
  exact hC _

end Lattice

section Finite

local notation "𝔸f" => Langlands.Global.FiniteAdeles ℚ
local notation "ϕ" => algebraMap ℚ (Langlands.Global.FiniteAdeles ℚ)

open Langlands.Global.RationalLattice (IsIntegral)

theorem exists_int_smul {m o : Type*} [Fintype m] [Fintype o] (M : Matrix m o ℚ) :
    ∃ N : ℤ, 0 < N ∧ ∃ M₀ : Matrix m o ℤ, M₀.map (Int.cast : ℤ → ℚ) = (N : ℚ) • M := by
  obtain ⟨N₀, hN₀, hint⟩ :=
    Langlands.Global.RationalLattice.exists_intCast_smul_isIntegral (M.map ϕ)
  have h1 : IsIntegral (((N₀ : ℚ) • M).map ϕ) := by
    rw [map_smul_rat, map_intCast]
    exact hint
  obtain ⟨M₁, hM₁⟩ := Langlands.Global.RationalLattice.exists_int_of_isIntegral h1
  refine ⟨N₀ * N₀, mul_self_pos.2 hN₀, N₀ • M₁, ?_⟩
  ext i j
  have e : M₁.map (Int.cast : ℤ → ℚ) i j = ((N₀ : ℚ) • M) i j := by rw [hM₁]
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e ⊢
  push_cast
  rw [e]
  ring

theorem intCast_map_mul {m o p : Type*} [Fintype o] (M : Matrix m o ℤ) (N : Matrix o p ℤ) :
    (M * N).map (Int.cast : ℤ → ℚ) = M.map (Int.cast : ℤ → ℚ) * N.map (Int.cast : ℤ → ℚ) :=
  Matrix.map_mul (f := Int.castRingHom ℚ)

variable {A : Type*} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {σ : AlgebraInvolution ℚ A} {n : ℕ} (b : Basis (Fin n) ℚ A)

/-- **Finiteness of definite double cosets.** For an involution `σ` of a finite-dimensional
`ℚ`-algebra whose real scalar extension is positive, and a `ℚ`-basis `b`, the double coset space
`GJ(ℚ) \ GJ(𝔸_f) / K₀` is finite for the lattice level `K₀ = latticeLevel σ b`. -/
theorem finite_doubleCosets_latticeLevel (hpos : (σ.baseChange ℝ).IsPositive) :
    Finite (EquivariantForms.DoubleCosets σ.finiteAdelicDiagonal (latticeLevel σ b)) := by
  classical
  set G := gram σ b with hGdef
  set R : Fin n → Matrix (Fin n) (Fin n) ℚ := fun k => AlgebraInvolution.rightMulMatrix b (b k)
    with hRdef
  obtain ⟨N, hN, G₀, hG₀⟩ := exists_int_smul G
  obtain ⟨N', hN', R₀, hR₀⟩ :=
    exists_int_smul (Matrix.of fun i (jk : Fin n × Fin n) => R jk.2 i jk.1)
  have hRint : ∀ k, IsIntegral ((N' : 𝔸f) • (R k).map ϕ) := by
    intro k i j
    have e : R₀.map (Int.cast : ℤ → ℚ) i (j, k) =
        ((N' : ℚ) • Matrix.of fun i (jk : Fin n × Fin n) => R jk.2 i jk.1) i (j, k) := by
      rw [hR₀]
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at e
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [← map_intCast ϕ N', ← map_mul, ← e, map_intCast]
    exact intCast_mem _ _
  have hGint : IsIntegral ((N : 𝔸f) • G.map ϕ) := by
    rw [← map_intCast ϕ N, ← map_smul_rat, ← hG₀, map_map_intCast]
    exact Langlands.Global.RationalLattice.isIntegral_map_intCast G₀
  have hG0 : G₀.det ≠ 0 := by
    have hGdet : G.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have h1 := AlgebraInvolution.dotProduct_toMatrix_traceForm_mulVec_pos σ hpos b hv
      rw [hGv, dotProduct_zero] at h1
      exact lt_irrefl _ h1
    have e : (G₀.det : ℚ) = (N : ℚ) ^ n * G.det := by
      rw [show (G₀.det : ℚ) = (G₀.map (Int.cast : ℤ → ℚ)).det from
        RingHom.map_det (Int.castRingHom ℚ) G₀, hG₀, Matrix.det_smul, Fintype.card_fin]
    intro h0
    rw [h0, Int.cast_zero] at e
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hN.ne')) hGdet e.symm
  choose C hC using fun k =>
    AlgebraInvolution.exists_dotProduct_mulVec_le_traceForm σ hpos b ((R k)ᵀ * G * R k)
  set Cmax : ℕ := ∑ k, C k
  obtain ⟨C₁, hC₁⟩ := exists_reduced_matrix n |G₀.det|
  set T : ℤ := N' ^ 2 * Cmax * C₁
  set 𝒮 : Set (Matrix (Fin n) (Fin n) ℤ) := {S | Sᵀ = S ∧
    (∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ S *ᵥ v) ∧ ∀ i j, |S i j| ≤ C₁}
  have h𝒮 : 𝒮.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Set.Icc (-C₁) C₁)
      fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _).subset ?_
    rintro S ⟨-, -, hS⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    exact fun i j => abs_le.1 (hS i j)
  set 𝒟 : Set (Matrix (Fin n) (Fin n) ℤ × (Fin n → Fin n → Fin n → ℤ)) :=
    ⋃ S ∈ 𝒮, {S} ×ˢ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => {v | v ⬝ᵥ S *ᵥ v ≤ T}
  have h𝒟 : 𝒟.Finite := h𝒮.biUnion fun S hS => (Set.finite_singleton S).prod
    (Set.Finite.pi fun _ => Set.Finite.pi fun _ =>
      finite_setOf_dotProduct_mulVec_le hS.1 hS.2.1 T)
  have key : ∀ g : σ.FiniteAdelicPoints, ∃ (B : Matrix (Fin n) (Fin n) ℚ) (r : ℚ)
      (S : Matrix (Fin n) (Fin n) ℤ) (M : Fin n → Matrix (Fin n) (Fin n) ℤ),
      IsReduction b g B r ∧ S.map (Int.cast : ℤ → ℚ) = ((N : ℚ) / r) • (Bᵀ * G * B) ∧
      (∀ k, (M k).map (Int.cast : ℤ → ℚ) = (N' : ℚ) • (B⁻¹ * R k * B)) ∧
      (S, fun k j i => M k i j) ∈ 𝒟 := by
    intro g
    obtain ⟨B₀, r, h₀⟩ := exists_isReduction b g
    obtain ⟨S₀, hS₀⟩ := Langlands.Global.RationalLattice.exists_int_of_isIntegral
      (h₀.isIntegral_map_smul_gram b hGint)
    have hsym₀ := transpose_eq_of_map_eq b hS₀
    have hpos₀ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ S₀ *ᵥ v := fun v hv =>
      h₀.dotProduct_pos b hpos hN hS₀ hv
    have hdet₀ : S₀.det ≤ |G₀.det| := by
      have hd := LinearAlgebra.Hermite.det_pos (Pi.basisFun ℤ (Fin n)) (isSymm_toBilin' hsym₀)
        (isPosDef_toBilin' hpos₀)
      rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at hd
      obtain ⟨z, hz⟩ := h₀.exists_det_eq b hS₀ hG₀ hd.ne'
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hz
        exact hG0 hz
      rw [hz, abs_mul, abs_of_pos hd]
      exact le_mul_of_one_le_left hd.le (Int.one_le_abs hz0)
    obtain ⟨P, Q, -, hQP, hP⟩ := hC₁ S₀ hsym₀ hpos₀ hdet₀
    have h := h₀.mul_right b hQP
    set B := B₀ * P.map (Int.cast : ℤ → ℚ) with hBdef
    obtain ⟨S, hS⟩ := Langlands.Global.RationalLattice.exists_int_of_isIntegral
      (h.isIntegral_map_smul_gram b hGint)
    have hSP : S = Pᵀ * S₀ * P := by
      apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
      change S.map (Int.cast : ℤ → ℚ) = (Pᵀ * S₀ * P).map (Int.cast : ℤ → ℚ)
      rw [hS, intCast_map_mul, intCast_map_mul, Matrix.transpose_map, hS₀, hBdef]
      simp only [Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have hpos' : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ S *ᵥ v := fun v hv =>
      h.dotProduct_pos b hpos hN hS hv
    choose M hM using fun k => Langlands.Global.RationalLattice.exists_int_of_isIntegral
      (h.isIntegral_map_smul_conj b (b k) (hRint k))
    refine ⟨B, r, S, M, h, hS, hM, ?_⟩
    have hSb : ∀ i j, |S i j| ≤ C₁ := fun i j => by
      rw [hSP]
      exact hP i j
    have hjj : ∀ j, 0 ≤ S j j := fun j => by
      have h1 := hpos' (Pi.single j 1) (by simp)
      rw [Matrix.mulVec_single_one, single_one_dotProduct] at h1
      exact h1.le
    have hcol : ∀ k j, (fun i => M k i j) ⬝ᵥ S *ᵥ (fun i => M k i j) ≤
        N' ^ 2 * (C k : ℤ) * S j j := by
      intro k j
      suffices hq : (((fun i => M k i j) ⬝ᵥ S *ᵥ (fun i => M k i j) : ℤ) : ℚ) ≤
          ((N' ^ 2 * (C k : ℤ) * S j j : ℤ) : ℚ) by exact_mod_cast hq
      rw [intCast_dotProduct_mulVec]
      have hv : (fun i => ((M k i j : ℤ) : ℚ)) =
          (N' : ℚ) • ((B⁻¹ * R k * B) *ᵥ Pi.single j 1) := by
        rw [← Matrix.smul_mulVec, ← hM k, Matrix.mulVec_single_one]
        rfl
      have hSjj : (S j j : ℚ) = (N : ℚ) / r *
          (Pi.single j 1 ⬝ᵥ (Bᵀ * G * B) *ᵥ Pi.single j 1) := by
        have e : S.map (Int.cast : ℤ → ℚ) j j = (((N : ℚ) / r) • (Bᵀ * G * B)) j j := by
          rw [hS]
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e
        rw [e, Matrix.mulVec_single_one, single_one_dotProduct]
        rfl
      rw [hv, hS]
      push_cast
      rw [hSjj]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      have hb := conj_dotProduct_le b (σ := σ) h.isUnit_det (R k) (hC k) (Pi.single j 1)
      have hnn : 0 ≤ (N' : ℚ) ^ 2 * ((N : ℚ) / r) :=
        mul_nonneg (sq_nonneg _) (div_nonneg (by exact_mod_cast hN.le) h.pos.le)
      have := mul_le_mul_of_nonneg_left hb hnn
      linarith
    refine Set.mem_biUnion (x := S) ⟨transpose_eq_of_map_eq b hS, hpos', hSb⟩ ?_
    refine ⟨Set.mem_singleton S, ?_⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
    intro k j
    have hCk : (C k : ℤ) ≤ Cmax := by
      exact_mod_cast Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ k)
    calc (fun i => M k i j) ⬝ᵥ S *ᵥ (fun i => M k i j) ≤ N' ^ 2 * (C k : ℤ) * S j j :=
          hcol k j
      _ ≤ N' ^ 2 * Cmax * C₁ := by
          have h1 : S j j ≤ C₁ := (le_abs_self _).trans (hSb j j)
          have h2 : 0 ≤ N' ^ 2 := sq_nonneg _
          have h3 : (0 : ℤ) ≤ C k := Int.natCast_nonneg _
          calc N' ^ 2 * (C k : ℤ) * S j j ≤ N' ^ 2 * Cmax * S j j :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCk h2) (hjj j)
            _ ≤ N' ^ 2 * Cmax * C₁ :=
                mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 (Int.natCast_nonneg _))
  choose B r S M hred hS hM hmem using key
  have := h𝒟.to_subtype
  let F : EquivariantForms.DoubleCosets σ.finiteAdelicDiagonal (latticeLevel σ b) → 𝒟 :=
    fun q => ⟨(S q.out, fun k j i => M q.out k i j), hmem q.out⟩
  refine Finite.of_injective F fun q q' hqq => ?_
  have e1 : S q.out = S q'.out := congrArg (fun x : 𝒟 => x.1.1) hqq
  have e2 : (fun k j i => M q.out k i j) = (fun k j i => M q'.out k i j) :=
    congrArg (fun x : 𝒟 => x.1.2) hqq
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hN'0 : (N' : ℚ) ≠ 0 := by exact_mod_cast hN'.ne'
  have hSq : (r q.out)⁻¹ • ((B q.out)ᵀ * G * B q.out) =
      (r q'.out)⁻¹ • ((B q'.out)ᵀ * G * B q'.out) := by
    have e3 : (S q.out).map (Int.cast : ℤ → ℚ) = (S q'.out).map (Int.cast : ℤ → ℚ) := by
      rw [e1]
    rw [hS, hS] at e3
    have e4 := congrArg (fun X : Matrix (Fin n) (Fin n) ℚ => (N : ℚ)⁻¹ • X) e3
    simp only [smul_smul] at e4
    rwa [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul, div_eq_mul_inv,
      ← mul_assoc, inv_mul_cancel₀ hN0, one_mul] at e4
  have hRq : ∀ k, (B q.out)⁻¹ * R k * B q.out = (B q'.out)⁻¹ * R k * B q'.out := by
    intro k
    have e3 : M q.out k = M q'.out k := by
      ext i j
      exact congrFun (congrFun (congrFun e2 k) j) i
    have e4 : (M q.out k).map (Int.cast : ℤ → ℚ) = (M q'.out k).map (Int.cast : ℤ → ℚ) := by
      rw [e3]
    rw [hM, hM] at e4
    exact smul_right_injective _ hN'0 e4
  calc q = DoubleCoset.mk σ.finiteAdelicDiagonal.range (latticeLevel σ b) q.out :=
        (DoubleCoset.out_eq' q).symm
    _ = DoubleCoset.mk σ.finiteAdelicDiagonal.range (latticeLevel σ b) q'.out :=
        mk_eq_of_isReduction b hpos (hred q.out) (hred q'.out) hSq hRq
    _ = q' := DoubleCoset.out_eq' q'

end Finite

end DefiniteDoubleCosets

end Langlands.Shimura
