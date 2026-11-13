import Langlands.GroupScheme.ExteriorSquareMatrix
import Langlands.GroupScheme.Quaternionic.KneserThreePresentation

/-!
# The exterior-square map `SU₄ → U₃` over a presented quaternion-type ring

Let `P : Presentation A B` present `B = ι(A) ⊕ j ι(A)` with `j² = δ`. On `A⁴` with basis
`(top, m₀, m₁, bot)` take the Hermitian Gram matrix `gram` (hyperbolic on `top, bot`,
`diag(1, -δ)` on `m₀, m₁`). For a special unitary `g`, the exterior square `Λ² g` on `A⁶`
commutes with the semilinear map `ξ ↦ Jm ξ̄`, which makes `A⁶` a free right `B`-module of rank
three. `cmap g` is the `3 × 3` matrix over `B` of `Λ² g` in the `B`-basis
`(e₀∧e₁, (θ bot∧m₀) ℓ, e₀∧e₃)`, where `ℓ = ι l₁ + j ι l₂` and `θ̄ = -θ`.

`cmap` is multiplicative on special unitary matrices and preserves the matrix `skewHermitian`
(`cmap g · skewHermitian · (cmap g)* = skewHermitian`, with `*` the conjugate transpose for the
conjugation `Presentation.bar`). When `θ̄ = -θ` and `l̄₁ = -l₁`, this matrix is skew-Hermitian
for `Presentation.bar`: `skewHermitian* = -skewHermitian` (`conjTranspose_skewHermitian`).
-/

namespace Langlands.GroupScheme.KneserThree

open SU3Root ExteriorSquare

variable {A B : Type*} [CommRing A] [Ring B] (P : Presentation A B)

namespace Presentation

/-- The Hermitian Gram matrix: hyperbolic on `top, bot`, `diag(1, -δ)` on `m₀, m₁`. -/
def gram : Matrix (Fin 4) (Fin 4) A := !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, -P.δ, 0; 1, 0, 0, 0]

/-- The conjugate transpose over `A`. -/
def conjT {m n : Type*} (M : Matrix m n A) : Matrix n m A := (M.map P.c.bar).transpose

/-- Special unitary matrices for `gram`. -/
def IsSpecialUnitary (g : Matrix (Fin 4) (Fin 4) A) : Prop :=
  P.conjT g * P.gram * g = P.gram ∧ g.det = 1

theorem conjT_mul {l m n : Type*} [Fintype m] (M : Matrix l m A) (N : Matrix m n A) :
    P.conjT (M * N) = P.conjT N * P.conjT M := by
  simp [conjT, Matrix.map_mul, Matrix.transpose_mul]

theorem IsSpecialUnitary.mul {g g' : Matrix (Fin 4) (Fin 4) A} (hg : P.IsSpecialUnitary g)
    (hg' : P.IsSpecialUnitary g') : P.IsSpecialUnitary (g * g') := by
  refine ⟨?_, by rw [Matrix.det_mul, hg.2, hg'.2, one_mul]⟩
  rw [conjT_mul]
  calc P.conjT g' * P.conjT g * P.gram * (g * g') =
        P.conjT g' * (P.conjT g * P.gram * g) * g' := by simp only [Matrix.mul_assoc]
    _ = P.gram := by rw [hg.1, hg'.1]

/-- The semilinear structure matrix `Jm = B · (Λ² gram)ᵀ` on `A⁶`. -/
def structureMatrix : Matrix (Fin 6) (Fin 6) A := pfaffian * (ExteriorSquare.matrix P.gram).transpose

/-- `Λ² g` commutes with the semilinear structure `ξ ↦ Jm ξ̄` for special unitary `g`. -/
theorem matrix_mul_structureMatrix {g : Matrix (Fin 4) (Fin 4) A} (hg : P.IsSpecialUnitary g) :
    ExteriorSquare.matrix g * P.structureMatrix =
      P.structureMatrix * (ExteriorSquare.matrix g).map P.c.bar := by
  set X := ExteriorSquare.matrix g
  set Γ := ExteriorSquare.matrix P.gram
  have hu : X.transpose * Γ.transpose * X.map P.c.bar = Γ.transpose := by
    have hm : ExteriorSquare.matrix (g.map P.c.bar) = X.map P.c.bar :=
      ExteriorSquare.matrix_map (P.c.bar : A →+* A) g
    have h := congrArg ExteriorSquare.matrix hg.1
    simp only [ExteriorSquare.matrix_mul, conjT, ExteriorSquare.matrix_transpose, hm] at h
    have h' := congrArg Matrix.transpose h
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h'
  have hd : X * pfaffian * X.transpose = pfaffian := by
    rw [mul_pfaffian_mul_transpose, hg.2, one_smul]
  calc X * P.structureMatrix = X * pfaffian * (X.transpose * Γ.transpose * X.map P.c.bar) := by
        rw [hu, structureMatrix, Matrix.mul_assoc]
    _ = (X * pfaffian * X.transpose) * Γ.transpose * X.map P.c.bar := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hd, structureMatrix]

theorem isSpecialUnitary_one : P.IsSpecialUnitary 1 := by
  refine ⟨?_, Matrix.det_one⟩
  simp [conjT]

variable (θ l₁ l₂ w : A)

/-- The `A`-basis `(B₁, B₁ j, B₂, B₂ j, B₃, B₃ j)` of `A⁶` in standard coordinates, where
`B₁ = e₀∧e₁`, `B₂ = (θ · e₃∧e₁) ℓ` with `ℓ = ι l₁ + j ι l₂`, and `B₃ = e₀∧e₃`. -/
def frame : Matrix (Fin 6) (Fin 3 × Fin 2) A :=
  Matrix.of fun r p =>
    (![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]],
      ![![0, 0, 0, 0, -(θ * l₁), -(θ * l₂)],
        ![0, 0, 0, 0, -(P.δ * θ * P.c.bar l₂), -(θ * P.c.bar l₁)]],
      ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0]]] : Fin 3 → Fin 2 → Fin 6 → A) p.1 p.2 r

/-- The inverse of `frame`, given `w θ (l₁ l̄₁ - δ l₂ l̄₂) = 1`. -/
def frameInv : Matrix (Fin 3 × Fin 2) (Fin 6) A :=
  Matrix.of fun p r =>
    (![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]],
      ![![0, 0, 0, 0, -(w * P.c.bar l₁), w * P.δ * P.c.bar l₂],
        ![0, 0, 0, 0, w * l₂, -(w * l₁)]],
      ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0]]] : Fin 3 → Fin 2 → Fin 6 → A) p.1 p.2 r

/-- The standard semilinear structure: `e_{i,0} ↦ e_{i,1}`, `e_{i,1} ↦ δ e_{i,0}`. -/
def standardStructure : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) A :=
  Matrix.of fun p q => if p.1 = q.1 then (!![0, P.δ; 1, 0] : Matrix (Fin 2) (Fin 2) A) p.2 q.2
    else 0

variable {θ l₁ l₂ w}

theorem frame_mul_frameInv (hw : w * (θ * (l₁ * P.c.bar l₁ - P.δ * l₂ * P.c.bar l₂)) = 1) :
    P.frame θ l₁ l₂ * P.frameInv l₁ l₂ w = 1 := by
  ext r r'
  fin_cases r <;> fin_cases r' <;>
    simp [frame, frameInv, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
      Fin.sum_univ_two] <;> first | ring1 | linear_combination hw

theorem frameInv_mul_frame (hw : w * (θ * (l₁ * P.c.bar l₁ - P.δ * l₂ * P.c.bar l₂)) = 1) :
    P.frameInv l₁ l₂ w * P.frame θ l₁ l₂ = 1 := by
  ext ⟨i, a⟩ ⟨k, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases k <;> fin_cases b <;>
    simp [frame, frameInv, Matrix.mul_apply, Fin.sum_univ_six] <;>
    first | ring1 | linear_combination hw

/-- The structure matrix in coordinates. -/
theorem structureMatrix_eq : P.structureMatrix =
    !![0, P.δ, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, -P.δ, 0, 0; 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, -P.δ; 0, 0, 0, 0, -1, 0] := by
  ext i k
  simp only [structureMatrix, Matrix.mul_apply, Fin.sum_univ_six, Matrix.transpose_apply]
  fin_cases i <;> fin_cases k <;>
    simp [pfaffian, ExteriorSquare.matrix_apply, ExteriorSquare.pair, gram]

theorem frame_mul_standardStructure (hθ : P.c.bar θ = -θ) :
    P.frame θ l₁ l₂ * P.standardStructure =
      P.structureMatrix * (P.frame θ l₁ l₂).map P.c.bar := by
  rw [structureMatrix_eq]
  ext r ⟨k, b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_six, Fin.sum_univ_three,
    Fin.sum_univ_two, Matrix.map_apply]
  fin_cases r <;> fin_cases k <;> fin_cases b <;>
    simp [frame, standardStructure, hθ, P.bar_δ] <;> ring

variable (θ l₁ l₂ w) in
/-- `Λ² g` in the adapted basis `frame`. -/
def adapted (g : Matrix (Fin 4) (Fin 4) A) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) A :=
  P.frameInv l₁ l₂ w * ExteriorSquare.matrix g * P.frame θ l₁ l₂

variable (θ l₁ l₂ w) in
/-- **The exterior-square map.** The `3 × 3` matrix over `B` of `Λ² g` in the `B`-basis
`(B₁, B₂, B₃)`: its `(i, k)` entry is `ι a + j ι c`, where `(a, c)` are the `(B_i, B_i j)`
coordinates of `Λ² g (B_k)`. -/
def cmap (g : Matrix (Fin 4) (Fin 4) A) : Matrix (Fin 3) (Fin 3) B :=
  Matrix.of fun i k =>
    P.elem (P.adapted θ l₁ l₂ w g (i, 0) (k, 0)) (P.adapted θ l₁ l₂ w g (i, 1) (k, 0))

section Hypotheses

variable (hθ : P.c.bar θ = -θ) (hw : w * (θ * (l₁ * P.c.bar l₁ - P.δ * l₂ * P.c.bar l₂)) = 1)
include hw

theorem adapted_mul (g g' : Matrix (Fin 4) (Fin 4) A) :
    P.adapted θ l₁ l₂ w (g * g') = P.adapted θ l₁ l₂ w g * P.adapted θ l₁ l₂ w g' := by
  simp only [adapted, ExteriorSquare.matrix_mul]
  calc P.frameInv l₁ l₂ w * (ExteriorSquare.matrix g * ExteriorSquare.matrix g') *
        P.frame θ l₁ l₂ =
      P.frameInv l₁ l₂ w * ExteriorSquare.matrix g * (P.frame θ l₁ l₂ * P.frameInv l₁ l₂ w) *
        ExteriorSquare.matrix g' * P.frame θ l₁ l₂ := by
        rw [P.frame_mul_frameInv hw]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem adapted_one : P.adapted θ l₁ l₂ w 1 = 1 := by
  rw [adapted, ExteriorSquare.matrix_one, Matrix.mul_one, P.frameInv_mul_frame hw]

include hθ in
theorem frameInv_mul_structureMatrix :
    P.frameInv l₁ l₂ w * P.structureMatrix =
      P.standardStructure * (P.frameInv l₁ l₂ w).map P.c.bar := by
  have h1 := P.frame_mul_standardStructure (l₁ := l₁) (l₂ := l₂) hθ
  have h2 : (P.frame θ l₁ l₂).map P.c.bar * (P.frameInv l₁ l₂ w).map P.c.bar = 1 := by
    rw [← Matrix.map_mul, P.frame_mul_frameInv hw, Matrix.map_one _ (map_zero _) (map_one _)]
  calc P.frameInv l₁ l₂ w * P.structureMatrix =
      P.frameInv l₁ l₂ w * P.structureMatrix * ((P.frame θ l₁ l₂).map P.c.bar *
        (P.frameInv l₁ l₂ w).map P.c.bar) := by rw [h2, Matrix.mul_one]
    _ = P.frameInv l₁ l₂ w * (P.structureMatrix * (P.frame θ l₁ l₂).map P.c.bar) *
        (P.frameInv l₁ l₂ w).map P.c.bar := by simp only [Matrix.mul_assoc]
    _ = (P.frameInv l₁ l₂ w * P.frame θ l₁ l₂) * P.standardStructure *
        (P.frameInv l₁ l₂ w).map P.c.bar := by rw [← h1]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [P.frameInv_mul_frame hw, Matrix.one_mul]

include hθ in
/-- For special unitary `g`, the adapted matrix commutes with the standard structure. -/
theorem adapted_mul_standardStructure {g : Matrix (Fin 4) (Fin 4) A}
    (hg : P.IsSpecialUnitary g) :
    P.adapted θ l₁ l₂ w g * P.standardStructure =
      P.standardStructure * (P.adapted θ l₁ l₂ w g).map P.c.bar := by
  have hP := P.frame_mul_standardStructure (l₁ := l₁) (l₂ := l₂) hθ
  have hI := P.frameInv_mul_structureMatrix hθ hw
  have hX := P.matrix_mul_structureMatrix hg
  simp only [adapted, Matrix.map_mul]
  calc P.frameInv l₁ l₂ w * ExteriorSquare.matrix g * P.frame θ l₁ l₂ * P.standardStructure =
      P.frameInv l₁ l₂ w * (ExteriorSquare.matrix g * P.structureMatrix) *
        (P.frame θ l₁ l₂).map P.c.bar := by rw [Matrix.mul_assoc _ _ P.standardStructure, hP]; simp only [Matrix.mul_assoc]
    _ = (P.frameInv l₁ l₂ w * P.structureMatrix) * (ExteriorSquare.matrix g).map P.c.bar *
        (P.frame θ l₁ l₂).map P.c.bar := by rw [hX]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hI]; simp only [Matrix.mul_assoc]

include hθ in
/-- The `rep`-blocks of `cmap g` are the adapted matrix. -/
theorem block_cmap {g : Matrix (Fin 4) (Fin 4) A} (hg : P.IsSpecialUnitary g) :
    P.block (P.cmap θ l₁ l₂ w g) = P.adapted θ l₁ l₂ w g := by
  have h := P.adapted_mul_standardStructure hθ hw hg
  set N := P.adapted θ l₁ l₂ w g
  ext ⟨i, a⟩ ⟨k, b⟩
  have h0 := congrFun (congrFun h (i, 0)) (k, 0)
  have h1 := congrFun (congrFun h (i, 1)) (k, 0)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, standardStructure,
    Matrix.of_apply, Matrix.map_apply] at h0 h1
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0 h1
  simp at h0 h1
  fin_cases a <;> fin_cases b <;>
    simp [block_apply, cmap, rep, N] <;> first | exact h0.symm | exact h1.symm

include hθ in
/-- **Multiplicativity.** -/
theorem cmap_mul {g g' : Matrix (Fin 4) (Fin 4) A} (hg : P.IsSpecialUnitary g)
    (hg' : P.IsSpecialUnitary g') :
    P.cmap θ l₁ l₂ w (g * g') = P.cmap θ l₁ l₂ w g * P.cmap θ l₁ l₂ w g' := by
  apply P.block_injective
  rw [P.block_mul, P.block_cmap hθ hw (hg.mul P hg'), P.block_cmap hθ hw hg,
    P.block_cmap hθ hw hg', P.adapted_mul hw]

include hθ in
theorem cmap_one : P.cmap θ l₁ l₂ w 1 = 1 := by
  apply P.block_injective
  rw [P.block_cmap hθ hw P.isSpecialUnitary_one, P.adapted_one hw, P.block_one]

end Hypotheses

variable (θ l₁ l₂) in
/-- The scalar `κ = θ ℓ²` with `ℓ² = l₁² + δ l̄₂ l₂`. -/
def kappa : A := θ * (l₁ * l₁ + P.δ * P.c.bar l₂ * l₂)

variable (θ l₁ l₂) in
/-- The matrix `[[0, ℓ, 0], [ℓ, 0, 0], [0, 0, -θ ℓ²]]` preserved by `cmap`. It is skew-Hermitian
for `Presentation.bar` when `θ̄ = -θ` and `l̄₁ = -l₁` (`conjTranspose_skewHermitian`). -/
def skewHermitian : Matrix (Fin 3) (Fin 3) B :=
  !![0, P.elem l₁ l₂, 0; P.elem l₁ l₂, 0, 0; 0, 0, P.elem (-P.kappa θ l₁ l₂) 0]

variable (θ l₁ l₂) in
/-- `block skewHermitian * blockSymplectic` in coordinates. -/
def skewHermitianSymplectic : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) A :=
  Matrix.of fun p q =>
    if (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ q.1 = 0) then
      (!![-(P.δ * P.c.bar l₂), l₁; -P.c.bar l₁, l₂] : Matrix (Fin 2) (Fin 2) A) p.2 q.2
    else if p.1 = 2 ∧ q.1 = 2 then
      (!![0, -P.kappa θ l₁ l₂; -P.kappa θ l₁ l₂, 0] : Matrix (Fin 2) (Fin 2) A) p.2 q.2
    else 0

/-- `skewHermitian` is skew-Hermitian for `Presentation.bar`: `skewHermitian* = -skewHermitian`. -/
theorem conjTranspose_skewHermitian (hθ : P.c.bar θ = -θ) (hl : P.c.bar l₁ = -l₁) :
    P.conjTranspose (P.skewHermitian θ l₁ l₂) = -P.skewHermitian θ l₁ l₂ := by
  ext i k
  fin_cases i <;> fin_cases k <;> apply P.ext <;>
    simp [conjTranspose, skewHermitian, kappa, hθ, hl, P.bar_δ] <;> ring

theorem block_skewHermitian_mul_blockSymplectic (hθ : P.c.bar θ = -θ) (hl : P.c.bar l₁ = -l₁) :
    P.block (P.skewHermitian θ l₁ l₂) * blockSymplectic = P.skewHermitianSymplectic θ l₁ l₂ := by
  ext ⟨i, a⟩ ⟨k, b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases a <;> fin_cases k <;> fin_cases b <;>
    simp [block_apply, rep, skewHermitian, skewHermitianSymplectic, blockSymplectic, symplectic,
      kappa, hθ, hl, P.bar_δ] <;> ring

theorem frame_mul_skewHermitianSymplectic_mul_transpose (hl : P.c.bar l₁ = -l₁) :
    P.frame θ l₁ l₂ * P.skewHermitianSymplectic θ l₁ l₂ * (P.frame θ l₁ l₂).transpose =
      P.kappa θ l₁ l₂ • pfaffian := by
  ext r r'
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.smul_apply]
  fin_cases r <;> fin_cases r' <;>
    simp [frame, skewHermitianSymplectic, pfaffian, kappa, hl] <;> ring

/-- **Preservation of the skew-Hermitian matrix.** For special unitary `g`,
`cmap g · skewHermitian · (cmap g)* = skewHermitian`. -/
theorem cmap_mul_skewHermitian_mul_conjTranspose (hθ : P.c.bar θ = -θ) (hl : P.c.bar l₁ = -l₁)
    (hw : w * (θ * (l₁ * P.c.bar l₁ - P.δ * l₂ * P.c.bar l₂)) = 1)
    {g : Matrix (Fin 4) (Fin 4) A} (hg : P.IsSpecialUnitary g) :
    P.cmap θ l₁ l₂ w g * P.skewHermitian θ l₁ l₂ * P.conjTranspose (P.cmap θ l₁ l₂ w g) =
      P.skewHermitian θ l₁ l₂ := by
  apply P.block_injective
  set C := P.cmap θ l₁ l₂ w g
  set N := P.adapted θ l₁ l₂ w g
  set M := P.skewHermitianSymplectic θ l₁ l₂
  set S : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) A := blockSymplectic
  set X := ExteriorSquare.matrix g
  have hC : P.block C = N := P.block_cmap hθ hw hg
  have hSS : S * S = -1 := blockSymplectic_mul_self
  have hstar : P.block (P.conjTranspose C) = -(S * N.transpose * S) := by
    have h := P.block_conjTranspose_mul C
    rw [hC] at h
    calc P.block (P.conjTranspose C) = -(P.block (P.conjTranspose C) * (S * S)) := by
          rw [hSS]; simp
      _ = -(S * N.transpose * S) := by rw [← Matrix.mul_assoc, h]
  have hH : P.block (P.skewHermitian θ l₁ l₂) * S = M :=
    P.block_skewHermitian_mul_blockSymplectic hθ hl
  have hF := P.frame_mul_skewHermitianSymplectic_mul_transpose (θ := θ) (l₂ := l₂) hl
  have hFI := P.frameInv_mul_frame (θ := θ) hw
  have hd : X * pfaffian * X.transpose = pfaffian := by
    rw [mul_pfaffian_mul_transpose, hg.2, one_smul]
  have hNM : N * M * N.transpose = M := by
    have hM : M = P.frameInv l₁ l₂ w * (P.kappa θ l₁ l₂ • pfaffian) *
        (P.frameInv l₁ l₂ w).transpose := by
      rw [← hF]
      calc M = (P.frameInv l₁ l₂ w * P.frame θ l₁ l₂) * M *
            (P.frameInv l₁ l₂ w * P.frame θ l₁ l₂).transpose := by
            rw [hFI, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
        _ = _ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]; rfl
    calc N * M * N.transpose =
        P.frameInv l₁ l₂ w * X * (P.frame θ l₁ l₂ * M * (P.frame θ l₁ l₂).transpose) *
          X.transpose * (P.frameInv l₁ l₂ w).transpose := by
          simp only [N, adapted, Matrix.transpose_mul, Matrix.mul_assoc]; rfl
      _ = P.frameInv l₁ l₂ w * (P.kappa θ l₁ l₂ • (X * pfaffian * X.transpose)) *
          (P.frameInv l₁ l₂ w).transpose := by
          rw [hF]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = M := by rw [hd, hM]
  rw [P.block_mul, P.block_mul, hC, hstar]
  calc N * P.block (P.skewHermitian θ l₁ l₂) * -(S * N.transpose * S) =
      -((N * (P.block (P.skewHermitian θ l₁ l₂) * S) * N.transpose) * S) := by
        simp only [Matrix.mul_neg, Matrix.mul_assoc]
    _ = P.block (P.skewHermitian θ l₁ l₂) := by
        rw [hH, hNM, ← hH, Matrix.mul_assoc, hSS]; simp

/-! ### The binary group -/

theorem cmap_eq_of_adapted_eq_block {g : Matrix (Fin 4) (Fin 4) A} {Z : Matrix (Fin 3) (Fin 3) B}
    (h : P.adapted θ l₁ l₂ w g = P.block Z) : P.cmap θ l₁ l₂ w g = Z := by
  ext i k
  simp only [cmap, Matrix.of_apply, h, block_apply, rep]
  simp [P.elem_fst_snd]

variable (θ) in
/-- The binary embedding: `g ∈ SL₂` on `top, bot` twisted by `diag(1, θ)`, and `rep b` on
`m₀, m₁`. -/
def binary (θinv : A) (g : Matrix (Fin 2) (Fin 2) A) (b : B) : Matrix (Fin 4) (Fin 4) A :=
  !![g 0 0, 0, 0, g 0 1 * θinv; 0, P.fst b, P.δ * P.c.bar (P.snd b), 0;
    0, P.snd b, P.c.bar (P.fst b), 0; θ * g 1 0, 0, 0, g 1 1]

/-- The product `(g_{ik} b)` on the first two coordinates, `1` on the third. -/
def product (g : Matrix (Fin 2) (Fin 2) A) (b : B) : Matrix (Fin 3) (Fin 3) B :=
  !![P.ι (g 0 0) * b, P.ι (g 0 1) * b, 0; P.ι (g 1 0) * b, P.ι (g 1 1) * b, 0; 0, 0, 1]

variable (l₁ l₂) in
/-- `diag(1, ℓ, 1)`. -/
def twist : Matrix (Fin 3) (Fin 3) B := !![1, 0, 0; 0, P.elem l₁ l₂, 0; 0, 0, 1]

theorem frame_eq_mul_block_twist :
    P.frame θ l₁ l₂ = P.frame θ 1 0 * P.block (P.twist l₁ l₂) := by
  ext r ⟨k, b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases r <;> fin_cases k <;> fin_cases b <;>
    simp [frame, block_apply, twist, rep] <;> ring

theorem matrix_binary_mul_frame {θinv : A} (hθinv : θ * θinv = 1)
    {g : Matrix (Fin 2) (Fin 2) A} (hg : ∀ i k, P.c.bar (g i k) = g i k) (hdet : g.det = 1)
    {b : B} (hb : P.fst b * P.c.bar (P.fst b) - P.δ * P.snd b * P.c.bar (P.snd b) = 1) :
    ExteriorSquare.matrix (P.binary θ θinv g b) * P.frame θ 1 0 =
      P.frame θ 1 0 * P.block (P.product g b) := by
  rw [Matrix.det_fin_two] at hdet
  ext r ⟨k, c⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
    Fin.sum_univ_six]
  fin_cases r <;> fin_cases k <;> fin_cases c <;>
    simp [frame, block_apply, product, rep, binary, ExteriorSquare.matrix_apply,
      ExteriorSquare.pair, hg] <;>
    first
    | ring1
    | linear_combination (g 0 1 * P.fst b) * hθinv
    | linear_combination (g 0 1 * P.δ * P.c.bar (P.snd b)) * hθinv
    | linear_combination (g 0 1 * P.snd b) * hθinv
    | linear_combination (g 0 1 * P.c.bar (P.fst b)) * hθinv
    | linear_combination hdet - (g 0 1 * g 1 0) * hθinv
    | linear_combination -hb

/-- `diag(1, ℓ⁻¹, 1)` for a supplied inverse `ℓ⁻¹`. -/
def twistInv (linv : B) : Matrix (Fin 3) (Fin 3) B := !![1, 0, 0; 0, linv, 0; 0, 0, 1]

theorem twist_mul_twistInv {linv : B} (h : P.elem l₁ l₂ * linv = 1) :
    P.twist l₁ l₂ * twistInv linv = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [twist, twistInv, Matrix.mul_apply, Fin.sum_univ_three, h]

/-- **The binary group.** The exterior-square map sends the binary embedding of `(g, b)` to
`diag(1, ℓ⁻¹, 1) · product g b · diag(1, ℓ, 1)`. -/
theorem cmap_binary (hw : w * (θ * (l₁ * P.c.bar l₁ - P.δ * l₂ * P.c.bar l₂)) = 1)
    {θinv : A} (hθinv : θ * θinv = 1)
    {g : Matrix (Fin 2) (Fin 2) A} (hg : ∀ i k, P.c.bar (g i k) = g i k) (hdet : g.det = 1)
    {b : B} (hb : P.fst b * P.c.bar (P.fst b) - P.δ * P.snd b * P.c.bar (P.snd b) = 1)
    {linv : B} (hl : P.elem l₁ l₂ * linv = 1) :
    P.cmap θ l₁ l₂ w (P.binary θ θinv g b) =
      twistInv linv * P.product g b * P.twist l₁ l₂ := by
  apply P.cmap_eq_of_adapted_eq_block
  have hT : P.block (P.twist l₁ l₂) * P.block (twistInv linv) = 1 := by
    rw [← P.block_mul, P.twist_mul_twistInv hl, P.block_one]
  have hFI : P.frameInv l₁ l₂ w * P.frame θ 1 0 = P.block (twistInv linv) := by
    have h := P.frameInv_mul_frame hw
    rw [P.frame_eq_mul_block_twist] at h
    calc P.frameInv l₁ l₂ w * P.frame θ 1 0 =
        P.frameInv l₁ l₂ w * P.frame θ 1 0 * (P.block (P.twist l₁ l₂) *
          P.block (twistInv linv)) := by rw [hT, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, Matrix.mul_assoc _ (P.frame θ 1 0), h, Matrix.one_mul]
  rw [adapted, P.frame_eq_mul_block_twist, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (P.frame θ 1 0),
    P.matrix_binary_mul_frame hθinv hg hdet hb, ← Matrix.mul_assoc, hFI, P.block_mul, P.block_mul]

end Presentation

end Langlands.GroupScheme.KneserThree
