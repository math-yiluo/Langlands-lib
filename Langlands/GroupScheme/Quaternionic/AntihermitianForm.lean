import Langlands.GroupScheme.Quaternionic.ScalarQuadratic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Abel

/-! # Antihermitian pairings and their nondegenerate lines -/

noncomputable section

universe u v w t

open Matrix

namespace Langlands.GroupScheme.Quaternionic

variable {F : Type u} {D : Type v} [Field F] [DivisionRing D] [Algebra F D]

/-- An antihermitian pairing on a left vector space over a division algebra. It is
linear in the first argument and conjugate-linear in the second. -/
structure AntihermitianForm (σ : FirstKindInvolution F D) (V : Type w)
    [AddCommGroup V] [Module D V] [Module F V] [IsScalarTower F D V] where
  toBilin : V →ₗ[F] V →ₗ[F] D
  smul_left' : ∀ (a : D) (x y : V), toBilin (a • x) y = a * toBilin x y
  skew' : ∀ x y : V, toBilin y x = -σ (toBilin x y)

namespace AntihermitianForm

variable {σ : FirstKindInvolution F D}
variable {V : Type w} [AddCommGroup V] [Module D V] [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm σ V)

instance : CoeFun (AntihermitianForm σ V) (fun _ => V → V → D) := ⟨fun B x y => B.toBilin x y⟩

@[simp] theorem add_left (x x' y : V) : B (x + x') y = B x y + B x' y := by
  change B.toBilin (x + x') y = _
  rw [map_add, LinearMap.add_apply]

@[simp] theorem add_right (x y y' : V) : B x (y + y') = B x y + B x y' :=
  (B.toBilin x).map_add y y'

@[simp] theorem sub_left (x x' y : V) : B (x - x') y = B x y - B x' y := by
  change B.toBilin (x - x') y = _
  rw [map_sub, LinearMap.sub_apply]

@[simp] theorem smul_left (a : D) (x y : V) : B (a • x) y = a * B x y := B.smul_left' a x y

theorem skew (x y : V) : B y x = -σ (B x y) := B.skew' x y

@[simp] theorem smul_right (a : D) (x y : V) : B x (a • y) = B x y * σ a := by
  rw [B.skew (a • y) x, B.smul_left, σ.map_mul, B.skew x y, σ.map_neg, σ.apply_apply,
    neg_mul, neg_neg]

@[simp] theorem zero_left (y : V) : B 0 y = 0 := by
  change B.toBilin 0 y = 0
  rw [map_zero, LinearMap.zero_apply]

@[simp] theorem zero_right (x : V) : B x 0 = 0 := (B.toBilin x).map_zero

/-- Pull an antihermitian form back along a division-linear map. -/
def pullback {W : Type t} [AddCommGroup W] [Module D W] [Module F W] [IsScalarTower F D W]
    (f : W →ₗ[D] V) : AntihermitianForm σ W where
  toBilin := B.toBilin.compl₁₂ (f.restrictScalars F) (f.restrictScalars F)
  smul_left' a x y := by
    change B (f (a • x)) (f y) = a * B (f x) (f y)
    rw [map_smul, B.smul_left]
  skew' x y := B.skew (f x) (f y)

@[simp] theorem pullback_apply {W : Type t} [AddCommGroup W] [Module D W] [Module F W]
    [IsScalarTower F D W] (f : W →ₗ[D] V) (x y : W) : B.pullback f x y = B (f x) (f y) := rfl

/-- The scalar quadratic form attached to the pairing and a linear functional on the algebra. -/
def scalarQuadratic (ℓ : D →ₗ[F] F) : QuadraticForm F V :=
  ℓ.compQuadraticMap' (LinearMap.BilinMap.toQuadraticMap B.toBilin)

@[simp] theorem scalarQuadratic_apply (ℓ : D →ₗ[F] F) (x : V) :
    B.scalarQuadratic ℓ x = ℓ (B x x) := rfl

@[simp] theorem polarBilin_scalarQuadratic (ℓ : D →ₗ[F] F) (x y : V) :
    (B.scalarQuadratic ℓ).polarBilin x y = ℓ (B x y - σ (B x y)) := by
  rw [scalarQuadratic, LinearMap.compQuadraticMap_polarBilin,
    LinearMap.BilinMap.polarBilin_toQuadraticMap]
  change ℓ (B x y + B y x) = _
  rw [B.skew x y, sub_eq_add_neg]

/-- A scalar coordinate detects radical vectors when it is nonzero on the alternating space. -/
theorem scalarQuadratic_nondegenerate (hB : B.toBilin.SeparatingLeft)
    (ℓ : D →ₗ[F] F) (hℓ : ∃ a, ℓ (a - σ a) ≠ 0) :
    (B.scalarQuadratic ℓ).polarBilin.Nondegenerate := by
  let Q := B.scalarQuadratic ℓ
  have hs : Q.polarBilin.IsSymm := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  apply hB x
  intro y
  by_contra hxy
  change B x y ≠ 0 at hxy
  obtain ⟨a, ha⟩ := hℓ
  have h := hx ((σ ((B x y)⁻¹ * a)) • y)
  change (B.scalarQuadratic ℓ).polarBilin x _ = 0 at h
  rw [polarBilin_scalarQuadratic, B.smul_right, σ.apply_apply, ← mul_assoc,
    mul_inv_cancel₀ hxy, one_mul] at h
  exact ha h

/-- Multiplication of a fixed vector by the division algebra, as a linear map. -/
def lineMap (x : V) : D →ₗ[D] V := (LinearMap.id : D →ₗ[D] D).smulRight x

@[simp] theorem lineMap_apply (x : V) (a : D) : lineMap x a = a • x := rfl

/-- The vectors orthogonal to the fixed vector `x` form a left division subspace. -/
def orthogonalLine (x : V) : Submodule D V :=
  LinearMap.ker
    ({ toFun := fun y => B y x
       map_add' := fun y z => B.add_left y z x
       map_smul' := fun a y => by
         simpa only [RingHom.id_apply, smul_eq_mul] using B.smul_left a y x } : V →ₗ[D] D)

@[simp] theorem mem_orthogonalLine (x y : V) : y ∈ B.orthogonalLine x ↔ B y x = 0 := Iff.rfl

/-- A nondegenerate line and its orthogonal complement split the pairing's domain. -/
def splitLine (x : V) (hx : B x x ≠ 0) : (D × B.orthogonalLine x) ≃ₗ[D] V where
  toFun p := p.1 • x + p.2
  invFun y := (B y x * (B x x)⁻¹, ⟨y - (B y x * (B x x)⁻¹) • x, by
    change B (y - (B y x * (B x x)⁻¹) • x) x = 0
    rw [B.sub_left, B.smul_left, mul_assoc, inv_mul_cancel₀ hx, mul_one, sub_self]⟩)
  left_inv p := by
    have h : B (p.1 • x + p.2) x = p.1 * B x x := by
      rw [B.add_left, B.smul_left, (B.mem_orthogonalLine x _).mp p.2.property, add_zero]
    have h' : B (p.1 • x + p.2) x * (B x x)⁻¹ = p.1 := by
      rw [h, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    refine Prod.ext h' (Subtype.ext ?_)
    change p.1 • x + (p.2 : V) - (B (p.1 • x + p.2) x * (B x x)⁻¹) • x = p.2
    rw [h']
    abel
  right_inv y := by
    change (B y x * (B x x)⁻¹) • x + (y - (B y x * (B x x)⁻¹) • x) = y
    abel
  map_add' p q := by
    change (p.1 + q.1) • x + ((p.2 : V) + q.2) = (p.1 • x + p.2) + (q.1 • x + q.2)
    rw [add_smul]
    abel
  map_smul' a p := by
    change (a * p.1) • x + a • (p.2 : V) = a • (p.1 • x + p.2)
    rw [smul_add, mul_smul]

@[simp] theorem splitLine_apply (x : V) (hx : B x x ≠ 0) (p : D × B.orthogonalLine x) :
    B.splitLine x hx p = p.1 • x + p.2 := rfl

theorem splitLine_pairing (x : V) (hx : B x x ≠ 0) (p q : D × B.orthogonalLine x) :
    B (B.splitLine x hx p) (B.splitLine x hx q) =
      p.1 * B x x * σ q.1 + B p.2 q.2 := by
  have hp := (B.mem_orthogonalLine x _).mp p.2.property
  have hq := (B.mem_orthogonalLine x _).mp q.2.property
  have hq' : B x q.2 = 0 := by rw [B.skew q.2 x, hq, σ.map_zero, neg_zero]
  simp only [splitLine_apply, add_left, add_right, smul_left, smul_right, hp, hq',
    mul_zero, zero_add, add_zero]

theorem orthogonalLine_separatingLeft (hB : B.toBilin.SeparatingLeft) (x : V) (hx : B x x ≠ 0) :
    (B.pullback (B.orthogonalLine x).subtype).toBilin.SeparatingLeft := by
  intro v hv
  apply Subtype.ext
  apply hB
  intro y
  obtain ⟨p, rfl⟩ := (B.splitLine x hx).surjective y
  have h : B v p.2 = 0 := hv p.2
  change B v (B.splitLine x hx p) = 0
  simp only [splitLine_apply, B.add_right, B.smul_right,
    (B.mem_orthogonalLine x _).mp v.property, zero_mul, h, add_zero]

/-- The scalar polar orthogonal complement of the entire division line equals its
antihermitian orthogonal complement. -/
theorem mem_orthogonalLine_iff_scalar (ℓ : D →ₗ[F] F) (hℓ : ∃ a, ℓ (a - σ a) ≠ 0)
    (x y : V) : y ∈ B.orthogonalLine x ↔ ∀ a : D, (B.scalarQuadratic ℓ).polarBilin y (a • x) = 0 := by
  rw [mem_orthogonalLine]
  constructor
  · intro h a
    rw [polarBilin_scalarQuadratic, B.smul_right, h, zero_mul, σ.map_zero, sub_self, map_zero]
  · intro h
    by_contra hy
    obtain ⟨a, ha⟩ := hℓ
    specialize h (σ ((B y x)⁻¹ * a))
    rw [polarBilin_scalarQuadratic, B.smul_right, σ.apply_apply, ← mul_assoc,
      mul_inv_cancel₀ hy, one_mul] at h
    exact ha h

section Matrix

variable {ι : Type w} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι D}

/-- An antihermitian Gram matrix gives an antihermitian pairing on its rows. -/
def ofMatrix (hH : σ.IsAntihermitian H) : AntihermitianForm σ (ι → D) where
  toBilin := σ.matrixSesqBilin H
  smul_left' a x y := σ.sesqForm_smul_left H a x y
  skew' x y := hH.sesqForm_swap σ x y

@[simp] theorem ofMatrix_apply (hH : σ.IsAntihermitian H) (x y : ι → D) :
    ofMatrix hH x y = σ.sesqForm H x y := rfl

@[simp] theorem scalarQuadratic_ofMatrix (hH : σ.IsAntihermitian H) (ℓ : D →ₗ[F] F) :
    (ofMatrix hH).scalarQuadratic ℓ = σ.scalarQuadratic ℓ H := rfl

/-- The row pairing of an invertible Gram matrix is left-separating. -/
theorem ofMatrix_separatingLeft (hH : σ.IsAntihermitian H) (hu : IsUnit H) :
    (ofMatrix hH).toBilin.SeparatingLeft := by
  intro x hx
  have h : x ᵥ* H = 0 := by
    ext i
    have hi := hx (Pi.single i 1)
    change σ.sesqForm H x (Pi.single i 1) = 0 at hi
    have hσ : σ ∘ (Pi.single i (1 : D) : ι → D) = Pi.single i 1 := by
      ext j
      by_cases h : j = i
      · subst j
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [σ.sesqForm_eq_dotProduct, dotProduct_mulVec, hσ, dotProduct_single, mul_one] at hi
    exact hi
  have hinv := congrArg (fun v => v ᵥ* (↑(hu.unit⁻¹) : Matrix ι ι D)) h
  simpa [Matrix.vecMul_vecMul, hu.mul_val_inv] using hinv

end Matrix

end AntihermitianForm

end Langlands.GroupScheme.Quaternionic
