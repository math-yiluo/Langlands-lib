import Langlands.GroupScheme.Quaternionic.KneserThreeCore
import Langlands.GroupScheme.Quaternionic.KneserThreeSplitting
import Langlands.GroupScheme.Quaternionic.Involution

/-!
# The exterior-square map: units, naturality and an invariant polar matrix

For a `Presentation A B`, the exterior-square map `cmap` of `KneserThreeCore` is natural in
compatible coefficient maps (`cmap_map`), gives a homomorphism into `3 × 3` unit matrices
(`cmapUnits`), and preserves `polarMatrix μ = [[0, 1, 0], [1, 0, 0], [0, 0, μ]]` for the conjugate
transpose of an involution `τ b = ℓ · bar b · ℓ⁻¹`, where `μ = -(ι θ · ℓ)`
(`cmap_mul_polarMatrix_mul_matrix`). The `QuatData` section specializes this to the base-changed
presentations of `KneserThreeSplitting` with constant parameters. `defect_mem_of_polar` converts
preservation of a polar matrix into the quadratic-form condition when `2` is invertible.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree

open Langlands.GroupScheme.Quaternionic

namespace Presentation

section Map

variable {A B A' B' : Type*} [CommRing A] [Ring B] [CommRing A'] [Ring B']
  (P : Presentation A B) (P' : Presentation A' B') {φA : A →+* A'} {φB : B →+* B'}

theorem map_elem (hι : ∀ a, φB (P.ι a) = P'.ι (φA a)) (hj : φB P.j = P'.j) (a a' : A) :
    φB (P.elem a a') = P'.elem (φA a) (φA a') := by
  simp [elem, hι, hj]

variable (hbar : ∀ a, φA (P.c.bar a) = P'.c.bar (φA a)) (hδ : φA P.δ = P'.δ)
include hbar hδ

theorem frame_map (θ l₁ l₂ : A) :
    (P.frame θ l₁ l₂).map φA = P'.frame (φA θ) (φA l₁) (φA l₂) := by
  ext r ⟨k, b⟩
  fin_cases r <;> fin_cases k <;> fin_cases b <;> simp [frame, hbar, hδ]

theorem frameInv_map (l₁ l₂ w : A) :
    (P.frameInv l₁ l₂ w).map φA = P'.frameInv (φA l₁) (φA l₂) (φA w) := by
  ext ⟨k, b⟩ r
  fin_cases r <;> fin_cases k <;> fin_cases b <;> simp [frameInv, hbar, hδ]

theorem adapted_map (θ l₁ l₂ w : A) (g : Matrix (Fin 4) (Fin 4) A) :
    (P.adapted θ l₁ l₂ w g).map φA =
      P'.adapted (φA θ) (φA l₁) (φA l₂) (φA w) (g.map φA) := by
  rw [adapted, adapted, Matrix.map_mul, Matrix.map_mul, P.frame_map P' hbar hδ,
    P.frameInv_map P' hbar hδ, ExteriorSquare.matrix_map]

/-- **Naturality of the exterior-square map** under compatible coefficient maps. -/
theorem cmap_map (hι : ∀ a, φB (P.ι a) = P'.ι (φA a)) (hj : φB P.j = P'.j)
    (θ l₁ l₂ w : A) (g : Matrix (Fin 4) (Fin 4) A) :
    (P.cmap θ l₁ l₂ w g).map φB =
      P'.cmap (φA θ) (φA l₁) (φA l₂) (φA w) (g.map φA) := by
  ext i k
  rw [Matrix.map_apply, cmap, cmap, Matrix.of_apply, Matrix.of_apply, P.map_elem P' hι hj,
    ← P.adapted_map P' hbar hδ]
  rfl

end Map

variable {A B : Type*} [CommRing A] [Ring B] (P : Presentation A B) {θ l₁ l₂ w : A}

section Units

variable (hθ : P.c.bar θ = -θ) (hw : w * (θ * (l₁ * P.c.bar l₁ - P.δ * l₂ * P.c.bar l₂)) = 1)

/-- The exterior-square map on a group of special unitary matrices, as a homomorphism to the
units of `M₃(B)`; the inverse of `cmap g` is `cmap g⁻¹`. -/
def cmapUnits {G : Type*} [Group G] (f : G →* (Matrix (Fin 4) (Fin 4) A)ˣ)
    (hf : ∀ g, P.IsSpecialUnitary (f g : Matrix (Fin 4) (Fin 4) A)) :
    G →* (Matrix (Fin 3) (Fin 3) B)ˣ where
  toFun g :=
    { val := P.cmap θ l₁ l₂ w (f g)
      inv := P.cmap θ l₁ l₂ w (f g⁻¹)
      val_inv := by
        rw [← P.cmap_mul hθ hw (hf g) (hf g⁻¹), ← Units.val_mul, ← map_mul, mul_inv_cancel,
          map_one, Units.val_one, P.cmap_one hθ hw]
      inv_val := by
        rw [← P.cmap_mul hθ hw (hf g⁻¹) (hf g), ← Units.val_mul, ← map_mul, inv_mul_cancel,
          map_one, Units.val_one, P.cmap_one hθ hw] }
  map_one' := Units.ext (by
    change P.cmap θ l₁ l₂ w (f 1) = 1
    rw [map_one, Units.val_one, P.cmap_one hθ hw])
  map_mul' g g' := Units.ext (by
    change P.cmap θ l₁ l₂ w (f (g * g')) = P.cmap θ l₁ l₂ w (f g) * P.cmap θ l₁ l₂ w (f g')
    rw [map_mul, Units.val_mul, P.cmap_mul hθ hw (hf g) (hf g')])

@[simp] theorem cmapUnits_val {G : Type*} [Group G] (f : G →* (Matrix (Fin 4) (Fin 4) A)ˣ)
    (hf : ∀ g, P.IsSpecialUnitary (f g : Matrix (Fin 4) (Fin 4) A)) (g : G) :
    (P.cmapUnits hθ hw f hf g : Matrix (Fin 3) (Fin 3) B) = P.cmap θ l₁ l₂ w (f g) := rfl

end Units

section Polar

/-- The matrix `[[0, 1, 0], [1, 0, 0], [0, 0, μ]]`. -/
def polarMatrix {B : Type*} [Ring B] (μ : B) : Matrix (Fin 3) (Fin 3) B :=
  !![0, 1, 0; 1, 0, 0; 0, 0, μ]

theorem elem_mul_self (hl : P.c.bar l₁ = -l₁) :
    P.elem l₁ l₂ * P.elem l₁ l₂ = P.ι (l₁ * l₁ + P.δ * P.c.bar l₂ * l₂) := by
  rw [elem_mul, hl, show -l₁ * l₂ + l₂ * l₁ = 0 by ring]
  simp [elem]

theorem skewHermitian_eq (hl : P.c.bar l₁ = -l₁) {μ : B}
    (hμ : μ = -(P.ι θ * P.elem l₁ l₂)) :
    P.skewHermitian θ l₁ l₂ =
      polarMatrix μ * Matrix.diagonal (fun _ => P.elem l₁ l₂) := by
  subst hμ
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [skewHermitian, polarMatrix, Matrix.mul_diagonal, kappa]
  rw [mul_assoc (P.ι θ), P.elem_mul_self hl, ← map_mul, ← map_neg]
  simp only [elem, map_zero, mul_zero, add_zero]

/-- **The polar form.** Let `τ` be an involution of the first kind of `B` (over a commutative
ring `S`) with `τ b = ℓ · bar b · ℓ⁻¹`, where `ℓ = elem l₁ l₂`, and let `μ = -θ ℓ`. Then for
special unitary `g`, `cmap g` preserves `polarMatrix μ` for the conjugate transpose of `τ`. -/
theorem cmap_mul_polarMatrix_mul_matrix {S : Type*} [CommRing S] [Algebra S B]
    (τ : FirstKindInvolution S B) (hθ : P.c.bar θ = -θ) (hl : P.c.bar l₁ = -l₁)
    (hw : w * (θ * (l₁ * P.c.bar l₁ - P.δ * l₂ * P.c.bar l₂)) = 1)
    {ℓinv : B} (hℓ : P.elem l₁ l₂ * ℓinv = 1)
    (hτ : ∀ b, τ b = P.elem l₁ l₂ * P.bar b * ℓinv)
    {μ : B} (hμ : μ = -(P.ι θ * P.elem l₁ l₂))
    {g : Matrix (Fin 4) (Fin 4) A} (hg : P.IsSpecialUnitary g) :
    P.cmap θ l₁ l₂ w g * polarMatrix μ * τ.matrix (Fin 3) (P.cmap θ l₁ l₂ w g) =
      polarMatrix μ := by
  set X := P.cmap θ l₁ l₂ w g
  set Dl : Matrix (Fin 3) (Fin 3) B := Matrix.diagonal (fun _ => P.elem l₁ l₂)
  set Dinv : Matrix (Fin 3) (Fin 3) B := Matrix.diagonal (fun _ => ℓinv)
  have hm : τ.matrix (Fin 3) X = Dl * P.conjTranspose X * Dinv := by
    ext i k
    simp [Dl, Dinv, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose, hτ]
  have hS := P.cmap_mul_skewHermitian_mul_conjTranspose hθ hl hw hg
  rw [P.skewHermitian_eq hl hμ] at hS
  have hD : Dl * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hℓ]
  calc X * polarMatrix μ * τ.matrix (Fin 3) X =
      X * (polarMatrix μ * Dl) * P.conjTranspose X * Dinv := by
        rw [hm]; simp only [Matrix.mul_assoc]
    _ = polarMatrix μ * (Dl * Dinv) := by rw [hS, Matrix.mul_assoc]
    _ = polarMatrix μ := by rw [hD, Matrix.mul_one]

end Polar

theorem bar_add (b b' : B) : P.bar (b + b') = P.bar b + P.bar b' := by
  apply P.ext <;> simp [map_add]; abel

theorem bar_zero : P.bar 0 = 0 := by
  apply P.ext <;> simp

end Presentation

namespace QuatData

open QuadField

variable {K D : Type u} [Field K] [Ring D] [Algebra K D] (Q : QuatData K D)

/-- The conjugation `ι a + j ι a' ↦ ι ā - j ι a'` of `D`. -/
def bar (d : D) : D :=
  Q.ι (SU3Root.conjugation K (field Q.c) (Q.fst d)) - Q.j * Q.ι (Q.snd d)

/-- The element `ι a + j ι a'` of `D`. -/
def elem (a a' : field Q.c) : D := Q.ι a + Q.j * Q.ι a'

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The constant `a ⊗ 1` of `L ⊗[K] R`. -/
abbrev const : field Q.c →ₐ[K] field Q.c ⊗[K] R := Algebra.TensorProduct.includeLeft

theorem presentation_bar_tmul (r : R) (d : D) :
    (Q.presentation R).bar (r ⊗ₜ[K] d) = r ⊗ₜ[K] Q.bar d := by
  change Q.ιR R ((Q.tensorInvolution R).bar (Q.fst d ⊗ₜ[K] r)) +
    Q.jR R * Q.ιR R (-(Q.snd d ⊗ₜ[K] r)) = _
  rw [tensorInvolution_tmul, ← TensorProduct.neg_tmul, ιR_tmul, ιR_tmul, jR,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, bar, map_neg,
    mul_neg, sub_eq_add_neg]

theorem presentation_elem_const (a a' : field Q.c) :
    (Q.presentation R).elem (Q.const R a) (Q.const R a') = (1 : R) ⊗ₜ[K] Q.elem a a' := by
  change Q.ιR R (a ⊗ₜ[K] 1) + Q.jR R * Q.ιR R (a' ⊗ₜ[K] 1) = _
  rw [ιR_tmul, ιR_tmul, jR, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.tmul_add, elem]

theorem presentation_ι_const (a : field Q.c) :
    (Q.presentation R).ι (Q.const R a) = (1 : R) ⊗ₜ[K] Q.ι a := by
  change Q.ιR R (a ⊗ₜ[K] 1) = _
  rw [ιR_tmul]

theorem presentation_bar_const (a : field Q.c) :
    (Q.presentation R).c.bar (Q.const R a) = Q.const R (SU3Root.conjugation K (field Q.c) a) :=
  rfl

theorem presentation_δ : (Q.presentation R).δ = Q.const R (algebraMap K (field Q.c) Q.δ) := by
  change algebraMap K (field Q.c ⊗[K] R) Q.δ = _
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem presentation_bar_const_neg {a : field Q.c} (ha : SU3Root.conjugation K (field Q.c) a = -a) :
    (Q.presentation R).c.bar (Q.const R a) = -Q.const R a := by
  rw [presentation_bar_const, ha, map_neg]

/-- The unit hypothesis of `Presentation.cmap` for constant parameters. -/
theorem presentation_unit_const {θ l₁ l₂ w : field Q.c}
    (hw : w * (θ * (l₁ * SU3Root.conjugation K (field Q.c) l₁ -
      algebraMap K (field Q.c) Q.δ * l₂ * SU3Root.conjugation K (field Q.c) l₂)) = 1) :
    Q.const R w * (Q.const R θ * (Q.const R l₁ * (Q.presentation R).c.bar (Q.const R l₁) -
      (Q.presentation R).δ * Q.const R l₂ * (Q.presentation R).c.bar (Q.const R l₂))) = 1 := by
  rw [presentation_bar_const, presentation_bar_const, presentation_δ, ← map_mul, ← map_mul,
    ← map_mul, ← map_sub, ← map_mul, ← map_mul, hw, map_one]

/-- Every coefficient map `L ⊗ R → L ⊗ R'` fixes the constants. -/
@[simp] theorem mapA_const {R' : Type u} [CommRing R'] [Algebra K R'] (φ : R →ₐ[K] R')
    (a : field Q.c) : Q.mapA φ (Q.const R a) = Q.const R' a := by
  simp

/-- Base change of an involution of the form `σ d = ℓ · bar d · ℓ⁻¹`. -/
theorem baseChange_eq (σ : FirstKindInvolution K D) {l₁ l₂ : field Q.c} {ℓinv : D}
    (hσ : ∀ d, σ d = Q.elem l₁ l₂ * Q.bar d * ℓinv) (b : R ⊗[K] D) :
    σ.baseChange R b = (Q.presentation R).elem (Q.const R l₁) (Q.const R l₂) *
      (Q.presentation R).bar b * ((1 : R) ⊗ₜ[K] ℓinv) := by
  induction b using TensorProduct.inductionOn with
  | tmul r d =>
    rw [FirstKindInvolution.baseChange_tmul, hσ, presentation_elem_const, presentation_bar_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | add b b' hb hb' =>
    rw [LinearMap.map_add, Presentation.bar_add, mul_add, add_mul, hb, hb']

variable {R}

/-- **The polar form over `R`.** Let `σ d = ℓ · bar d · ℓ⁻¹` with `ℓ = ι l₁ + j ι l₂`, and
`μ = -(ι θ · ℓ)`. For a special unitary `g` over `L ⊗[K] R`, `cmap g` preserves
`polarMatrix (1 ⊗ μ)` for the conjugate transpose of `σ ⊗ R`. -/
theorem cmap_mul_polarMatrix_mul_matrix (σ : FirstKindInvolution K D) {θ l₁ l₂ w : field Q.c}
    (hθ : SU3Root.conjugation K (field Q.c) θ = -θ)
    (hl : SU3Root.conjugation K (field Q.c) l₁ = -l₁)
    (hw : w * (θ * (l₁ * SU3Root.conjugation K (field Q.c) l₁ -
      algebraMap K (field Q.c) Q.δ * l₂ * SU3Root.conjugation K (field Q.c) l₂)) = 1)
    {ℓinv : D} (hℓ : Q.elem l₁ l₂ * ℓinv = 1) (hσ : ∀ d, σ d = Q.elem l₁ l₂ * Q.bar d * ℓinv)
    {g : Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] R)}
    (hg : (Q.presentation R).IsSpecialUnitary g) :
    (Q.presentation R).cmap (Q.const R θ) (Q.const R l₁) (Q.const R l₂) (Q.const R w) g *
        Presentation.polarMatrix ((1 : R) ⊗ₜ[K] (-(Q.ι θ * Q.elem l₁ l₂))) *
        (σ.baseChange R).matrix (Fin 3)
          ((Q.presentation R).cmap (Q.const R θ) (Q.const R l₁) (Q.const R l₂)
            (Q.const R w) g) =
      Presentation.polarMatrix ((1 : R) ⊗ₜ[K] (-(Q.ι θ * Q.elem l₁ l₂))) := by
  refine (Q.presentation R).cmap_mul_polarMatrix_mul_matrix (σ.baseChange R)
    (Q.presentation_bar_const_neg R hθ) (Q.presentation_bar_const_neg R hl)
    (Q.presentation_unit_const R hw) (ℓinv := (1 : R) ⊗ₜ[K] ℓinv) ?_
    (Q.baseChange_eq R σ hσ) ?_ hg
  · rw [presentation_elem_const, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hℓ,
      Algebra.TensorProduct.one_def]
  · rw [presentation_ι_const, presentation_elem_const, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, TensorProduct.tmul_neg]

end QuatData

/-- If `2` is invertible and `τ d = -d`, then `d` is alternating. -/
theorem mem_alternatingSubspace_of_neg {S M : Type*} [CommRing S] [Ring M] [Algebra S M]
    (τ : FirstKindInvolution S M) {h : S} (hh : 2 * h = 1) {d : M} (hd : τ d = -d) :
    d ∈ τ.alternatingSubspace := by
  refine τ.mem_alternatingSubspace.2 ⟨h • d, ?_⟩
  rw [τ.map_smul, hd, smul_neg, sub_neg_eq_add, ← add_smul, ← two_mul, hh, one_smul]

/-- If `X` preserves the polar form `Q + τ Q`, then the defect `X Q τ X - Q` is alternating
when `2` is invertible. -/
theorem defect_mem_of_polar {S M : Type*} [CommRing S] [Ring M] [Algebra S M]
    (τ : FirstKindInvolution S M) {h : S} (hh : 2 * h = 1) {Q X : M}
    (hX : X * (Q + τ Q) * τ X = Q + τ Q) :
    X * Q * τ X - Q ∈ τ.alternatingSubspace := by
  apply mem_alternatingSubspace_of_neg τ hh
  have h1 : τ (X * Q * τ X - Q) = X * τ Q * τ X - τ Q := by
    simp [mul_assoc]
  have h2 : X * τ Q * τ X = Q + τ Q - X * Q * τ X := by
    rw [← hX]; noncomm_ring
  rw [h1, h2]
  abel

end Langlands.GroupScheme.KneserThree
