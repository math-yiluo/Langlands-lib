import Langlands.Theta.Heisenberg.Representation
import Langlands.HarmonicAnalysis.AdditiveCharacterExists
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The Schrödinger representation of a polarization

For a pairing `β : X →ₗ[R] Y →ₗ[R] R` the module `X × Y` carries the alternating form
`polarizedForm β ((x, y), (x', y')) = β x y' - β x' y`, for which `X × 0` and `0 × Y` are
complementary isotropic submodules. For an additive character `ψ` of `R` the operators

`schrodingerFun ψ β (x₀, y₀) φ x = ψ (β x y₀ + ⅟2 * β x₀ y₀) * φ (x + x₀)`

on functions `X → ℂ` satisfy `S(w) S(w') = ψ(⅟2 · polarizedForm β w w') S(w + w')`, so that
`(w, t) ↦ ψ t • S(w)` is a representation `schrodinger ψ β` of the Heisenberg group of
`polarizedForm β`, with central character `ψ`. For continuous `ψ` on a nonarchimedean ring and
continuous `x ↦ β x y`, the operators preserve the Schwartz–Bruhat functions
(`schrodingerSB`).
-/

noncomputable section

namespace Langlands.HeisenbergGroup

universe u v w

variable {R : Type u} [CommRing R]

variable {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- The alternating form `((x, y), (x', y')) ↦ β x y' - β x' y` on `X × Y`. -/
def polarizedForm (β : X →ₗ[R] Y →ₗ[R] R) : LinearMap.BilinForm R (X × Y) :=
  LinearMap.mk₂ R (fun w w' => β w.1 w'.2 - β w'.1 w.2)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- `polarizedForm β ((x, y), (x', y')) = β x y' - β x' y`. -/
@[simp] theorem polarizedForm_apply (β : X →ₗ[R] Y →ₗ[R] R) (w w' : X × Y) :
    polarizedForm β w w' = β w.1 w'.2 - β w'.1 w.2 := rfl

/-- The polarized form is alternating. -/
theorem polarizedForm_isAlt (β : X →ₗ[R] Y →ₗ[R] R) : (polarizedForm β).IsAlt :=
  fun w => by simp

variable [Invertible (2 : R)]

/-- The Schrödinger operator of `w = (x₀, y₀)` on functions on `X`:
`φ ↦ (x ↦ ψ (β x y₀ + ⅟2 * β x₀ y₀) * φ (x + x₀))`. -/
def schrodingerFun (ψ : AddChar R ℂ) (β : X →ₗ[R] Y →ₗ[R] R) (w : X × Y) (φ : X → ℂ) : X → ℂ :=
  fun x => ψ (β x w.2 + ⅟2 * β w.1 w.2) * φ (x + w.1)

variable (ψ : AddChar R ℂ) (β : X →ₗ[R] Y →ₗ[R] R)

/-- The value of the Schrödinger operator. -/
@[simp] theorem schrodingerFun_apply (w : X × Y) (φ : X → ℂ) (x : X) :
    schrodingerFun ψ β w φ x = ψ (β x w.2 + ⅟2 * β w.1 w.2) * φ (x + w.1) := rfl

/-- The Schrödinger operator of `0` is the identity. -/
@[simp] theorem schrodingerFun_zero (φ : X → ℂ) : schrodingerFun ψ β 0 φ = φ := by
  funext x; simp

/-- The Schrödinger operators form a projective representation of `X × Y` with cocycle
`ψ (⅟2 * polarizedForm β w w')`. -/
theorem schrodingerFun_comp (w w' : X × Y) (φ : X → ℂ) :
    schrodingerFun ψ β w (schrodingerFun ψ β w' φ) =
      ψ (⅟2 * polarizedForm β w w') • schrodingerFun ψ β (w + w') φ := by
  have h2 : (⅟2 : R) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  funext x
  simp only [schrodingerFun_apply, Pi.smul_apply, smul_eq_mul, polarizedForm_apply, Prod.fst_add,
    Prod.snd_add, add_assoc]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [map_add, LinearMap.add_apply]
  linear_combination (-β w.1 w'.2) * h2

/-- The Schrödinger operator of `w` as a linear map. -/
def schrodingerLinear (w : X × Y) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun := schrodingerFun ψ β w
  map_add' φ φ' := by funext x; simp [mul_add]
  map_smul' c φ := by funext x; simp; ring

/-- The value of `schrodingerLinear`. -/
@[simp] theorem schrodingerLinear_apply (w : X × Y) (φ : X → ℂ) :
    schrodingerLinear ψ β w φ = schrodingerFun ψ β w φ := rfl

/-- The Schrödinger representation of the Heisenberg group of `polarizedForm β` on all functions
on `X`: `(w, t)` acts by `ψ t • schrodingerFun ψ β w`. -/
def schrodinger : Representation ℂ (HeisenbergGroup (polarizedForm β)) (X → ℂ) where
  toFun g := ψ g.cen • schrodingerLinear ψ β g.vec
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' g h := LinearMap.ext fun φ => by
    simp only [mul_cen, mul_vec, AddChar.map_add_eq_mul, LinearMap.smul_apply,
      Module.End.mul_apply, map_smul, schrodingerLinear_apply, schrodingerFun_comp, smul_smul]
    congr 1; ring

/-- `(w, t)` acts by `ψ t • schrodingerFun ψ β w`. -/
theorem schrodinger_apply (g : HeisenbergGroup (polarizedForm β)) (φ : X → ℂ) :
    schrodinger ψ β g φ = ψ g.cen • schrodingerFun ψ β g.vec φ := rfl

/-- `(w, 0)` acts by `schrodingerFun ψ β w`. -/
@[simp] theorem schrodinger_ofVec (w : X × Y) (φ : X → ℂ) :
    schrodinger ψ β (ofVec w) φ = schrodingerFun ψ β w φ := by
  simp [schrodinger_apply]

/-- The Schrödinger representation has central character `ψ`. -/
theorem schrodinger_hasCentralCharacter : HasCentralCharacter (schrodinger ψ β) ψ :=
  fun t φ => by simp [schrodinger_apply]

section Scale

/-- For bilinear forms with `B' = a B`, the map `(w, t) ↦ (w, a⁻¹ t)` is an isomorphism of
Heisenberg groups `H(B') ≃* H(B)`. -/
def mulCenEquiv {W : Type*} [AddCommGroup W] [Module R W] {B B' : LinearMap.BilinForm R W}
    (a : Rˣ) (h : ∀ x y, B' x y = a * B x y) : HeisenbergGroup B' ≃* HeisenbergGroup B where
  toFun g := ⟨g.vec, (a⁻¹ : Rˣ) * g.cen⟩
  invFun g := ⟨g.vec, a * g.cen⟩
  left_inv g := by ext <;> simp [← mul_assoc]
  right_inv g := by ext <;> simp [← mul_assoc]
  map_mul' g g' := by
    ext
    · rfl
    · simp only [mul_cen, h]
      linear_combination (⅟2 * B g.vec g'.vec) * Units.inv_mul a

@[simp] theorem mulCenEquiv_apply {W : Type*} [AddCommGroup W] [Module R W]
    {B B' : LinearMap.BilinForm R W} (a : Rˣ) (h : ∀ x y, B' x y = a * B x y)
    (g : HeisenbergGroup B') : mulCenEquiv a h g = ⟨g.vec, (a⁻¹ : Rˣ) * g.cen⟩ := rfl

variable {β}

omit [Invertible (2 : R)] in
/-- `polarizedForm (a β) = a polarizedForm β`. -/
theorem polarizedForm_eq_mul {β' : X →ₗ[R] Y →ₗ[R] R} (a : R) (h : ∀ x y, β' x y = a * β x y)
    (w w' : X × Y) : polarizedForm β' w w' = a * polarizedForm β w w' := by
  simp only [polarizedForm_apply, h]; ring

/-- **Change of normalization of the pairing.** For `β' = a β`, the Schrödinger representation of
`(β', ψ)` is that of `(β, x ↦ ψ(a x))` read through `mulCenEquiv`. (With `a = 2`: the model of the
form `½ ⟪,⟫` and the character `ψ(2 ·)` is the model of `⟪,⟫` and `ψ`; equivalently the model of
`(½ ⟪,⟫, ψ)` is that of `(⟪,⟫, ψ_{1/2})`.) -/
theorem schrodinger_comp_mulCenEquiv {β' : X →ₗ[R] Y →ₗ[R] R} (a : Rˣ)
    (h : ∀ x y, β' x y = a * β x y) :
    (schrodinger (ψ.mulShift a) β).comp
      (mulCenEquiv a (polarizedForm_eq_mul (a : R) h)).toMonoidHom = schrodinger ψ β' := by
  ext g φ x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, mulCenEquiv_apply,
    schrodinger_apply, Pi.smul_apply,
    schrodingerFun_apply, AddChar.mulShift_apply, smul_eq_mul, h]
  rw [← mul_assoc (a : R), Units.mul_inv, one_mul, mul_add, mul_left_comm (a : R) (⅟2 : R)]

end Scale

section SchwartzBruhat

variable [TopologicalSpace R] [TopologicalSpace X] [IsTopologicalAddGroup X]
open HarmonicAnalysis

variable {ψ β}

/-- For a locally constant `ψ` and continuous `x ↦ β x y`, the Schrödinger operators preserve
the Schwartz–Bruhat functions. -/
theorem schrodingerFun_mem (hψ : IsLocallyConstant ψ) (hβ : ∀ y, Continuous fun x => β x y)
    (w : X × Y) {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) :
    schrodingerFun ψ β w φ ∈ schwartzBruhatSubmodule X := by
  have h1 : IsLocallyConstant fun x => ψ (β x w.2 + ⅟2 * β w.1 w.2) := by
    simp_rw [AddChar.map_add_eq_mul]
    exact (hψ.comp_continuous (hβ w.2)).mul (IsLocallyConstant.const _)
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩

variable [NonarchimedeanAddGroup R]

/-- The Schrödinger representation on Schwartz–Bruhat functions on `X`, for a continuous
character `ψ` of a nonarchimedean ring and a pairing continuous in its first variable. -/
def schrodingerSB (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y) :
    Representation ℂ (HeisenbergGroup (polarizedForm β)) (SchwartzBruhat X) :=
  (⟨schwartzBruhatSubmodule X, fun g φ hφ => by
      rw [schrodinger_apply]
      exact Submodule.smul_mem _ _ (schrodingerFun_mem
        (isLocallyConstant_of_continuous_addChar ψ hψ) hβ g.vec hφ)⟩ :
    Subrepresentation (schrodinger ψ β)).toRepresentation

/-- The Schrödinger representation on Schwartz–Bruhat functions is the restriction of `schrodinger`. -/
theorem schrodingerSB_apply (hψ : Continuous ψ) (hβ : ∀ y, Continuous fun x => β x y)
    (g : HeisenbergGroup (polarizedForm β)) (φ : SchwartzBruhat X) :
    (schrodingerSB hψ hβ g φ : X → ℂ) = schrodinger ψ β g φ := rfl

/-- The Schrödinger representation on Schwartz–Bruhat functions has central character `ψ`. -/
theorem schrodingerSB_hasCentralCharacter (hψ : Continuous ψ)
    (hβ : ∀ y, Continuous fun x => β x y) : HasCentralCharacter (schrodingerSB hψ hβ) ψ :=
  fun t φ => Subtype.ext (schrodinger_hasCentralCharacter ψ β t φ)

/-- The change of normalization of `schrodinger_comp_mulCenEquiv` on Schwartz–Bruhat functions. -/
theorem schrodingerSB_comp_mulCenEquiv {β' : X →ₗ[R] Y →ₗ[R] R} (a : Rˣ)
    (h : ∀ x y, β' x y = a * β x y) (hψ : Continuous ψ) (hψa : Continuous (ψ.mulShift a))
    (hβ : ∀ y, Continuous fun x => β x y) (hβ' : ∀ y, Continuous fun x => β' x y) :
    (schrodingerSB hψa hβ).comp (mulCenEquiv a (polarizedForm_eq_mul (a : R) h)).toMonoidHom =
      schrodingerSB hψ hβ' := by
  ext g φ : 2
  apply Subtype.ext
  exact LinearMap.congr_fun (DFunLike.congr_fun (schrodinger_comp_mulCenEquiv ψ a h) g) φ

end SchwartzBruhat

end Langlands.HeisenbergGroup
