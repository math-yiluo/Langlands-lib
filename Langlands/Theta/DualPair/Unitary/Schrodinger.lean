import Langlands.Theta.DualPair.Unitary.Form

/-!
# The Schrödinger model of the unitary dual pair

GKT §12.4.1 (the Schrödinger model `S(𝕏^*)` for a Type I pair with `W` split, p. 369) in Case
`3₊` (GKT p. 288): `E / F` a quadratic extension of nonarchimedean local fields with conjugation
`c`, `Q` a Hermitian `α × α` matrix over `E`, `U(ν, ν)` the quasi-split unitary group, and
`𝕎 = M_{α×2ν}(E)` with the symplectic form `hermitianSymplecticForm c Q` and its polarization by the
first and last `ν` columns (`Langlands.Theta.DualPair.Unitary.Form`).

`hermitianSchrodinger c ν Q ψ` is the Schrödinger representation `HeisenbergGroup.schrodingerSB`
of the Heisenberg group of `polarizedForm (hermitianPairing c Q)` on the Schwartz–Bruhat functions
on `M_{α×ν}(E)`: `(x₀, y₀)` acts by `φ ↦ ψ(β(·, y₀) + ½ β(x₀, y₀)) φ(· + x₀)` with
`β = hermitianPairing c Q` (GKT (1.6), Theorem 1.13, p. 25, with the book's `(X, Y)` the file's
`(0 × M_{α×ν}(E), M_{α×ν}(E) × 0)`). The form is `½ tr_{E/F}` of the book's form `⟪,⟫` of
GKT Theorem 10.28 (p. 288), so that this is the book's Schrödinger model for the character
`t ↦ ψ(t / 2)`.

Internal: the operators `heisFun` (the same operators written with the symplectic form), their
composition law (`heisFun_heisFun`) and their behaviour under the Siegel Levi (`heisFun_levi`).
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis

namespace Unitary.Internal

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The Schrödinger operator of `w = (x₀, y₀)` written with the symplectic form:
`φ ↦ ψ(⟪(x, 0), (0, y₀)⟫ + ½ ⟪(x₀, 0), (0, y₀)⟫) φ(x + x₀)`. -/
def heisFun (ψ : AddChar F ℂ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  fun x => ψ (hermitianSymplecticForm c Q (fromCols x 0) (fromCols 0 w.toCols₂) +
    2⁻¹ * hermitianSymplecticForm c Q (fromCols w.toCols₁ 0) (fromCols 0 w.toCols₂)) * φ
        (x + w.toCols₁)

theorem heisFun_heisFun [CharZero F] (hc : ∀ z,
    c (c z) = z) (ψ : AddChar F ℂ) {Q : Matrix α α E} (hQ : IsHerm c Q)
    (w w' : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w (heisFun c ψ Q w' φ) = ψ
        (2⁻¹ * hermitianSymplecticForm c Q w w') • heisFun c ψ Q (w + w') φ := by
  have e1 : ∀ x x' : Matrix α ν E,
      fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E,
      fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp
  have e3 : ∀ u : Matrix α (ν ⊕ ν) E, u = fromCols u.toCols₁ 0 + fromCols 0 u.toCols₂ := fun u => by
    ext i (j | j) <;> simp
  have e4 : hermitianSymplecticForm c Q w w' = hermitianSymplecticForm c Q (fromCols w.toCols₁ 0)
      (fromCols 0 w'.toCols₂) -
      hermitianSymplecticForm c Q (fromCols w'.toCols₁ 0) (fromCols 0 w.toCols₂) := by
    conv_lhs => rw [e3 w, e3 w']
    rw [form_add_left, form_add_right, form_add_right, form_left_left, form_right_right,
      form_swap c hc hQ.1 (fromCols w'.toCols₁ 0)]
    ring
  funext x
  rw [Pi.smul_apply, heisFun, heisFun, heisFun,
      show (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ from rfl,
    show (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ from rfl, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x, e4]
  congr 2
  simp only [e1, e2, form_add_left, form_add_right]
  ring

omit [DecidableEq α] in

theorem heisFun_levi (hc : ∀ z,
    c (c z) = z) (ψ : AddChar F ℂ) (Q : Matrix α α E) (a : GL ν E) (w : Matrix α (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w (fun x => φ (x * (a : Matrix ν ν E))) =
      fun x => heisFun c ψ Q (w * ((siegelLevi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) φ
          (x * (a : Matrix ν ν E)) := by
  have e : ∀ x y : Matrix α ν E,
      fromCols x y * ((siegelLevi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      fromCols (x * (a : Matrix ν ν E)) (y *
          (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ) := fun x y => by
    rw [siegelLevi_val c hc a, fromCols_mul_fromBlocks]; simp
  have f : ∀ x y : Matrix α ν E, hermitianSymplecticForm c Q (fromCols (x * (a : Matrix ν ν E)) 0)
      (fromCols 0 (y * (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ)) = hermitianSymplecticForm c Q
          (fromCols x 0) (fromCols 0 y) := fun x y => by
    rw [← form_mul c Q (siegelLevi c hc a) (fromCols x 0), e, e, Matrix.zero_mul, Matrix.zero_mul]
  funext x
  conv_rhs => rw [← fromCols_toCols w, e]
  simp only [heisFun, toCols₁_fromCols, toCols₂_fromCols, f, Matrix.add_mul]

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

omit [DecidableEq α] in
theorem heisFun_mem {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α
    (ν ⊕ ν) E)
    {φ : Matrix α ν E → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule
        (Matrix α ν E)) : heisFun c ψ Q w φ ∈ schwartzBruhatSubmodule (Matrix α ν E) := by
  have := IsModuleTopology.isTopologicalAddGroup F E
  have h1 := (isLocallyConstant_of_continuous_addChar ψ hψ).comp_continuous
    ((continuous_form_left c Q (fromCols 0 w.toCols₂)).add (continuous_const
      (y := 2⁻¹ * hermitianSymplecticForm c Q (fromCols w.toCols₁ 0) (fromCols 0 w.toCols₂))))
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.toCols₁)).mul_left⟩

def Heisenberg₂ {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E) :
    Module.End ℂ (schwartzBruhatSubmodule (Matrix α ν E)) where
  toFun φ := ⟨heisFun c ψ Q w φ, heisFun_mem c hψ Q w φ.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => mul_left_comm _ _ _)

omit [DecidableEq α] in
theorem heis_apply {ψ : AddChar F ℂ} (hψ : Continuous ψ) (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E)
    (φ : schwartzBruhatSubmodule (Matrix α ν E)) :
        (Heisenberg₂ c hψ Q w φ : Matrix α ν E → ℂ) = heisFun c ψ Q w φ := rfl

end Local

end Unitary.Internal

open Unitary.Internal

section Pairing

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The Schrödinger operators of the Hermitian pairing are the operators `heisFun`. -/
theorem Unitary.Internal.schrodingerFun_hermitian [Invertible (2 : F)] (ψ : AddChar F ℂ)
    (Q : Matrix α α E) (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w φ =
      HeisenbergGroup.schrodingerFun ψ (hermitianPairing c Q) (w.toCols₁, w.toCols₂) φ := by
  funext x
  simp only [heisFun, HeisenbergGroup.schrodingerFun_apply,
      hermitianPairing_eq_hermitianSymplecticForm,
    invOf_eq_inv]

end Pairing

section Schrodinger

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
      [IsModuleTopology F E]
  (c : E →ₐ[F] E) {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

variable (ν) in
/-- The Schrödinger representation of the Heisenberg group of `M_{α×2ν}(E)` on Schwartz–Bruhat
functions on `M_{α×ν}(E)`: `HeisenbergGroup.schrodingerSB` for the character `ψ` and the
Hermitian pairing. -/
def hermitianSchrodinger (Q : Matrix α α E) (ψ : UnitaryAdditiveCharacter F) :
    Representation ℂ (HeisenbergGroup (HeisenbergGroup.polarizedForm (hermitianPairing
        (ν := ν) c Q)))
      (SchwartzBruhat (Matrix α ν E)) :=
  have := IsModuleTopology.isTopologicalAddGroup F E
  HeisenbergGroup.schrodingerSB ψ.continuous_complex (continuous_hermitianPairing_left c Q)

theorem hermitianSchrodinger_apply (Q : Matrix α α E) (ψ : UnitaryAdditiveCharacter F)
    (k : HeisenbergGroup (HeisenbergGroup.polarizedForm (hermitianPairing (ν := ν) c Q)))
    (φ : SchwartzBruhat (Matrix α ν E)) :
    (hermitianSchrodinger c ν Q ψ k φ : Matrix α ν E → ℂ) =
      HeisenbergGroup.schrodinger ψ.complex (hermitianPairing c Q) k φ :=
  rfl

end Schrodinger

end Langlands.Theta
