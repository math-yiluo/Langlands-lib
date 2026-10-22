import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Representation.Whittaker.GeneralLinear
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# The explicit spherical Whittaker function on `GL_(n+1)`

Functions on `GL_(n+1)(F)` are built from their values on the dominant torus cells
of the Iwasawa decomposition `g = u * ϖ ^ lam * k`. The spherical Whittaker function
has value `δ_B ^ (1/2) (ϖ ^ lam) * s_lam(x)` on a dominant cell, where `s_lam` is
the Schur function evaluated at the Satake parameters `x`.
-/

namespace Langlands.GeneralLinear

open Matrix Langlands.Conductor Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF uΓ

namespace Iwasawa

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀}

/-! ### The unipotent part of the chosen decomposition -/

/-- The upper unipotent factor of the chosen decomposition `g = u * ϖ ^ lam * k`. -/
noncomputable def unipotentPart {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) : upperUnipotent (n + 1) F :=
  ⟨(exists_iwasawa hϖ g).choose, (exists_iwasawa hϖ g).choose_spec.1⟩

theorem exists_eq_unipotentPart {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ k ∈ integralSubgroup v.integer n,
      g = (unipotentPart hϖ g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
        torus ϖ (exponent hϖ g) * k :=
  (exists_iwasawa hϖ g).choose_spec.2.choose_spec

variable (v) in
/-- A character of the upper unipotent group that is trivial on its integral points. -/
def IsIntegrallyTrivial {n : ℕ} (θ : upperUnipotent (n + 1) F →* ℂˣ) : Prop :=
  ∀ u : upperUnipotent (n + 1) F,
    (u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) ∈ integralSubgroup v.integer n → θ u = 1

/-! ### Functions given by their values on dominant cells -/

open scoped Classical in
/-- The function with value `θ u * c lam` at `u * ϖ ^ lam * k` when `lam` is antitone
(dominant), and value zero on the other cells. -/
noncomputable def cellFunction {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (θ : upperUnipotent (n + 1) F →* ℂˣ) (c : (Fin (n + 1) → ℤ) → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) : ℂ :=
  if Antitone (exponent hϖ g) then (θ (unipotentPart hϖ g) : ℂ) * c (exponent hϖ g) else 0

section CellFunction

variable {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
  {θ : upperUnipotent (n + 1) F →* ℂˣ} (c : (Fin (n + 1) → ℤ) → ℂ)

/-- On a dominant cell the value does not depend on the chosen decomposition. -/
theorem cellFunction_of_antitone (hθ : IsIntegrallyTrivial v θ) (u : upperUnipotent (n + 1) F)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) :
    cellFunction hϖ θ c ((u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * torus ϖ lam * k) =
      (θ u : ℂ) * c lam := by
  set g := (u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * torus ϖ lam * k with hg
  have he : exponent hϖ g = lam := exponent_eq hϖ u.2 hk rfl
  obtain ⟨k0, hk0, h0⟩ := exists_eq_unipotentPart hϖ g
  rw [he] at h0
  have hamb := iwasawa_unipotent_ambiguity hϖ.1.le hlam u.2 (unipotentPart hϖ g).2 hk hk0
    (hg.symm.trans h0)
  have hθu : θ ((unipotentPart hϖ g)⁻¹ * u) = 1 := hθ _ hamb
  rw [map_mul, map_inv, inv_mul_eq_one] at hθu
  rw [cellFunction, ite_eq_left (he ▸ hlam), he, hθu]

/-- Off the dominant cells the function vanishes. -/
theorem cellFunction_of_not_antitone (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hg : ¬ Antitone (exponent hϖ g)) : cellFunction hϖ θ c g = 0 := by
  rw [cellFunction, ite_eq_right hg]

/-- The value at the torus element `ϖ ^ lam`. -/
theorem cellFunction_torus (hθ : IsIntegrallyTrivial v θ) (lam : Fin (n + 1) → ℤ) :
    cellFunction hϖ θ c (torus ϖ lam) = if Antitone lam then c lam else 0 := by
  split_ifs with hlam
  · have h := cellFunction_of_antitone hϖ c hθ 1 hlam (one_mem _)
    rwa [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one, one_mul] at h
  · exact cellFunction_of_not_antitone hϖ c _ (by rwa [exponent_torus])

theorem cellFunction_one (hθ : IsIntegrallyTrivial v θ) :
    cellFunction hϖ θ c 1 = c 0 := by
  have h := cellFunction_torus hϖ c hθ 0
  have h0 : Antitone (0 : Fin (n + 1) → ℤ) := fun _ _ _ => le_rfl
  have h1 : torus ϖ (0 : Fin (n + 1) → ℤ) = 1 := by
    rw [torus]
    simp only [Pi.zero_apply, zpow_zero]
    exact map_one diagonalUnits
  rw [ite_eq_left h0, h1] at h
  exact h

/-- Left translation by the upper unipotent group multiplies by `θ`. -/
theorem cellFunction_unipotent_mul (hθ : IsIntegrallyTrivial v θ) (u : upperUnipotent (n + 1) F)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    cellFunction hϖ θ c ((u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g) =
      (θ u : ℂ) * cellFunction hϖ θ c g := by
  obtain ⟨k0, hk0, h0⟩ := exists_eq_unipotentPart hϖ g
  by_cases hlam : Antitone (exponent hϖ g)
  · have h1 : (u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g =
        ((u * unipotentPart hϖ g : upperUnipotent (n + 1) F) :
          Matrix.GeneralLinearGroup (Fin (n + 1)) F) * torus ϖ (exponent hϖ g) * k0 := by
      rw [Subgroup.coe_mul]
      conv_lhs => rw [h0]
      simp only [mul_assoc]
    have h2 : g = ((unipotentPart hϖ g : upperUnipotent (n + 1) F) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) F) * torus ϖ (exponent hϖ g) * k0 := h0
    rw [h1, cellFunction_of_antitone hϖ c hθ _ hlam hk0]
    conv_rhs => rw [h2, cellFunction_of_antitone hϖ c hθ _ hlam hk0]
    rw [map_mul, Units.val_mul, mul_assoc]
  · rw [cellFunction_of_not_antitone hϖ c g hlam, cellFunction_of_not_antitone hϖ c _
      (by rwa [exponent_unipotent_mul hϖ g u.2]), mul_zero]

/-- Right translation by an integral matrix preserves the function. -/
theorem cellFunction_mul_integral (hθ : IsIntegrallyTrivial v θ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) :
    cellFunction hϖ θ c (g * k) = cellFunction hϖ θ c g := by
  obtain ⟨k0, hk0, h0⟩ := exists_eq_unipotentPart hϖ g
  by_cases hlam : Antitone (exponent hϖ g)
  · have h1 : g * k = ((unipotentPart hϖ g : upperUnipotent (n + 1) F) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) F) * torus ϖ (exponent hϖ g) * (k0 * k) := by
      rw [← mul_assoc, ← h0]
    rw [h1, cellFunction_of_antitone hϖ c hθ _ hlam (mul_mem hk0 hk)]
    conv_rhs => rw [h0, cellFunction_of_antitone hϖ c hθ _ hlam hk0]
  · rw [cellFunction_of_not_antitone hϖ c g hlam, cellFunction_of_not_antitone hϖ c _
      (by rwa [exponent_mul_integral hϖ g hk])]

/-- The cell function lies in the `θ`-equivariant function space. -/
theorem cellFunction_mem (hθ : IsIntegrallyTrivial v θ) :
    cellFunction hϖ θ c ∈ (equivariantFunctions (upperUnipotent (n + 1) F) θ).toSubmodule :=
  fun u g => cellFunction_unipotent_mul hϖ c hθ u g

/-- A `θ`-equivariant, right integral-invariant function is the cell function of its torus
values, provided it vanishes at `ϖ ^ lam` for every non-antitone `lam`. -/
theorem eq_cellFunction (hθ : IsIntegrallyTrivial v θ)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : f ∈ (equivariantFunctions (upperUnipotent (n + 1) F) θ).toSubmodule)
    (hK : ∀ g, ∀ k ∈ integralSubgroup v.integer n, f (g * k) = f g)
    (hzero : ∀ lam : Fin (n + 1) → ℤ, ¬ Antitone lam → f (torus ϖ lam) = 0) :
    f = cellFunction hϖ θ (fun lam => f (torus ϖ lam)) := by
  funext g
  obtain ⟨k0, hk0, h0⟩ := exists_eq_unipotentPart hϖ g
  have hfg : f g = (θ (unipotentPart hϖ g) : ℂ) * f (torus ϖ (exponent hϖ g)) := by
    conv_lhs => rw [h0, hK _ k0 hk0]
    exact hf _ _
  by_cases hlam : Antitone (exponent hϖ g)
  · rw [hfg]
    conv_rhs => rw [h0, cellFunction_of_antitone hϖ _ hθ _ hlam hk0]
  · rw [hfg, hzero _ hlam, mul_zero, cellFunction_of_not_antitone hϖ _ g hlam]

end CellFunction

/-! ### Standard characters of integrally trivial additive characters -/

section Standard

variable [TopologicalSpace F]

theorem isIntegrallyTrivial_standardCharacter {ψ : UnitaryAdditiveCharacter F}
    (hψ : ∀ x ∈ v.integer, ψ x = 1) (n : ℕ) :
    IsIntegrallyTrivial v (standardCharacter ψ n) := by
  intro u hu
  have hsum : ∑ i : Fin n, u.val i.castSucc i.succ ∈ v.integer :=
    Subring.sum_mem _ fun i _ => ((mem_integralSubgroup v.integer n _).1 hu).1 _ _
  apply Units.ext
  rw [standardCharacter_apply, ψ.complex_apply, hψ _ hsum, Circle.coe_one, Units.val_one]

theorem isIntegrallyTrivial_inverseStandardCharacter {ψ : UnitaryAdditiveCharacter F}
    (hψ : ∀ x ∈ v.integer, ψ x = 1) (n : ℕ) :
    IsIntegrallyTrivial v (inverseStandardCharacter ψ n) := by
  intro u hu
  change (standardCharacter ψ n u)⁻¹ = 1
  rw [isIntegrallyTrivial_standardCharacter hψ n u hu, inv_one]

end Standard

end Iwasawa

/-! ### Schur functions at Satake parameters -/

namespace Spherical

open MvPolynomial

/-- The complete homogeneous symmetric polynomial `h_k`, with `h_k = 0` for `k < 0`. -/
noncomputable def completeSymm (σ : Type*) (R : Type*) [CommSemiring R] [Fintype σ]
    [DecidableEq σ] (k : ℤ) :
    MvPolynomial σ R :=
  if 0 ≤ k then hsymm σ R k.toNat else 0

/-- The Jacobi–Trudi determinant `det (h_(α i - i + j))` in `m` variables. -/
noncomputable def jacobiTrudi (R : Type*) [CommRing R] {m : ℕ} (α : Fin m → ℤ) :
    MvPolynomial (Fin m) R :=
  (Matrix.of fun i j : Fin m => completeSymm (Fin m) R (α i - i + j)).det

/-- The Schur function of an integral weight `lam` at nonzero parameters `x`: the
Jacobi–Trudi determinant of the shifted weight `lam - lam_last`, times
`(∏ i, x i) ^ lam_last`. -/
noncomputable def satakeSchur {n : ℕ} (x : Fin (n + 1) → ℂˣ) (lam : Fin (n + 1) → ℤ) : ℂ :=
  (∏ i, (x i : ℂ)) ^ lam (Fin.last n) *
    eval (fun i => (x i : ℂ)) (jacobiTrudi ℂ fun i => lam i - lam (Fin.last n))

/-- The square root of the modulus character of the upper Borel subgroup at `ϖ ^ lam`,
`δ_B ^ (1/2) (ϖ ^ lam) = q ^ (-(∑ i, (n - 2 i) lam i) / 2)` for residue cardinality `q`. -/
noncomputable def halfModulus (q : ℕ) {n : ℕ} (lam : Fin (n + 1) → ℤ) : ℂ :=
  ((Real.sqrt q : ℝ) : ℂ) ^ (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i)

theorem jacobiTrudi_zero (R : Type*) [CommRing R] (m : ℕ) :
    jacobiTrudi R (0 : Fin m → ℤ) = 1 := by
  rw [jacobiTrudi, Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [completeSymm, hsymm_zero]
  · intro i j hji
    have hlt : (j : ℕ) < (i : ℕ) := hji
    have : ¬ (0 : ℤ) ≤ (0 : Fin m → ℤ) i - (i : ℤ) + j := by
      simp only [Pi.zero_apply]
      omega
    rw [Matrix.of_apply, completeSymm, ite_eq_right this]

theorem satakeSchur_zero {n : ℕ} (x : Fin (n + 1) → ℂˣ) : satakeSchur x 0 = 1 := by
  have : (fun i : Fin (n + 1) => (0 : Fin (n + 1) → ℤ) i - (0 : Fin (n + 1) → ℤ) (Fin.last n)) =
      0 := by
    funext i
    simp
  rw [satakeSchur, this, jacobiTrudi_zero, map_one, Pi.zero_apply, zpow_zero, one_mul]

theorem halfModulus_zero (q : ℕ) (n : ℕ) : halfModulus q (0 : Fin (n + 1) → ℤ) = 1 := by
  simp [halfModulus]

/-! ### The spherical Whittaker function -/

open Iwasawa

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀}

/-- The explicit spherical Whittaker function with Satake parameters `x`: its value at
`u * ϖ ^ lam * k` is `θ u * δ_B ^ (1/2) (ϖ ^ lam) * s_lam(x)` for antitone `lam`, and zero
on the other cells. -/
noncomputable def sphericalWhittaker {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ) (x : Fin (n + 1) → ℂˣ) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ :=
  cellFunction hϖ θ fun lam => halfModulus q lam * satakeSchur x lam

section SphericalWhittaker

variable {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
  {θ : upperUnipotent (n + 1) F →* ℂˣ} (q : ℕ) (x : Fin (n + 1) → ℂˣ)

theorem sphericalWhittaker_mem (hθ : IsIntegrallyTrivial v θ) :
    sphericalWhittaker hϖ θ q x ∈
      (equivariantFunctions (upperUnipotent (n + 1) F) θ).toSubmodule :=
  cellFunction_mem hϖ _ hθ

theorem sphericalWhittaker_mul_integral (hθ : IsIntegrallyTrivial v θ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) :
    sphericalWhittaker hϖ θ q x (g * k) = sphericalWhittaker hϖ θ q x g :=
  cellFunction_mul_integral hϖ _ hθ g hk

theorem sphericalWhittaker_torus (hθ : IsIntegrallyTrivial v θ) (lam : Fin (n + 1) → ℤ) :
    sphericalWhittaker hϖ θ q x (torus ϖ lam) =
      if Antitone lam then halfModulus q lam * satakeSchur x lam else 0 :=
  cellFunction_torus hϖ _ hθ lam

theorem sphericalWhittaker_one (hθ : IsIntegrallyTrivial v θ) :
    sphericalWhittaker hϖ θ q x 1 = 1 := by
  rw [sphericalWhittaker, cellFunction_one hϖ _ hθ, halfModulus_zero, satakeSchur_zero, one_mul]

end SphericalWhittaker

end Spherical

end Langlands.GeneralLinear
