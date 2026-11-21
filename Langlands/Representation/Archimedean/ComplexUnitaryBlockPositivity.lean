import Langlands.Representation.Archimedean.ComplexUnitaryHermitianDual
import Langlands.Representation.Archimedean.GKModuleDensity

/-! Positivity of relative multipliers of intertwiners into the Hermitian-dual series. -/

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.Operator TensorProduct
open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean ComplexDuality ComplexStandardHomTransposeProof

variable {n : ℕ}

/-- An irreducible complex principal series satisfies the hypotheses of the Library's
Schur lemma for admissible `(𝔤, K)`-modules. -/
theorem densityHyp_standard (ds : List ComplexCharacterData)
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)) :
    GKModuleDensity.Hyp (complexStandardRep n ds) (complexStandardLie n ds) := by
  have gk := isComplexGKModule_complexStandardModule n ds
  exact
    { irreducible := hirr
      admissible := isAdmissibleGKModule_principalSeriesRep (n := n) (complexPositionCharacter ds)
      finite := fun w =>
        ⟨FiniteVectors.orbitSpan (complexStandardRep n ds) w,
          FiniteVectors.self_mem_orbitSpan (complexStandardRep n ds) w, gk.1 w,
          fun k _ hx =>
            (FiniteVectors.orbitSubrepresentation (complexStandardRep n ds) w).apply_mem_toSubmodule
              k hx⟩
      continuous := gk.2.1 }

/-- On an irreducible unitarizable principal series, the diagonal of the integral pairing
of any intertwiner into the Hermitian-dual series with the pointwise conjugate is a fixed
multiple of an invariant positive form. -/
theorem exists_hermitianPairing_diag (ds : List ComplexCharacterData) (hn : ds.length = n)
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds))
    (hU : IsComplexUnitarizableGKModule n (complexStandardRep n ds) (complexStandardLie n ds))
    (S : ComplexBlock.KFs n ds →ₗ[ℂ] ComplexBlock.KFs n (ds.map hermitianData))
    (hS : IsComplexStandardIntertwining n (complexStandardRep n (ds.map hermitianData))
      (complexStandardLie n (ds.map hermitianData)) ds S) :
    ∃ (b : InvariantPositiveForm (complexStandardRep n ds)) (μ : ℂ), ∀ v,
      hermitianPairing n ds (S v) (conjugateStandard ds v) = μ * b.inner v v := by
  have hperm := perm_hermitianData_of_irreducible_unitarizable ds hn hirr hU
  obtain ⟨b, hb⟩ := hU
  obtain ⟨T, hTinj, hT, hTdiag⟩ := exists_hermitianIntertwiner ds b hb
  obtain ⟨P, hPbij, hP⟩ :=
    complexStandardPermutation n ds (ds.map hermitianData) hn hperm.symm hirr
  have H := densityHyp_standard ds hirr
  obtain ⟨α, hα⟩ := GKModuleDensity.exists_eq_scalar H (P ∘ₗ S)
    (fun k v => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hS.map_rep, hP.map_rep])
    (fun X v => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hS.map_lie, hP.map_lie])
  obtain ⟨β, hβ⟩ := GKModuleDensity.exists_eq_scalar H (P ∘ₗ T)
    (fun k v => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.map_rep, hP.map_rep])
    (fun X v => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.map_lie, hP.map_lie])
  have hβ0 : β ≠ 0 := by
    intro h0
    have : Nontrivial (ComplexBlock.KFs n ds) := complexStandardNontrivial n ds hn
    obtain ⟨v, hv⟩ := exists_ne (0 : ComplexBlock.KFs n ds)
    apply hv
    apply hTinj
    apply hPbij.injective
    have e := hβ v
    rw [LinearMap.comp_apply, h0, zero_smul] at e
    rw [e, map_zero, map_zero]
  refine ⟨b, α / β, fun v => ?_⟩
  have hST : S v = (α / β) • T v := by
    apply hPbij.injective
    have e₁ := hα v
    have e₂ := hβ v
    rw [LinearMap.comp_apply] at e₁ e₂
    rw [map_smul, e₁, e₂, smul_smul, div_mul_cancel₀ _ hβ0]
  rw [hST, map_smul, LinearMap.smul_apply, hTdiag, smul_eq_mul]

/-- The diagonal integral pairing of a vector whose image is a scalar multiple of it on the
compact group is that scalar times the squared `L²` norm over `U(n)`. -/
theorem hermitianPairing_eq_mul_integral_normSq (ds : List ComplexCharacterData)
    (v : ComplexBlock.KFs n ds) (w : ComplexBlock.KFs n (ds.map hermitianData)) (a : ℂ)
    (h : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      (w : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) =
        a * (v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U)) :
    hermitianPairing n ds w (conjugateStandard ds v) =
      a * ((∫ k : unitaryCompact ℂ n,
        Complex.normSq ((v : Langlands.GeneralLinear n ℂ → ℂ) k) ∂unitaryHaar n : ℝ) : ℂ) := by
  rw [hermitianPairing, integralPairing_apply, ← integral_complex_ofReal, ← integral_const_mul]
  congr 1
  funext k
  let U : Matrix.unitaryGroup (Fin n) ℂ := ⟨((k : Langlands.GeneralLinear n ℂ) :
    Matrix (Fin n) (Fin n) ℂ), k.2⟩
  have hU : Unitary.toUnits U = (k : Langlands.GeneralLinear n ℂ) := Units.ext rfl
  change (w : Langlands.GeneralLinear n ℂ → ℂ) k *
      conj ((v : Langlands.GeneralLinear n ℂ → ℂ) k) = _
  rw [← hU, h U, mul_assoc, Complex.mul_conj]

/-- A nonzero compact-finite vector of a principal series has positive squared `L²` norm
over `U(n)`. -/
theorem integral_normSq_pos (ds : List ComplexCharacterData) (v : ComplexBlock.KFs n ds) (hv : v ≠ 0) :
    0 < ∫ k : unitaryCompact ℂ n,
      Complex.normSq ((v : Langlands.GeneralLinear n ℂ → ℂ) k) ∂unitaryHaar n := by
  have hmem := Submodule.mem_inf.mp v.2
  obtain ⟨k, hk⟩ : ∃ k : unitaryCompact ℂ n, (v : Langlands.GeneralLinear n ℂ → ℂ) k ≠ 0 := by
    by_contra hc
    apply hv
    exact (Submodule.coe_eq_zero).mp (eq_zero_of_mem_principalSeries_of_eqOn hmem.1
      fun k hk => by_contra fun h => hc ⟨⟨k, hk⟩, h⟩)
  have hcont : Continuous (v : Langlands.GeneralLinear n ℂ → ℂ) := hmem.1.1.continuous
  exact integral_unitaryHaar_pos
    (f := fun k : unitaryCompact ℂ n => Complex.normSq ((v : Langlands.GeneralLinear n ℂ → ℂ) k))
    (Complex.continuous_normSq.comp (hcont.comp continuous_subtype_val))
    (fun k => Complex.normSq_nonneg _) (k := k) (Complex.normSq_pos.mpr hk).ne'

/-- The diagonal value of an invariant positive form is a positive real number. -/
theorem exists_inner_self_eq_pos {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V} (b : InvariantPositiveForm ρ)
    (v : V) (hv : v ≠ 0) : ∃ B : ℝ, 0 < B ∧ b.inner v v = B := by
  refine ⟨(b.inner v v).re, ?_, (Complex.conj_eq_iff_re.mp (b.conj_inner_symm v v)).symm⟩
  have hnn : 0 ≤ (b.inner v v).re := b.re_inner_nonneg v
  refine lt_of_le_of_ne hnn fun h0 => hv (b.definite v ?_)
  rw [← (Complex.conj_eq_iff_re.mp (b.conj_inner_symm v v)), ← h0, Complex.ofReal_zero]

/-- **Positivity of the relative multiplier.** Let `ds` be a list of `n` characters whose
compact-finite principal series is irreducible and infinitesimally unitarizable, and let `S`
be an intertwiner into the principal series of the Hermitian-dual characters. If on the
compact group `S` multiplies a nonzero vector `v₀` by a nonzero scalar `c` and a nonzero
vector `v₁` by `c * r` with `r` real, then `r` is positive. -/
theorem relativeMultiplier_pos (ds : List ComplexCharacterData) (hn : ds.length = n)
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds))
    (hU : IsComplexUnitarizableGKModule n (complexStandardRep n ds) (complexStandardLie n ds))
    (S : ComplexBlock.KFs n ds →ₗ[ℂ] ComplexBlock.KFs n (ds.map hermitianData))
    (hS : IsComplexStandardIntertwining n (complexStandardRep n (ds.map hermitianData))
      (complexStandardLie n (ds.map hermitianData)) ds S)
    {v₀ v₁ : ComplexBlock.KFs n ds} (h₀ : v₀ ≠ 0) (h₁ : v₁ ≠ 0) {c : ℂ} (hc : c ≠ 0) {r : ℝ}
    (hv₀ : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      (S v₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) =
        c * (v₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U))
    (hv₁ : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      (S v₁ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) =
        (c * r) * (v₁ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U)) :
    0 < r := by
  obtain ⟨b, μ, hμ⟩ := exists_hermitianPairing_diag ds hn hirr hU S hS
  obtain ⟨B₀, hB₀, e₀⟩ := exists_inner_self_eq_pos b v₀ h₀
  obtain ⟨B₁, hB₁, e₁⟩ := exists_inner_self_eq_pos b v₁ h₁
  have hN₀ := integral_normSq_pos ds v₀ h₀
  have hN₁ := integral_normSq_pos ds v₁ h₁
  set N₀ := ∫ k : unitaryCompact ℂ n,
    Complex.normSq ((v₀ : Langlands.GeneralLinear n ℂ → ℂ) k) ∂unitaryHaar n
  set N₁ := ∫ k : unitaryCompact ℂ n,
    Complex.normSq ((v₁ : Langlands.GeneralLinear n ℂ → ℂ) k) ∂unitaryHaar n
  have E₀ := hμ v₀
  have E₁ := hμ v₁
  rw [hermitianPairing_eq_mul_integral_normSq ds v₀ (S v₀) c hv₀, e₀] at E₀
  rw [hermitianPairing_eq_mul_integral_normSq ds v₁ (S v₁) (c * r) hv₁, e₁] at E₁
  have key : c * ((r * N₁ * B₀ : ℝ) : ℂ) = c * ((N₀ * B₁ : ℝ) : ℂ) := by
    push_cast
    linear_combination (B₀ : ℂ) * E₁ - (B₁ : ℂ) * E₀
  have hreal : r * N₁ * B₀ = N₀ * B₁ := Complex.ofReal_injective (mul_left_cancel₀ hc key)
  have hpos : 0 < r * (N₁ * B₀) := by
    rw [← mul_assoc, hreal]
    exact mul_pos hN₀ hB₁
  exact pos_of_mul_pos_left hpos (mul_pos hN₁ hB₀).le

end Langlands.Archimedean.ComplexUnitary
