import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement
import Langlands.Representation.Unitary.InvariantSesquilinear

/-! # From a nonnegative diagonal to infinitesimal unitarity -/

noncomputable section

open scoped ComplexConjugate TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

/-- A nonzero invariant sesquilinear form with real nonnegative diagonal
unitarizes an irreducible real `(𝔤, K)`-module. -/
def RealGKNonnegativeFormStatement : Prop :=
  ∀ {n : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsIrreducibleGKModule ρ π →
    ∀ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, B ≠ 0 →
      (∀ k v w, B (ρ k v) (ρ k w) = B v w) →
      (∀ (X : Matrix (Fin n) (Fin n) ℝ) v w,
        B (π (1 ⊗ₜ X) v) w + B v (π (1 ⊗ₜ X) w) = 0) →
      (∀ v, (B v v).im = 0) → (∀ v, 0 ≤ (B v v).re) →
      IsRealUnitarizableGKModule n ρ π

theorem realGKNonnegativeForm : RealGKNonnegativeFormStatement.{u} := by
  intro n V _ _ ρ π hirr B hB hK hL hIm hRe
  have hAdjoint : B = LinearAlgebra.adjointPairing B := by
    apply sub_eq_zero.mp
    apply InvariantSesquilinear.eq_zero_of_diagonal
    intro v
    change B v v - conj (B v v) = 0
    rw [(Complex.conj_eq_iff_im).2 (hIm v), sub_self]
  have hSymm (v w : V) : B w v = conj (B v w) :=
    congrArg (fun C : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => C w v) hAdjoint
  let R := LinearMap.ker B
  have hRK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V) (hv : v ∈ R) :
      ρ k v ∈ R := by
    change B v = 0 at hv
    change B (ρ k v) = 0
    ext w
    have he := hK k v (ρ k⁻¹ w)
    rw [ρ.self_inv_apply, hv, LinearMap.zero_apply] at he
    exact he
  have hRLreal (X : Matrix (Fin n) (Fin n) ℝ) (v : V) (hv : v ∈ R) :
      π (1 ⊗ₜ X) v ∈ R := by
    change B v = 0 at hv
    change B (π (1 ⊗ₜ X) v) = 0
    ext w
    have he := hL X v w
    rwa [hv, LinearMap.zero_apply, add_zero] at he
  have hRL (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) : ∀ v ∈ R, π X v ∈ R := by
    induction X using TensorProduct.inductionOn with
    | tmul c Y =>
      intro v hv
      have he : c ⊗ₜ[ℝ] Y = c • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, map_smul, LinearMap.smul_apply]
      exact R.smul_mem c (hRLreal Y v hv)
    | add X Y hX hY =>
      intro v hv
      rw [map_add, LinearMap.add_apply]
      exact R.add_mem (hX v hv) (hY v hv)
  have hR : R = ⊥ :=
    (hirr.2 R hRK hRL).resolve_right (fun htop => hB (LinearMap.ker_eq_top.mp htop))
  have hDef (v : V) (hvv : B v v = 0) : v = 0 := by
    have hv : v ∈ R := by
      change B v = 0
      ext w
      change B v w = 0
      by_contra hz
      let t : ℝ := (B w w).re + 1
      let a : ℂ := -(t : ℂ) / conj (B v w)
      have hConj : conj (B v w) ≠ 0 := by simpa using hz
      have ha : a * conj (B v w) = -(t : ℂ) :=
        div_mul_cancel₀ _ hConj
      have ha' : conj a * B v w = -(t : ℂ) := by
        simpa only [map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal] using
          congrArg (starRingEnd ℂ) ha
      have hn := hRe (w + a • v)
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply, hvv, mul_zero, add_zero] at hn
      rw [hSymm v w, ha, ha'] at hn
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, t] at hn
      linarith [hRe w]
    simpa only [hR, Submodule.mem_bot] using hv
  let b : InvariantPositiveForm ρ :=
    { inner := fun v w => B v w
      conj_inner_symm := fun v w => (hSymm w v).symm
      re_inner_nonneg := hRe
      add_left := fun _ _ _ => by simp
      smul_left := fun _ _ _ => by simp
      definite := hDef
      invariant := hK }
  exact ⟨b, hL⟩

end Langlands.Archimedean
