import Langlands.Global.AdelicEisensteinConvergenceStatement
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Regular lines and holomorphy of Eisenstein series along lines -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

section Lines

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The imaginary or real shift of a parameter along a character multiplies each Eisenstein
term by the corresponding exponential of its height. -/
theorem eisensteinTerm_add_smul (hK : IsIwasawaCompact p K) (φ : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) (χ : rationalCharacters P) (z : ℂ)
    (g : AdelicGroupPoints F G) (c : ParabolicRationalCosets F p) :
    hK.eisensteinTerm φ (lam + z • ((1 : ℂ) ⊗ₜ[ℤ] χ)) g c =
      hK.eisensteinTerm φ lam g c * Complex.exp (z * (hK.height
        (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g) χ : ℂ)) := by
  simp only [IsIwasawaCompact.eisensteinTerm, IsIwasawaCompact.parameterTwist,
    IsIwasawaCompact.heightPower, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    complexParameterPairing_tmul, one_mul, smul_eq_mul, Complex.exp_add]
  ring

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem parameterRealPart_add_smul (lam : ComplexCharacterParameter F P)
    (χ : rationalCharacters P) (z : ℂ) :
    parameterRealPart F P (lam + z • ((1 : ℂ) ⊗ₜ[ℤ] χ)) =
      parameterRealPart F P lam + z.re • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
  rw [map_add, TensorProduct.smul_tmul', smul_eq_mul, mul_one, parameterRealPart_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

section Regular

variable {M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- Regularity along a character line depends only on the real part of the coordinate. -/
theorem isRegularParameter_add_smul_iff (R : ℝ) (lam : ComplexCharacterParameter F P)
    (χ : rationalCharacters P) (z : ℂ) :
    r.IsRegularParameter hA hT R (lam + z • ((1 : ℂ) ⊗ₜ[ℤ] χ)) ↔
      r.IsRegularParameter hA hT R (lam + (z.re : ℂ) • ((1 : ℂ) ⊗ₜ[ℤ] χ)) := by
  unfold ParabolicRootPresentation.IsRegularParameter
  rw [parameterRealPart_add_smul, parameterRealPart_add_smul, Complex.ofReal_re]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- **Holomorphy along lines.** If the Eisenstein terms admit compact-uniform summable
majorants on `R`-regular parameters, the Eisenstein series is holomorphic along every complex
line on any open set of regular parameters. -/
theorem differentiableOn_eisensteinSeries_line (hK : IsIwasawaCompact p K) (R : ℝ)
    (φ : AdelicGroupPoints F G → ℂ)
    (hconv : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (Λ : Set (Fin n → ℂ)), IsCompact Λ →
        (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
        ∃ b : ParabolicRationalCosets F p → ℝ, Summable b ∧
          ∀ c, ∀ g ∈ C, ∀ s ∈ Λ, ‖hK.eisensteinTerm φ (e s) g c‖ ≤ b c)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ v : Fin n → ℂ)
    {S : Set ℂ} (hS : IsOpen S) (hreg : ∀ z ∈ S, r.IsRegularParameter hA hT R (e (s₀ + z • v)))
    (g : AdelicGroupPoints F G) :
    DifferentiableOn ℂ (fun z => hK.eisensteinSeries φ (e (s₀ + z • v)) g) S := by
  intro z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS z₀ hz₀
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hcb : Metric.closedBall z₀ δ ⊆ S := fun z hz =>
    hball (Metric.closedBall_subset_ball (half_lt_self hε) hz)
  let aff : ℂ → Fin n → ℂ := fun z => s₀ + z • v
  have haff : Continuous aff := continuous_const.add (continuous_id.smul continuous_const)
  obtain ⟨b, hb, hbound⟩ := hconv {g} isCompact_singleton n e (aff '' Metric.closedBall z₀ δ)
    ((isCompact_closedBall z₀ δ).image haff) (by
      rintro _ ⟨z, hz, rfl⟩
      exact hreg z (hcb hz))
  have hterm : ∀ c, Differentiable ℂ fun z => hK.eisensteinTerm φ (e (aff z)) g c := by
    intro c
    let x := ((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g
    have h : (fun z => hK.eisensteinTerm φ (e (aff z)) g c) = fun z =>
        φ x * Complex.exp (complexParameterPairing F P (e s₀) (hK.height x) +
          z * complexParameterPairing F P (e v) (hK.height x)) := by
      funext z
      simp only [aff, IsIwasawaCompact.eisensteinTerm, IsIwasawaCompact.parameterTwist,
        IsIwasawaCompact.heightPower, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, x]
    rw [h]
    fun_prop
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm hb (fun c => (hterm c).differentiableOn)
    Metric.isOpen_ball (fun c z hz => hbound c g rfl (aff z)
      ⟨z, Metric.ball_subset_closedBall hz, rfl⟩)
  exact ((hdiff z₀ (Metric.mem_ball_self hδ)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))).differentiableWithinAt

end Regular

end Lines

end Langlands.Global.EisensteinGenericInjectivity
