import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicHeightPowerPolynomialBound
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Global polynomial majorants for the absolute Eisenstein series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)

include hN in
/-- A positive envelope on the original left quotient controls all right
translates by one polynomial weight. Only invariance and moderate growth are used. -/
private theorem exists_moderateGrowthEnvelope (Γ : Subgroup (AdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) (hinv : IsLeftInvariantUnder F G Γ φ)
    (hφ : HasModerateGrowthFunction F G rho φ) :
    ∃ (ψ : AdelicGroupPoints F G → ℂ) (A d : ℝ),
      IsLeftInvariantUnder F G Γ ψ ∧ HasModerateGrowthFunction F G rho ψ ∧
      0 < A ∧ 0 ≤ d ∧ ∀ x g : AdelicGroupPoints F G,
        ‖φ (x * g)‖ ≤ A * adelicHeight F G rho g ^ d * ‖ψ x‖ := by
  obtain ⟨d, hd, hb⟩ := HasModerateGrowthFunction.exists_compact_mul_le_height hφ
  obtain ⟨A, hA, hAt⟩ := hb {1} isCompact_singleton
  let H := adelicHeight F G rho
  have hH (x : AdelicGroupPoints F G) : 1 ≤ H x := one_le_adelicHeight F G rho hN x
  have hBound (x : AdelicGroupPoints F G) : ‖φ x‖ ≤ A * H x ^ d := by
    simpa only [mul_one, adelicHeightAtLeastOne_eq hN] using hAt x 1 (Set.mem_singleton 1)
  let height (x : AdelicGroupPoints F G) (y : Γ) := H (y.val * x) ^ d
  let envelope (x : AdelicGroupPoints F G) : ℝ := ⨅ y : Γ, height x y
  have hHeight₁ (x : AdelicGroupPoints F G) (y : Γ) : 1 ≤ height x y :=
    Real.one_le_rpow (hH _) hd
  have hLower (x : AdelicGroupPoints F G) : 1 ≤ envelope x :=
    le_ciInf (hHeight₁ x)
  have hUpper (x : AdelicGroupPoints F G) : envelope x ≤ H x ^ d := by
    have hb : BddBelow (Set.range (height x)) :=
      ⟨1, by rintro _ ⟨y, rfl⟩; exact hHeight₁ x y⟩
    have h := ciInf_le hb (1 : Γ)
    simpa only [height, Subgroup.coe_one, one_mul] using h
  let ψ (x : AdelicGroupPoints F G) : ℂ := envelope x
  have hψNorm (x : AdelicGroupPoints F G) : ‖ψ x‖ = envelope x :=
    Complex.norm_of_nonneg (zero_le_one.trans (hLower x))
  refine ⟨ψ, A, d, ?_, ?_, hA, hd, ?_⟩
  · intro z hz x
    have hrange : Set.range (height (z * x)) = Set.range (height x) := by
      ext r
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y * ⟨z, hz⟩, by simp only [height, Subgroup.coe_mul, mul_assoc]⟩
      · rintro ⟨y, rfl⟩
        refine ⟨y * (⟨z, hz⟩ : Γ)⁻¹, ?_⟩
        simp only [height, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
    exact congrArg (fun S : Set ℝ => ((sInf S : ℝ) : ℂ)) hrange
  · let scale : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hscale : 0 < scale := pow_pos (Nat.cast_pos.mpr hN) _
    refine ⟨scale ^ d, Real.rpow_pos_of_pos hscale _, d, fun x => ?_⟩
    rw [hψNorm]
    refine (hUpper x).trans_eq ?_
    change adelicHeight F G rho x ^ d = _
    have hEq : adelicHeight F G rho x = scale * adelicSourceNorm F G rho x :=
      adelicHeight_eq_scalar_mul_sourceNorm F G rho x
    have hmul : 0 ≤ scale * adelicSourceNorm F G rho x := hEq ▸ (zero_le_one.trans (hH x))
    rw [hEq, Real.mul_rpow hscale.le (nonneg_of_mul_nonneg_right hmul hscale)]
  · intro x g
    let C := A * H g ^ d
    have hC : 0 < C := mul_pos hA (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hH g)) _)
    have h := le_ciInf (show ∀ y : Γ, ‖φ (x * g)‖ / C ≤ height x y from fun y => by
      apply (div_le_iff₀ hC).mpr
      rw [← hinv y.val y.property (x * g), ← mul_assoc]
      calc
        _ ≤ A * H ((y.val * x) * g) ^ d := hBound _
        _ ≤ A * (H (y.val * x) * H g) ^ d :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (zero_le_one.trans (hH _))
            (adelicHeight_mul_le F G rho hN _ _) hd) hA.le
        _ = _ := by
          dsimp only [C, height]
          rw [Real.mul_rpow (zero_le_one.trans (hH _)) (zero_le_one.trans (hH _))]
          ring)
    rw [hψNorm]
    exact (div_le_iff₀ hC).mp h |>.trans_eq (mul_comm _ _)

/-- For a sufficiently regular parameter, the absolute values of the actual
Eisenstein terms admit a summable coset majorant times a polynomial in the
external adelic argument. -/
def EisensteinGlobalMajorantStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) {N : ℕ}
      (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
      ∀ φ : AdelicGroupPoints F G → ℂ,
        IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ →
        HasModerateGrowthFunction F G rho φ →
        ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam →
          ∃ (b : ParabolicRationalCosets F p → ℝ) (d : ℝ),
            Summable b ∧ (∀ x, 0 ≤ b x) ∧ 0 ≤ d ∧
            ∀ g x, ‖hK.eisensteinTerm φ lam g x‖ ≤ b x * adelicHeight F G rho g ^ d

set_option maxHeartbeats 1200000 in
theorem eisensteinGlobalMajorant : EisensteinGlobalMajorantStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N rho hN hrho φ hinv hφ
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨ψ, C, e, hψ, hψGrowth, hC, he, hEnvelope⟩ :=
    exists_moderateGrowthEnvelope rho hN (parabolicQuotientSubgroup F p iU l) φ hinv hφ
  obtain ⟨n, j, σ, hstab⟩ := Chevalley.exists_line_stabilizer F G P p
    r.isCompatible.parabolic.isClosedSubgroup
  have hrep := exists_polynomial_rationalCoset_representatives rho σ j hG
    r.isCompatible.parabolic hstab
  obtain ⟨R, hsum⟩ := hK.exists_summable_eisenstein_majorant_of_projectiveRepresentatives
    r hA hT hG hU rho σ j hstab hrep ψ hψ hψGrowth
  refine ⟨R, fun lam hlam => ?_⟩
  obtain ⟨m, ⟨E⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  let spectral := E.symm lam
  have hreg (z : Fin m → ℂ) (hz : z ∈ ({spectral} : Set (Fin m → ℂ))) :
      r.IsRegularParameter hA hT R (E z) := by
    rw [Set.mem_singleton_iff.mp hz, show E spectral = lam from E.apply_symm_apply lam]
    exact hlam
  obtain ⟨b, hb, hb0⟩ := hsum {1} isCompact_singleton m E {spectral} isCompact_singleton hreg
  have hB (x : ParabolicRationalCosets F p) : ‖hK.eisensteinTerm ψ lam 1 x‖ ≤ b x := by
    simpa only [spectral, E.apply_symm_apply] using
      hb0 x 1 (Set.mem_singleton 1) spectral (Set.mem_singleton _)
  obtain ⟨D, d, hD, hd, hHeight⟩ := hK.iwasawaHeightPowerPolynomialBound rho hN hrho lam
  refine ⟨fun x => C * D * b x, e + d, hb.mul_left _, fun x => ?_, add_nonneg he hd, fun g x => ?_⟩
  · exact mul_nonneg (mul_nonneg hC.le hD.le) ((norm_nonneg _).trans (hB x))
  have hψAt : ‖hK.parameterTwist ψ lam (Quotient.out x : rationalSubgroup F G)‖ ≤ b x := by
    simpa only [IsIwasawaCompact.eisensteinTerm, mul_one] using hB x
  change ‖hK.parameterTwist φ lam ((Quotient.out x : rationalSubgroup F G).val * g)‖ ≤ _
  unfold IsIwasawaCompact.parameterTwist at hψAt ⊢
  rw [norm_mul] at hψAt ⊢
  let y := (Quotient.out x : rationalSubgroup F G).val
  let H := adelicHeight F G rho g
  calc
    _ ≤ (C * H ^ e * ‖ψ y‖) * (D * H ^ d * ‖hK.heightPower lam y‖) :=
      mul_le_mul (hEnvelope y g) (hHeight y g) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg
          (zero_le_one.trans (one_le_adelicHeight F G rho hN g)) _)) (norm_nonneg _))
    _ = (C * D * (‖ψ y‖ * ‖hK.heightPower lam y‖)) * H ^ (e + d) := by
      rw [Real.rpow_add (zero_lt_one.trans_le (one_le_adelicHeight F G rho hN g))]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψAt (mul_nonneg hC.le hD.le))
      exact Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G rho hN g)) _

end Langlands.Global
