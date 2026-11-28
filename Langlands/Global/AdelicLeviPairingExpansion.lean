import Langlands.Global.AdelicLeadingCuspidalComponents
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Norm-one Levi pairings of twisted finite expansions -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (𝓕 : StandardParabolicFamily F G)
  (J : StandardIndex F G 𝓕.i 𝓕.ν)

local notation "P" => 𝓕.P J
local notation "M" => 𝓕.M J
local notation "μ" => normOneRationalQuotientHaarMeasure F M

/-- The norm-one Levi pairings commute with multiplication by a scalar. -/
theorem leviPairing_const_mul (c : ℂ) (f : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ) :
    𝓕.leviPairing J (fun x => c * f x) g ψ = c * 𝓕.leviPairing J f g ψ := by
  unfold StandardParabolicFamily.leviPairing StandardParabolicFamily.leviPairingIntegrand
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_const_mul c _

section Twist

variable [IsClosedImmersion (𝓕.p J).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (𝓕.p J) K)

/-- The height twist is constant along each norm-one Levi translate used in a
cuspidal pairing. -/
theorem heightPower_normOneLevi_mul_self (m : normOneSubgroup F M)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower lam (AdelicGroupPoints.map F M G (𝓕.l J ≫ 𝓕.p J) m.val * g) =
      hK.heightPower lam g := by
  have hm : AdelicGroupPoints.map F M P (𝓕.l J) m.val ∈ normOneSubgroup F P :=
    map_normOneSubgroup_le F M P (𝓕.l J) ⟨m.val, m.property, rfl⟩
  simp only [IsIwasawaCompact.heightPower, map_comp_apply_of_hom, hK.height_map_mul,
    (characterLog_eq_zero_iff F P _).mpr hm, zero_add]

/-- The parameter twist may be taken outside the norm-one Levi pairing. -/
theorem leviPairing_parameterTwist (φ : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    (ψ : AdelicGroupPoints F M → ℂ) :
    𝓕.leviPairing J (hK.parameterTwist φ lam) g ψ =
      hK.heightPower lam g * 𝓕.leviPairing J φ g ψ := by
  unfold leviPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  simp only [leviPairingIntegrand, IsIwasawaCompact.parameterTwist,
    heightPower_normOneLevi_mul_self 𝓕 J hK]
  ac_rfl

end Twist

/-- Pairing a finite sum with the fixed test, when each summand has an
integrable pairing integrand. -/
theorem leviPairing_finsetSum {κ : Type*} (S : Finset κ)
    (a : κ → ℂ) (φ : κ → AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F M → ℂ)
    (hφ : ∀ i ∈ S, Integrable (𝓕.leviPairingIntegrand J (φ i) g ψ) μ) :
    𝓕.leviPairing J (fun x => ∑ i ∈ S, a i * φ i x) g ψ =
      ∑ i ∈ S, a i * 𝓕.leviPairing J (φ i) g ψ := by
  unfold leviPairing
  have heq (q : NormOneRationalQuotient F M) :
      𝓕.leviPairingIntegrand J (fun x => ∑ i ∈ S, a i * φ i x) g ψ q =
        ∑ i ∈ S, a i * 𝓕.leviPairingIntegrand J (φ i) g ψ q := by
    simp only [leviPairingIntegrand, Finset.sum_mul, mul_assoc]
  simp_rw [heq]
  rw [integral_finsetSum S (fun i hi => (hφ i hi).const_mul (a i))]
  simp only [integral_const_mul]

section Expansion

variable [IsClosedImmersion (𝓕.p J).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (𝓕.p J) K) {κ : Type*} (S : Finset κ)
  (φ : κ → AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
  (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ)

/-- The paired finite expansion consists of the common height power and the
fixed pairings with the expansion vectors. -/
def twistedLeviPairingExpansion (lam : ComplexCharacterParameter F P) (a : κ → ℂ) : ℂ :=
  hK.heightPower lam g * ∑ i ∈ S, a i * 𝓕.leviPairing J (φ i) g ψ

/-- Identify the finite expansion with the actual norm-one pairing of the
twisted family. -/
theorem leviPairing_parameterTwist_eq_expansion (lam : ComplexCharacterParameter F P)
    (a : κ → ℂ) (hφ : ∀ i ∈ S, Integrable (𝓕.leviPairingIntegrand J (φ i) g ψ) μ) :
    𝓕.leviPairing J (hK.parameterTwist (fun x => ∑ i ∈ S, a i * φ i x) lam) g ψ =
      𝓕.twistedLeviPairingExpansion J hK S φ g ψ lam a := by
  rw [leviPairing_parameterTwist, leviPairing_finsetSum 𝓕 J S a φ g ψ hφ]
  rfl

omit [IsClosedImmersion (𝓕.p J).hom.hom.left] in
/-- A scalar factor clearing each coefficient of a finite expansion also
clears its twisted norm-one Levi pairing. -/
theorem differentiableOn_mul_twistedLeviPairingExpansion {n : ℕ}
    (τ : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P)
    (a : κ → (Fin n → ℂ) → ℂ) {p : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)}
    (ha : ∀ i ∈ S, DifferentiableOn ℂ (fun s => p s * a i s) W) :
    DifferentiableOn ℂ (fun s => p s *
      𝓕.twistedLeviPairingExpansion J hK S φ g ψ (τ s) (fun i => a i s)) W := by
  have hpow : Differentiable ℂ (fun s => hK.heightPower (τ s) g) :=
    Complex.differentiable_exp.comp
      (((complexParameterPairing F P).flip (hK.height g)).comp τ).toContinuousLinearMap.differentiable
  have hsum : DifferentiableOn ℂ (fun s => ∑ i ∈ S,
      (p s * a i s) * 𝓕.leviPairing J (φ i) g ψ) W := by
    apply DifferentiableOn.fun_sum
    intro i hi
    exact (ha i hi).mul_const _
  refine (hpow.differentiableOn.mul hsum).congr fun s _ => ?_
  simp only [twistedLeviPairingExpansion, Pi.mul_apply, mul_left_comm (p s), Finset.mul_sum, mul_assoc]

omit [IsClosedImmersion (𝓕.p J).hom.hom.left] in
/-- Holomorphic extensions of cleared coefficients on one neighborhood give
an extension of the cleared twisted pairing on that neighborhood. -/
theorem exists_twistedLeviPairingExpansion_extension {n : ℕ}
    (τ : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P)
    (a : κ → (Fin n → ℂ) → ℂ) {p : (Fin n → ℂ) → ℂ} {W D : Set (Fin n → ℂ)}
    (ha : ∀ i ∈ S, ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b W ∧
      EqOn b (fun s => p s * a i s) (W ∩ D)) :
    ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b W ∧
      EqOn b (fun s => p s * 𝓕.twistedLeviPairingExpansion J hK S φ g ψ (τ s) (fun i => a i s))
        (W ∩ D) := by
  classical
  choose b hb hbeq using fun i : S => ha i i.property
  let c (i : κ) : (Fin n → ℂ) → ℂ := if hi : i ∈ S then b ⟨i, hi⟩ else 0
  have hc (i : κ) (hi : i ∈ S) : c i = b ⟨i, hi⟩ := by simp only [c, dite_eq_left hi]
  refine ⟨fun s => 𝓕.twistedLeviPairingExpansion J hK S φ g ψ (τ s) (fun i => c i s), ?_, ?_⟩
  · simpa only [one_mul] using
      differentiableOn_mul_twistedLeviPairingExpansion 𝓕 J hK S φ g ψ τ c
        (p := fun _ => 1) (fun i hi => by simpa only [one_mul, hc i hi] using hb ⟨i, hi⟩)
  · intro s hs
    change 𝓕.twistedLeviPairingExpansion J hK S φ g ψ (τ s) (fun i => c i s) =
      p s * 𝓕.twistedLeviPairingExpansion J hK S φ g ψ (τ s) (fun i => a i s)
    have hsum : (∑ i ∈ S, c i s * 𝓕.leviPairing J (φ i) g ψ) =
        p s * (∑ i ∈ S, a i s * 𝓕.leviPairing J (φ i) g ψ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have heq : b ⟨i, hi⟩ s = p s * a i s := hbeq ⟨i, hi⟩ hs
      rw [hc i hi, heq, mul_assoc]
    unfold twistedLeviPairingExpansion
    rw [hsum, mul_left_comm (p s)]

end Expansion

end Langlands.Global.StandardParabolicFamily
