import Langlands.Global.AdelicWeakConstantTermPairingPolynomials
import Langlands.Global.AdelicLeviPairingExpansion
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicTruncatedEisensteinPairing

/-! # The coroot polynomial in a normalized weak pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (Q : StandardIndex F G fam.i fam.ν)

local notation "P" => fam.P Q
local notation "M" => fam.M Q
local notation "p" => fam.p Q
local notation "j" => fam.l Q ≫ fam.p Q
local notation "Roots" => fam.relativeSimpleRoots Q
local notation "Fun" => (AdelicGroupPoints F G → ℂ)

attribute [local instance] isClosedImmersion_p

private theorem exists_polynomial_comp_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Ix : Type*} [Fintype Ix] (b : Ix → V) {d : ℕ} {f : V → ℂ} (hf : f ∈ polynomialFunctions V d) :
    ∃ poly : MvPolynomial Ix ℂ, ∀ x : Ix → ℝ,
      poly.eval (fun i => (x i : ℂ)) = f (∑ i, x i • b i) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, _, L, rfl⟩ := hf
    let H (s : Fin k) : MvPolynomial Ix ℂ :=
      ∑ i, MvPolynomial.C ((L s (b i) : ℝ) : ℂ) * MvPolynomial.X i
    refine ⟨∏ s, H s, fun x => ?_⟩
    have hH (s : Fin k) : (H s).eval (fun i => (x i : ℂ)) =
        ((L s (∑ i, x i • b i) : ℝ) : ℂ) := by
      simp only [H, map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
        map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    change MvPolynomial.eval (fun i => (x i : ℂ)) _ = _
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => hH s
  | zero => exact ⟨0, fun _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨p₁, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    exact ⟨p₁ + q, fun x => by simp only [map_add, hp, hq, Pi.add_apply]⟩
  | smul c f _ hf =>
    obtain ⟨p₁, hp⟩ := hf
    exact ⟨MvPolynomial.C c * p₁, fun x => by rw [map_mul, MvPolynomial.eval_C, hp, Pi.smul_apply, smul_eq_mul]⟩

private theorem parameterPower_neg_eq_conj_of_realPart_zero
    (lam : ComplexCharacterParameter F P) (hu : parameterRealPart F P lam = 0)
    (x : AdelicGroupPoints F P) :
    (starRingEnd ℂ) (parameterPower F P lam x) = parameterPower F P (-lam) x := by
  let t := complexParameterPairing F P lam (characterLog F P x)
  have ht : t.re = 0 := by
    change (complexParameterPairing F P lam (characterLog F P x)).re = 0
    rw [complexParameterPairing_re, hu, map_zero, LinearMap.zero_apply]
  rw [parameterPower, parameterPower, map_neg, LinearMap.neg_apply]
  change (starRingEnd ℂ) (Complex.exp t) = Complex.exp (-t)
  rw [← Complex.exp_conj]
  congr 1
  exact Complex.ext (by simp [ht]) (by simp)

private theorem halfModulus_sq_eq_parameterPower (x : AdelicGroupPoints F P) :
    fam.halfModulus Q x ^ 2 = parameterPower F P (modulusParameter F P) x := by
  rw [pow_two, halfModulus, ← StandardParabolicFamily.parameterPower_add]
  congr 2
  simp only [halfModulusParameter, modulusParameter, ← TensorProduct.add_tmul]
  norm_num


private theorem heightPower_levi_slice {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p Q) K) (eta : ComplexCharacterParameter F P)
    (x : AdelicGroupPoints F P) (m : normOneSubgroup F M) (k : K) :
    hK.heightPower eta (map F P G p x * map F M G (j) m.val * k.val) = parameterPower F P eta x := by
  rw [mul_assoc, hK.heightPower_map_mul, fam.heightPower_normOneLevi_mul_self Q hK]
  have hk : hK.height k.val = 0 := by
    rw [hK.height_eq k.property (q := 1) (by rw [map_one, one_mul]), characterLog_one]
  simp only [IsIwasawaCompact.heightPower, hk, LinearMap.map_zero, Complex.exp_zero, mul_one]

/-- The normalized pairing of a height-twisted inducing section with a unitary exponent
component has exponent `eta - mu`. Its coroot polynomial is independent of the twist `eta`. -/
def NormalizedPairingCorootPolynomialStatement {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p Q) K) : Prop :=
  ∀ {φ ψ : Fun} {mu : ComplexCharacterParameter F P},
    IsSplitComponentEquivariant p (fam.l Q) φ → fam.HasExponent Q mu ψ →
    parameterRealPart F P mu = 0 →
    (∀ x ∈ fam.positiveSplitComponent Q,
      Integrable (fam.squareIntegrablePairingIntegrand K Q x φ ψ)
        (fam.squareIntegrablePairingMeasure K hK.isCompact Q)) →
    ∃ p₀ : MvPolynomial Roots ℂ,
      ∀ (eta : ComplexCharacterParameter F P) (x : fam.positiveSplitComponent Q),
        Integrable (fam.squareIntegrablePairingIntegrand K Q x.val (hK.parameterTwist φ eta) ψ)
          (fam.squareIntegrablePairingMeasure K hK.isCompact Q) ∧
        ∀ c : Roots → ℝ, characterLog F P x.val = ∑ α, c α • fam.relativeCoroot Q α →
          fam.normalizedPairing K hK.isCompact Q x.val (hK.parameterTwist φ eta) ψ =
            Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (eta - mu) α) *
              p₀.eval (fun α => (c α : ℂ))

set_option maxHeartbeats 2000000 in
theorem normalizedPairingCorootPolynomial {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p Q) K) : fam.NormalizedPairingCorootPolynomialStatement Q hK := by
  intro φ ψ mu hφ hψ hunit hint
  obtain ⟨n, q, hq, hpair⟩ := fam.squareIntegrablePairing_polynomial_of_integrable Q K hK.isCompact hφ hψ hint
  obtain ⟨p₀, hp₀⟩ := exists_polynomial_comp_sum (fam.relativeCoroot Q) hq
  refine ⟨p₀, fun eta x => ?_⟩
  have hfac (z : K × NormOneRationalQuotient F M) :
      fam.squareIntegrablePairingIntegrand K Q x.val (hK.parameterTwist φ eta) ψ z =
        parameterPower F P eta x.val * fam.squareIntegrablePairingIntegrand K Q x.val φ ψ z := by
    unfold squareIntegrablePairingIntegrand IsIwasawaCompact.parameterTwist
    rw [fam.heightPower_levi_slice Q hK eta x.val z.2.out z.1]
    ring
  refine ⟨((hint x.val x.property).const_mul _).congr (Filter.Eventually.of_forall fun z => (hfac z).symm), ?_⟩
  intro c hc
  unfold normalizedPairing
  simp_rw [hfac]
  rw [integral_const_mul, hpair x.val x.property, fam.halfModulus_sq_eq_parameterPower Q,
    fam.parameterPower_neg_eq_conj_of_realPart_zero Q mu hunit, hp₀, ← hc]
  have hpow : parameterPower F P (eta - mu) x.val =
      parameterPower F P eta x.val * parameterPower F P (-mu) x.val := by
    rw [sub_eq_add_neg, StandardParabolicFamily.parameterPower_add]
  have hc₀ : parameterPower F P (eta - mu) x.val =
      Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (eta - mu) α) := by
    simp only [parameterPower, hc, map_sum, map_smul, corootValue, Complex.real_smul]
  rw [← hc₀, hpow]
  have hne : parameterPower F P (modulusParameter F P) x.val ≠ 0 := Complex.exp_ne_zero _
  calc
    _ = (parameterPower F P (modulusParameter F P) x.val)⁻¹ *
        parameterPower F P (modulusParameter F P) x.val *
        (parameterPower F P eta x.val * parameterPower F P (-mu) x.val) *
          q (characterLog F P x.val) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hne, one_mul]

end Langlands.Global.StandardParabolicFamily
