import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicStandardPositiveLog
import Langlands.Global.AdelicExponentPolynomialIntegral

/-! # Polynomial dependence of the weak constant term pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

private theorem polynomialFunctions_conj {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {q : V → ℂ} (hq : q ∈ polynomialFunctions V n) :
    (fun v => (starRingEnd ℂ) (q v)) ∈ polynomialFunctions V n := by
  refine Submodule.span_induction (p := fun f _ =>
    (fun v => (starRingEnd ℂ) (f v)) ∈ polynomialFunctions V n) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨k, hk, ℓ, rfl⟩
    apply Submodule.subset_span
    exact ⟨k, hk, ℓ, by funext v; simp [map_prod]⟩
  · simp only [Pi.zero_apply, map_zero]
    exact (polynomialFunctions V n).zero_mem
  · intro f g _ _ hf hg
    simp only [Pi.add_apply, map_add]
    exact (polynomialFunctions V n).add_mem hf hg
  · intro a f _ hf
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact (polynomialFunctions V n).smul_mem ((starRingEnd ℂ) a) hf

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)
  (J : StandardIndex F G 𝓕.i 𝓕.ν)

private theorem splitComponentAction_inducing {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant (𝓕.p J) (𝓕.l J) φ)
    {x : AdelicGroupPoints F (𝓕.P J)} (hx : x ∈ 𝓕.positiveSplitComponent J)
    (g : AdelicGroupPoints F G) :
    φ (map F (𝓕.P J) G (𝓕.p J) x * g) = 𝓕.halfModulus J x * φ g := by
  obtain ⟨t, ht, rfl⟩ := hx
  have ha : map F (𝓕.A J).toGrp (𝓕.M J) (𝓕.a J) t ∈
      RestrictionSplitCentre.canonicalSubgroup F (𝓕.M J) := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup
      (𝓕.isCompatible J).splitComponent]
    exact ⟨t, ht, rfl⟩
  let x := map F (𝓕.A J).toGrp (𝓕.P J) (𝓕.a J ≫ 𝓕.l J) t
  change φ (map F (𝓕.P J) G (𝓕.p J) x * g) = 𝓕.halfModulus J x * φ g
  simpa only [x, halfModulus, map_comp_apply_of_hom] using hφ _ ha g

private theorem halfModulus_mul_conj (x : AdelicGroupPoints F (𝓕.P J)) :
    𝓕.halfModulus J x * (starRingEnd ℂ) (𝓕.halfModulus J x) =
      parameterPower F (𝓕.P J) (modulusParameter F (𝓕.P J)) x := by
  have hstar : (starRingEnd ℂ) (𝓕.halfModulus J x) = 𝓕.halfModulus J x := by
    rw [halfModulus_eq_sqrt]
    exact Complex.conj_ofReal _
  rw [hstar]
  unfold halfModulus
  rw [← parameterPower_add]
  congr 2
  simp only [halfModulusParameter, modulusParameter, ← add_tmul]
  norm_num

/-- Once all translated pairings with a normalized exponent component are integrable,
their integrals are its conjugate parameter times the modulus and a polynomial in the
split-component logarithm. The polynomial degree is bounded by the degree for the
component. -/
theorem squareIntegrablePairing_polynomial_of_integrable
    (K : Subgroup (AdelicGroupPoints F G)) (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    {lam : ComplexCharacterParameter F (𝓕.P J)} {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant (𝓕.p J) (𝓕.l J) φ)
    (hψ : 𝓕.HasExponent J lam ψ)
    (hint : ∀ x ∈ 𝓕.positiveSplitComponent J,
      Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ ψ)
        (𝓕.squareIntegrablePairingMeasure K hKc J)) :
    ∃ (n : ℕ) (q : RealCharacterDual F (𝓕.P J) → ℂ),
      q ∈ polynomialFunctions (RealCharacterDual F (𝓕.P J)) n ∧
      ∀ x ∈ 𝓕.positiveSplitComponent J,
      (∫ z, 𝓕.squareIntegrablePairingIntegrand K J x φ ψ z
        ∂(𝓕.squareIntegrablePairingMeasure K hKc J)) =
        parameterPower F (𝓕.P J) (modulusParameter F (𝓕.P J)) x *
          (starRingEnd ℂ) (parameterPower F (𝓕.P J) lam x) *
          q (characterLog F (𝓕.P J) x) := by
  classical
  let P := 𝓕.P J
  let ν := lam + halfModulusParameter F P
  obtain ⟨n, hQ⟩ := (𝓕.hasExponent_iff J lam ψ).mp hψ
  choose Q hQpoly hQ using hQ
  have hψvalue (g : AdelicGroupPoints F G) (x : AdelicGroupPoints F P)
      (hx : x ∈ 𝓕.positiveSplitComponent J) :
      ψ (map F P G (𝓕.p J) x * g) =
        (𝓕.halfModulus J x * parameterPower F P lam x) * Q g (characterLog F P x) := by
    have h := hQ g x hx
    change ψ (map F P G (𝓕.p J) x * g) * parameterPower F P (-ν) x = _ at h
    have hsum : parameterPower F P ν x = 𝓕.halfModulus J x * parameterPower F P lam x := by
      dsimp only [ν, halfModulus]
      rw [add_comm lam, parameterPower_add]
    have hcancel : parameterPower F P ν x * parameterPower F P (-ν) x = 1 := by
      rw [← parameterPower_add, add_neg_cancel]
      simp [parameterPower]
    rw [← h, ← hsum]
    calc
      _ = (parameterPower F P ν x * parameterPower F P (-ν) x) *
          ψ (map F P G (𝓕.p J) x * g) := by rw [hcancel, one_mul]
      _ = _ := by ring
  let base (z : K × NormOneRationalQuotient F (𝓕.M J)) : AdelicGroupPoints F G :=
    map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
      ((z.2.out : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
      (z.1 : AdelicGroupPoints F G)
  let w (x : AdelicGroupPoints F P) : ℂ :=
    parameterPower F P (modulusParameter F P) x * (starRingEnd ℂ) (parameterPower F P lam x)
  let f (z : K × NormOneRationalQuotient F (𝓕.M J)) (H : RealCharacterDual F P) : ℂ :=
    φ (base z) * (starRingEnd ℂ) (Q (base z) H)
  have hf (z : K × NormOneRationalQuotient F (𝓕.M J)) :
      f z ∈ polynomialFunctions (RealCharacterDual F P) n :=
    (polynomialFunctions _ n).smul_mem _ (polynomialFunctions_conj (hQpoly (base z)))
  have hfactor (x : AdelicGroupPoints F P) (hx : x ∈ 𝓕.positiveSplitComponent J)
      (z : K × NormOneRationalQuotient F (𝓕.M J)) :
      𝓕.squareIntegrablePairingIntegrand K J x φ ψ z = w x * f z (characterLog F P x) := by
    simp only [squareIntegrablePairingIntegrand, mul_assoc]
    change φ (map F P G (𝓕.p J) x * base z) *
      (starRingEnd ℂ) (ψ (map F P G (𝓕.p J) x * base z)) = _
    rw [𝓕.splitComponentAction_inducing J hφ hx, hψvalue _ _ hx]
    simp only [map_mul, w, f]
    rw [← 𝓕.halfModulus_mul_conj J x]
    ring
  obtain ⟨hDim, e, he⟩ := 𝓕.standardPositiveLog J
  let : FiniteDimensional ℝ (RealCharacterDual F P) := hDim
  let μPair := 𝓕.squareIntegrablePairingMeasure K hKc J
  have hInt (H : RealCharacterDual F P) : Integrable (fun z => f z H) μPair := by
    obtain ⟨x, hx⟩ := e.surjective (Multiplicative.ofAdd H)
    have hlog : characterLog F P x.val = H :=
      (he x).symm.trans (congrArg Multiplicative.toAdd hx)
    rw [← hlog]
    have hw : w x.val ≠ 0 := by
      exact mul_ne_zero (Complex.exp_ne_zero _) ((map_ne_zero (starRingEnd ℂ)).2 (Complex.exp_ne_zero _))
    refine ((hint x.val x.property).const_mul (w x.val)⁻¹).congr (Eventually.of_forall fun z => ?_)
    change (w x.val)⁻¹ * 𝓕.squareIntegrablePairingIntegrand K J x.val φ ψ z =
      f z (characterLog F P x.val)
    rw [hfactor x.val x.property z, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  refine ⟨n, fun H => ∫ z, f z H ∂μPair, exponentPolynomialIntegral n f μPair hf hInt, ?_⟩
  intro x hx
  simp_rw [hfactor x hx, integral_const_mul]
  rfl

end StandardParabolicFamily

/-- Absolute convergence of (3.7) for each unitary component in an exponent
decomposition of the constant term of a log-square-integrable automorphic form. -/
def WeakConstantTermComponentPairingIntegrableStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
      (Φ : AdelicGroupPoints F G → ℂ),
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν)
      (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
      (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ),
    𝓕.IsAutomorphicExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho
      J (𝓕.constantTerm J Φ) s c →
    ∀ lam ∈ s, parameterRealPart F (𝓕.P J) lam = 0 →
    ∀ (φ : AdelicGroupPoints F G → ℂ),
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ →
    ∀ x ∈ 𝓕.positiveSplitComponent J,
      Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ (c lam))
        (𝓕.squareIntegrablePairingMeasure K hK.isCompact J)

end Langlands.Global
