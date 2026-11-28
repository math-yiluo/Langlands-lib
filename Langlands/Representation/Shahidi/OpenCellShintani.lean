import Langlands.Representation.Shahidi.OpenCellJacquet
import Langlands.Representation.Conductor.SphericalCentral

/-! # Shintani uniqueness for the Jacquet function of the two-block section

For `ψ` of conductor `𝒪`, the lift `F` of `δ_P^(1/2 + s/N) W°(·; a) ⊗ W°(·; c)` satisfies the
minuscule Hecke relations of the Satake parameter `χ = sectionParameter K a c s` at every point,
and `ϖ⁻¹` acts on it by `(∏ χ)⁻¹`. When the Jacquet integrands are integrable at every torus point, the Jacquet function
`J` therefore has the defining properties of the spherical Whittaker function, and the Library's
uniqueness theorem gives `J = J(1) · W°(·; χ)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.Unramified.MinusculeCosets
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocShintaniTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocShintaniValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocShintaniLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocShintaniT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocShintaniSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocShintaniMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocShintaniBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology}
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}

section HeckeEverywhere

include hϖ in
/-- **The minuscule Hecke relations of the lift at every point**, for `ψ` of conductor `𝒪` and a
system of representatives `σ` of the residue field. -/
theorem sum_liftFunction_fullΦ_mul_labelledRep
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    {Λ : Type*} [Fintype Λ] (σ : Λ → K.Carrier)
    (hcard : Fintype.card Λ = K.canonicalTopologicalData.residueCardinality)
    (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation K.Carrier).integer)
    (hinj : ∀ x y, ValuativeRel.valuation K.Carrier (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ (ValuativeRel.valuation K.Carrier).integer,
      ∃ x, ValuativeRel.valuation K.Carrier (z - σ x) < 1)
    (k : ℕ) (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    ∑ α : CosetIndex Λ ((r + 1) + (t + 1)) k,
        liftFunction hϖ (Base.fullΦ ψ hϖ a c s) (g * labelledRep ϖ σ α) =
      ((Real.sqrt (K.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^
          (k * (r + 1 + t + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple (sectionParameter K a c s)) k) *
        liftFunction hϖ (Base.fullΦ ψ hϖ a c s) g := by
  set E := (Real.sqrt (K.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^
      (k * (r + 1 + t + 1 - k)) *
    Langlands.Unramified.elementaryCoefficient
      (Langlands.Unramified.Eigenvalues.ofTuple (sectionParameter K a c s)) k with hE
  have hψI := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ a c s
  have hθ := isLeviEquivariant_fullΦ hϖ hψ a c s
  have hFb := isBlockEquivariant_liftFunction hϖ hΦ hθ
  have hFK := isRightIntegral_liftFunction hϖ hΦ
  set φ : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ :=
    fun g => ∑ α : CosetIndex Λ ((r + 1) + (t + 1)) k,
      liftFunction hϖ (Base.fullΦ ψ hϖ a c s) (g * labelledRep ϖ σ α) with hφ
  set φ' : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ :=
    fun g => E * liftFunction hϖ (Base.fullΦ ψ hϖ a c s) g with hφ'
  have hφb : IsBlockEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t) φ := by
    intro u hu g
    simp only [hφ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_assoc, hFb u hu]
  have hφ'b : IsBlockEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t) φ' := by
    intro u hu g
    simp only [hφ', hFb u hu]
    ring
  have hφK : IsRightIntegral (ValuativeRel.valuation K.Carrier) φ := by
    intro g κ hκ
    have h := minusculeSumOperator_mul_integral (R := ℂ) (n := r + 1 + t) hϖ σ hσ hinj hsurj k
      (liftFunction hϖ (Base.fullΦ ψ hϖ a c s)) hFK g hκ
    simp only [minusculeSumOperator_apply] at h
    simp only [hφ]
    exact h
  have hφ'K : IsRightIntegral (ValuativeRel.valuation K.Carrier) φ' := by
    intro g κ hκ
    simp only [hφ', hFK g κ hκ]
  have hnd₁ := fun i : Fin r => Base.standardCharacter_nondegenerate' hϖ hψI i
  have hnd₂ := fun i : Fin t => Base.standardCharacter_nondegenerate' hϖ hψI i
  have heq : φ = φ' := by
    apply eq_of_eval_torus hϖ hφb hφ'b hφK hφ'K
    intro ν
    by_cases h₁ : Antitone fun i : Fin (r + 1) => ν (i.castAdd (t + 1))
    · by_cases h₂ : Antitone fun j : Fin (t + 1) => ν (j.natAdd (r + 1))
      · exact sum_liftFunction_fullΦ_torus hϖ hψ a c s σ hcard hσ hinj hsurj h₁ h₂ k
      · rw [eval_torus_eq_zero_of_not_antitone_second hϖ hφb hφK hnd₂ h₂,
          eval_torus_eq_zero_of_not_antitone_second hϖ hφ'b hφ'K hnd₂ h₂]
    · rw [eval_torus_eq_zero_of_not_antitone_first hϖ hφb hφK hnd₁ h₁,
        eval_torus_eq_zero_of_not_antitone_first hϖ hφ'b hφ'K hnd₁ h₁]
  exact congrFun heq g

end HeckeEverywhere

section Central

include hϖ in
theorem twoBlockModulus_mul_torus_neg_one (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    twoBlockModulus K (m₁ * Iwasawa.torus ϖ (fun _ : Fin (r + 1) => (-1 : ℤ)))
        (m₂ * Iwasawa.torus ϖ (fun _ : Fin (t + 1) => (-1 : ℤ))) = twoBlockModulus K m₁ m₂ := by
  have h := twoBlockModulus_torus (K := K) hϖ (r := r) (t := t) (fun _ => -1) (fun _ => -1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_neg, nsmul_eq_mul,
    mul_one] at h
  have e : ((r + 1 : ℕ) : ℤ) * -((t + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) * -((r + 1 : ℕ) : ℤ) = 0 := by
    ring
  push_cast at h e
  rw [e, zpow_zero] at h
  unfold twoBlockModulus at h ⊢
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, NNReal.coe_mul, NNReal.coe_mul, mul_pow,
    mul_pow, mul_div_mul_comm, h, mul_one]

include hϖ in
/-- For `ψ` of conductor `𝒪`, the central element `ϖ⁻¹` acts on the lift by `(∏ a ∏ c)⁻¹`. -/
theorem liftFunction_fullΦ_mul_torus_neg_one
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (h : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ (Base.fullΦ ψ hϖ a c s)
        (h * Iwasawa.torus ϖ (fun _ : Fin ((r + 1) + (t + 1)) => (-1 : ℤ))) =
      ((∏ i, (a i : ℂ)) * ∏ j, (c j : ℂ))⁻¹ * liftFunction hϖ (Base.fullΦ ψ hϖ a c s) h := by
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ a c s
  set z₁ := Iwasawa.torus ϖ (fun _ : Fin (r + 1) => (-1 : ℤ))
  set z₂ := Iwasawa.torus ϖ (fun _ : Fin (t + 1) => (-1 : ℤ))
  have hz : Iwasawa.torus ϖ (fun _ : Fin ((r + 1) + (t + 1)) => (-1 : ℤ)) =
      ((liftLevi K r t z₁ z₂ : (liftShape r t).parabolic K.Carrier) :
        Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) := by
    rw [liftLevi_val, RankinSelberg.TwoBlockDominantRectangular.blockSum_torus]
    congr 1
    funext i
    induction i using Fin.addCases <;> simp
  have hc : h * Iwasawa.torus ϖ (fun _ : Fin ((r + 1) + (t + 1)) => (-1 : ℤ)) =
      Iwasawa.torus ϖ (fun _ : Fin ((r + 1) + (t + 1)) => (-1 : ℤ)) * h :=
    (torus_const_commute (n := r + 1 + t) (-1) h).symm
  rw [hc, hz]
  obtain ⟨m₁, m₂, h1, h2⟩ := liftFunction_parabolic_mul_left hϖ hΦ (liftLevi K r t z₁ z₂) h
  rw [h1, h2, liftFirst_liftLevi, liftSecond_liftLevi, torus_const_commute (n := r),
    torus_const_commute (n := t)]
  simp only [Base.fullΦ]
  rw [twoBlockModulus_mul_torus_neg_one hϖ,
    sphericalWhittaker_mul_torus_neg_one hϖ _ (isIntegrallyTrivial_of_additiveConductor K hψ r),
    sphericalWhittaker_mul_torus_neg_one hϖ _ (isIntegrallyTrivial_of_additiveConductor K hψ t)]
  rw [mul_inv]
  ring

theorem prod_sectionParameter (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    (∏ i, (sectionParameter K a c s i : ℂ)) = (∏ i, (a i : ℂ)) * ∏ j, (c j : ℂ) := by
  rw [Fin.prod_univ_add]
  simp only [sectionParameter_castAdd, sectionParameter_natAdd, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hq : (K.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 := by
    exact_mod_cast (residueCardinality_pos K).ne'
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul]
  have e : ((r + 1 : ℕ) : ℂ) * -(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) +
      ((t + 1 : ℕ) : ℂ) * (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) = 0 := by
    ring
  calc (∏ i, (a i : ℂ)) * (K.canonicalTopologicalData.residueCardinality : ℂ) ^
          (((r + 1 : ℕ) : ℂ) * -(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) *
        ((∏ j, (c j : ℂ)) * (K.canonicalTopologicalData.residueCardinality : ℂ) ^
          (((t + 1 : ℕ) : ℂ) * (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)))) =
      (∏ i, (a i : ℂ)) * (∏ j, (c j : ℂ)) *
        (K.canonicalTopologicalData.residueCardinality : ℂ) ^
          (((r + 1 : ℕ) : ℂ) * -(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) +
            ((t + 1 : ℕ) : ℂ) * (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) := by
        rw [Complex.cpow_add _ _ hq]
        ring
    _ = _ := by rw [e, Complex.cpow_zero, mul_one]

end Central

section Jacquet

variable (ψ)
variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
    Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

/-- A Hecke relation of the lift holding at every point passes to the Jacquet function at `g`
when the translated integrands at `g` are integrable. -/
theorem sum_jacquetFunction_mul_labelledRep {Λ : Type*} [Fintype Λ] (σ : Λ → K.Carrier) (k : ℕ)
    (E : ℂ)
    (hF : ∀ h, ∑ α : CosetIndex Λ ((r + 1) + (t + 1)) k,
      liftFunction hϖ Φ (h * labelledRep ϖ σ α) = E * liftFunction hϖ Φ h)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hint : ∀ α : CosetIndex Λ ((r + 1) + (t + 1)) k,
      Integrable (jacquetIntegrandAt ψ hϖ Φ (g * labelledRep ϖ σ α))
        (matrixHaar K (t + 1) (r + 1))) :
    ∑ α : CosetIndex Λ ((r + 1) + (t + 1)) k, jacquetFunction ψ hϖ Φ (g * labelledRep ϖ σ α) =
      E * jacquetFunction ψ hϖ Φ g := by
  unfold jacquetFunction
  rw [← integral_finsetSum _ (fun α _ => hint α), ← integral_const_mul]
  congr 1
  funext Y
  simp only [jacquetIntegrandAt_apply, ← Finset.mul_sum]
  have h := hF (blockWeyl (r + 1) (t + 1) K.Carrier *
    intertwiningUnipotent (r + 1) (t + 1) K.Carrier Y * g)
  simp only [mul_assoc] at h ⊢
  rw [h]
  ring

/-- A central relation of the lift holding at every point passes to the Jacquet function. -/
theorem jacquetFunction_mul_torus_neg_one (ω : ℂ)
    (hF : ∀ h, liftFunction hϖ Φ
      (h * Iwasawa.torus ϖ (fun _ : Fin ((r + 1) + (t + 1)) => (-1 : ℤ))) =
        ω * liftFunction hϖ Φ h)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    jacquetFunction ψ hϖ Φ (g * Iwasawa.torus ϖ (fun _ : Fin ((r + 1) + (t + 1)) => (-1 : ℤ))) =
      ω * jacquetFunction ψ hϖ Φ g := by
  unfold jacquetFunction
  rw [← integral_const_mul]
  congr 1
  funext Y
  simp only [jacquetIntegrandAt_apply]
  rw [← mul_assoc _ g, hF]
  ring

/-- For a Levi-invariant `Φ` that is Levi-equivariant for the standard characters, integrability
at every torus point gives integrability everywhere. -/
theorem integrable_jacquetIntegrandAt_of_torus (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t) Φ)
    (hint : ∀ μ : Fin ((r + 1) + (t + 1)) → ℤ,
      Integrable (jacquetIntegrandAt ψ hϖ Φ (Iwasawa.torus ϖ μ)) (matrixHaar K (t + 1) (r + 1)))
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    Integrable (jacquetIntegrandAt ψ hϖ Φ g) (matrixHaar K (t + 1) (r + 1)) := by
  obtain ⟨u, hu, μ, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (n := r + 1 + t) hϖ g
  rw [jacquetIntegrandAt_mul_integral ψ hϖ hΦ _ k hk]
  exact integrable_jacquetIntegrandAt_unipotent_mul ψ hϖ hΦ hθ ⟨u, hu⟩ _ (hint μ)

end Jacquet

section Uniqueness

variable (ψ)

include hϖ in
/-- **Shintani uniqueness for the Jacquet function.** Let `ψ` have conductor `𝒪`. If the Jacquet
integrands of the lift of
`δ_P^(1/2 + s/N) W°(·; a) ⊗ W°(·; c)` are integrable at every torus point, the Jacquet function is
`J(1)` times the spherical Whittaker function of `χ = sectionParameter K a c s`. -/
theorem jacquetFunction_fullΦ_eq_smul (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (hint : ∀ μ : Fin ((r + 1) + (t + 1)) → ℤ,
      Integrable (jacquetIntegrandAt ψ hϖ (Base.fullΦ ψ hϖ a c s) (Iwasawa.torus ϖ μ))
        (matrixHaar K (t + 1) (r + 1))) :
    jacquetFunction ψ hϖ (Base.fullΦ ψ hϖ a c s) =
      jacquetFunction ψ hϖ (Base.fullΦ ψ hϖ a c s) 1 •
        GeneralLinear.Spherical.sphericalWhittaker (n := r + 1 + t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (r + 1 + t))
          K.canonicalTopologicalData.residueCardinality (sectionParameter K a c s) := by
  have hψI := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ a c s
  have hθ := isLeviEquivariant_fullΦ hϖ hψ a c s
  have hall := integrable_jacquetIntegrandAt_of_torus ψ hϖ hΦ hθ hint
  have hcard : Fintype.card K.canonicalTopologicalData.ResidueField =
      K.canonicalTopologicalData.residueCardinality := Nat.card_eq_fintype_card.symm
  apply eq_smul_sphericalWhittaker hϖ (residueCardinality_pos K) hcard
    (Langlands.Unramified.residueLift K) (Langlands.Unramified.residueLift_mem K)
    (fun x y h => Langlands.Unramified.residueLift_eq_of_lt_one K h)
    (fun z hz => Langlands.Unramified.exists_residueLift_lt_one K hz)
    (isIntegrallyTrivial_of_additiveConductor K hψ (r + 1 + t))
    (fun i => Base.standardCharacter_nondegenerate' hϖ hψI i)
  · exact fun u g => jacquetFunction_unipotent_mul ψ hϖ hΦ hθ u g
  · exact fun g k hk => jacquetFunction_mul_integral ψ hϖ hΦ g k hk
  · intro k _ _ g
    exact sum_jacquetFunction_mul_labelledRep ψ hϖ _ k _
      (fun h => sum_liftFunction_fullΦ_mul_labelledRep hϖ hψ a c s _ hcard
        (Langlands.Unramified.residueLift_mem K)
        (fun x y h => Langlands.Unramified.residueLift_eq_of_lt_one K h)
        (fun z hz => Langlands.Unramified.exists_residueLift_lt_one K hz) k h) g
      (fun α => hall _)
  · intro g
    refine (jacquetFunction_mul_torus_neg_one ψ hϖ _
      (fun h => liftFunction_fullΦ_mul_torus_neg_one hϖ hψ a c s h) g).trans ?_
    rw [show (∏ i : Fin (r + 1 + t + 1), (sectionParameter K a c s i : ℂ)) =
      (∏ i, (a i : ℂ)) * ∏ j, (c j : ℂ) from prod_sectionParameter a c s]

end Uniqueness

end Langlands.Shahidi.OpenCell
