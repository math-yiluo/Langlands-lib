import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands
import Langlands.Analysis.Local.QuotientTopology
import Langlands.Group.GL.CountabilityProof

/-!
# Adapters for the first-block Laurent assembly

The descended row character `[v] ↦ ψ((x v⁻¹)_0)` on the small quotient, joint
measurability of the fiber maps, and the vanishing of the two large integrands when
the test functional or the first block functional is zero.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient
  TwoBlockLowerUnipotentQuotient HarmonicAnalysis QuotientIntegration Whittaker

universe uF uW uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

section RowCharacter

variable (ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (n : ℕ)

/-- The row character `[v] ↦ ψ((x v⁻¹)_0)` on `N \ GL_(n+1)`, by actual descent: right
multiplication of a row by an upper unipotent matrix does not change its first entry. -/
def firstRowCharacter (x : Fin (n + 1) → F.Carrier) :
    LeftUnipotentQuotient n F.Carrier → ℂ :=
  letI := F.canonicalTopologicalData.topology
  descend (upperUnipotent (n + 1) F.Carrier)
    (fun v => ψ.complex (Matrix.vecMul x (v⁻¹).val 0))
    (fun u v => by
      change ψ.complex (Matrix.vecMul x ((u.val * v)⁻¹).val 0) =
        ψ.complex (Matrix.vecMul x (v⁻¹).val 0)
      rw [mul_inv_rev, Units.val_mul, ← Matrix.vecMul_vecMul]
      exact congrArg ψ.complex (TwoBlockLowerUnfolding.vecMul_upperUnipotent_zero _ u⁻¹))

@[simp]
theorem firstRowCharacter_mk (x : Fin (n + 1) → F.Carrier)
    (v : GeneralLinear (n + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    firstRowCharacter ψ n x (Quotient.mk _ v) = ψ.complex (Matrix.vecMul x (v⁻¹).val 0) :=
  rfl

theorem norm_firstRowCharacter (x : Fin (n + 1) → F.Carrier)
    (q : LeftUnipotentQuotient n F.Carrier) :
    ‖firstRowCharacter ψ n x q‖ = 1 := by
  let := F.canonicalTopologicalData.topology
  induction q using Quotient.inductionOn with
  | h v => exact ψ.norm_complex _

theorem continuous_firstRowCharacter :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    Continuous (fun p : (Fin (n + 1) → F.Carrier) × LeftUnipotentQuotient n F.Carrier =>
      firstRowCharacter ψ n p.1 p.2) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  have hq : Topology.IsQuotientMap (Prod.map (id : (Fin (n + 1) → F.Carrier) → _)
      (leftQuotientMap (upperUnipotent (n + 1) F.Carrier))) :=
    (IsOpenQuotientMap.id.prodMap (leftQuotient_isOpenQuotientMap _)).isQuotientMap
  refine hq.continuous_iff.mpr ?_
  change Continuous (fun p : (Fin (n + 1) → F.Carrier) × GeneralLinear (n + 1) F.Carrier =>
    ψ.complex (Matrix.vecMul p.1 (p.2⁻¹).val 0))
  refine ψ.continuous_complex.comp ?_
  have hinv : Continuous fun g : GeneralLinear (n + 1) F.Carrier => (g⁻¹).val :=
    Units.continuous_coe_inv
  exact (continuous_apply 0).comp
    (Continuous.matrix_vecMul continuous_fst (hinv.comp continuous_snd))

/-- Joint almost-everywhere strong measurability of the row character for every measure
on the product of rows and the Borel small quotient. -/
theorem aestronglyMeasurable_firstRowCharacter :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
    ∀ ρ : Measure ((Fin (n + 1) → F.Carrier) × LeftUnipotentQuotient n F.Carrier),
      AEStronglyMeasurable (Function.uncurry (firstRowCharacter ψ n)) ρ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  have := T.secondCountableTopology
  have := T.generalLinearSecondCountableTopology (n + 1)
  let := T.generalLinearTopologicalGroup (n + 1)
  have : SecondCountableTopology (LeftUnipotentQuotient n F.Carrier) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  intro ρ
  exact (continuous_firstRowCharacter ψ n).aestronglyMeasurable

end RowCharacter

section FiberMeasurability

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Joint almost-everywhere strong measurability of `(Z, q) ↦ E([diag(v_q, 1) R(Z) g])`
for continuous `E`. -/
theorem aestronglyMeasurable_comp_fiberPoint_lowerRadical
    (E : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
    Continuous E →
    ∀ ρ : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
        LeftUnipotentQuotient (m 0) F.Carrier),
      AEStronglyMeasurable (Function.uncurry fun Z x =>
        E (fiberPoint h F.Carrier x (lowerRadical h F.Carrier Z * g))) ρ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
  have := T.secondCountableTopology
  have := T.generalLinearSecondCountableTopology (m 0 + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := T.generalLinearTopologicalGroup (t + 1)
  have : SecondCountableTopology (LeftUnipotentQuotient (m 0) F.Carrier) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  have : SecondCountableTopology (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin (m 1 + 1) → Fin (m 0 + 1) → F.Carrier))
  have : OpensMeasurableSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :=
    inferInstanceAs (OpensMeasurableSpace (Fin (m 1 + 1) → Fin (m 0 + 1) → F.Carrier))
  intro hE ρ
  have hc : Continuous (fun p : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
      LeftUnipotentQuotient (m 0) F.Carrier =>
      E (fiberPoint h F.Carrier p.2 (lowerRadical h F.Carrier p.1 * g))) :=
    hE.comp ((continuous_fiberPoint F h).comp (continuous_snd.prodMk
      (((TwoBlockLowerFirstBlockQuotient.continuous_lowerRadical h F.Carrier).comp continuous_fst).mul continuous_const)))
  exact hc.aestronglyMeasurable

end FiberMeasurability

section Degenerate

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}

/-- A zero first functional makes every scalar section vanish. -/
theorem scalarSection_eq_zero_of_first (ell : ∀ i, W i →ₗ[ℂ] ℂ) (h0 : ell 0 = 0)
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier)
    (a : (succBlockShape m h).Levi F.Carrier) : scalarSection ell f g a = 0 := by
  rw [scalarSection_def]
  generalize (succBlockShape m h).blockTensor σ a (sectionEval F h σ f g) = X
  induction X using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, tensorContraction_tprod, Fin.prod_univ_two, h0, LinearMap.zero_apply,
      zero_mul, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}

/-- The upper integrand vanishes for a zero first functional. -/
theorem upperIntegrand_eq_zero_of_first
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i)) (h0 : (ell 0).val = 0)
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier)) :
    TwoBlockUnfolding.integrand ell f Wtest Φ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockUnfolding.integrand_mk, scalarSection_eq_zero_of_first _ h0, mul_zero, zero_mul]
    rfl

/-- The upper integrand vanishes for a zero test function. -/
theorem upperIntegrand_eq_zero_of_test
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t) (hW : Wtest.val = 0)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier)) :
    TwoBlockUnfolding.integrand ell f Wtest Φ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockUnfolding.integrand_mk, hW, Pi.zero_apply, zero_mul, zero_mul]
    rfl

/-- The lower integrand vanishes for a zero first functional. -/
theorem lowerIntegrand_eq_zero_of_first [MeasurableSpace F.Carrier]
    [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i)) (h0 : (ell 0).val = 0)
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier) :
    TwoBlockLowerUnfolding.integrand ell f Wtest Φ μ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockLowerUnfolding.integrand_mk, scalarSection_eq_zero_of_first _ h0, mul_zero,
      zero_mul]
    rfl

/-- The lower integrand vanishes for a zero test function. -/
theorem lowerIntegrand_eq_zero_of_test [MeasurableSpace F.Carrier]
    [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t) (hW : Wtest.val = 0)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier) :
    TwoBlockLowerUnfolding.integrand ell f Wtest Φ μ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockLowerUnfolding.integrand_mk, hW, Pi.zero_apply, zero_mul, zero_mul]
    rfl

/-- Every vector of the coefficient image of a zero functional is the zero function. -/
theorem coefficientModel_val_eq_zero {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V}
    {lambda : letI := F.canonicalTopologicalData.topology; glFunctionals ψ t π}
    (hlam : lambda.val = 0)
    (Wtest : letI := F.canonicalTopologicalData.topology
      (coefficientModel π lambda).toSubmodule) :
    Wtest.val.val = 0 := by
  obtain ⟨v, hv⟩ := Wtest.property
  rw [← hv]
  funext g
  change lambda.val (π g v) = 0
  rw [hlam, LinearMap.zero_apply]

end Degenerate

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
