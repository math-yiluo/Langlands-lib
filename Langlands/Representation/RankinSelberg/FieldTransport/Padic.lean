import Langlands.Representation.RankinSelberg.FieldTransport.Factors
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.LocalField.CanonicalTransport
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# p-adic JPSS factors along an isomorphism of p-adic fields

The normalized Haar measures of `GL_(n+1)` and of its upper unipotent subgroup
are carried onto each other by a field isomorphism that is a homeomorphism and
maps the integer ring onto the integer ring. For an isomorphism `f : F ≃ₐ[ℚ_p] E`
of p-adic fields this holds, and the residue cardinalities and normalized
absolute values also correspond. Consequently the p-adic L-polynomial and
epsilon relations `IsPadicPairLPolynomial`, `IsPadicPairEpsilonFactor` and their
symmetric versions hold for representations over `E` exactly when they hold for
the pulled-back representations over `F`, with the additive character and
additive Haar measure transported along `f`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Polynomial

universe uF uE uV uW uG uG'

namespace Langlands.RankinSelberg.FieldTransport

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration

section Haar

variable {G : Type uG} {G' : Type uG'} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [MeasurableSpace G'] [BorelSpace G']

/-- A topological group isomorphism carrying one compact-open subgroup onto
another carries the Haar measure normalized on the first onto the Haar measure
normalized on the second. -/
theorem normalizedCompactOpenHaar_map (Θ : G ≃ₜ* G') (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (K' : OpenSubgroup G') (hK' : IsCompact (K' : Set G'))
    (hKK' : ∀ g, Θ g ∈ K' ↔ g ∈ K) :
    (normalizedCompactOpenHaar K hK).map Θ = normalizedCompactOpenHaar K' hK' := by
  have : LocallyCompactSpace G' :=
    hK'.locallyCompactSpace_of_mem_nhds_of_group (K'.isOpen.mem_nhds K'.one_mem)
  have : (Measure.map Θ (normalizedCompactOpenHaar K hK)).Regular :=
    Measure.Regular.map Θ.toHomeomorph
  have hpre : Θ ⁻¹' (K' : Set G') = (K : Set G) := Set.ext hKK'
  have hval : (normalizedCompactOpenHaar K hK).map Θ (K' : Set G') = 1 := by
    rw [Measure.map_apply (map_continuous Θ).measurable K'.isOpen.measurableSet, hpre,
      normalizedCompactOpenHaar_self]
  have h := isMulLeftInvariant_eq_smul_of_regular
    ((normalizedCompactOpenHaar K hK).map Θ) (normalizedCompactOpenHaar K' hK')
  have hc : haarScalarFactor ((normalizedCompactOpenHaar K hK).map Θ)
      (normalizedCompactOpenHaar K' hK') = 1 := by
    have h1 := congrArg (fun m : Measure G' => m (K' : Set G')) h
    simp only [Measure.smul_apply, normalizedCompactOpenHaar_self, hval, ENNReal.smul_def,
      smul_eq_mul, mul_one] at h1
    exact_mod_cast h1.symm
  rw [h, hc, one_smul]

end Haar

section LocalField

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [ValuativeRel F] [ValuativeRel E]
  [TopologicalSpace F] [TopologicalSpace E]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField E]
  (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)
  (hO : ∀ x, σ x ∈ (ValuativeRel.valuation E).integer ↔ x ∈ (ValuativeRel.valuation F).integer)

include hO in
/-- A field isomorphism preserving the integer rings preserves `GL_(n+1)(O)`. -/
theorem fieldEquiv_mem_levelOpenSubgroup_zero_iff (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    fieldEquiv (n + 1) σ hσ hσs g ∈ Conductor.levelOpenSubgroup E n 0 ↔
      g ∈ Conductor.levelOpenSubgroup F n 0 := by
  change fieldEquiv (n + 1) σ hσ hσs g ∈ Conductor.levelSubgroup E n 0 ↔
    g ∈ Conductor.levelSubgroup F n 0
  rw [Conductor.levelSubgroup_zero, Conductor.levelSubgroup_zero,
    Conductor.mem_integralSubgroup, Conductor.mem_integralSubgroup, ← map_inv]
  simp only [fieldEquiv_apply, hO]

include hO in
/-- The normalized Haar measure of `GL_(n+1)` over `E` is the pushforward of
the one over `F`. -/
theorem generalLinearHaar_map (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) E)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) E)] :
    (generalLinearHaar F n).map (fieldEquiv (n + 1) σ hσ hσs) = generalLinearHaar E n :=
  normalizedCompactOpenHaar_map _ _ _ _ _
    (fieldEquiv_mem_levelOpenSubgroup_zero_iff σ hσ hσs hO n)

include hO in
/-- The normalized Haar measure of the upper unipotent subgroup over `E` is the
pushforward of the one over `F`. -/
theorem unipotentHaar_map (n : ℕ)
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) E)] [BorelSpace (upperUnipotent (n + 1) E)] :
    (unipotentHaar F n).map (unipotentEquiv σ hσ hσs (n + 1)) = unipotentHaar E n :=
  normalizedCompactOpenHaar_map _ _ _ _ _
    (fun u => fieldEquiv_mem_levelOpenSubgroup_zero_iff σ hσ hσs hO n u.val)

end LocalField

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- An isomorphism of p-adic fields preserves the canonical integer rings. -/
theorem algEquiv_mem_integers_iff (x : F.Carrier) :
    f x ∈ E.canonicalTopologicalData.Integers ↔ x ∈ F.canonicalTopologicalData.Integers := by
  constructor
  · intro h
    have hx := (Weil.Local.extensionIntegerMap E F f.symm.toAlgHom ⟨f x, h⟩).property
    simpa using hx
  · intro h
    exact (Weil.Local.extensionIntegerMap F E f.toAlgHom ⟨x, h⟩).property

/-- The entrywise isomorphism of general linear groups induced by an
isomorphism of p-adic fields. -/
def padicGeneralLinearEquiv (n : ℕ) :
    Langlands.GeneralLinear n F.Carrier ≃* Langlands.GeneralLinear n E.Carrier :=
  letI := F.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.topology
  (fieldEquiv n f.toRingEquiv (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv F E f)
    (VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv E F f.symm)).toMulEquiv

@[simp]
theorem padicGeneralLinearEquiv_apply (n : ℕ) (g : Langlands.GeneralLinear n F.Carrier)
    (i j : Fin n) : padicGeneralLinearEquiv F E f n g i j = f (g i j) := rfl

variable {F E f}

/-- **p-adic L-polynomials along an isomorphism of p-adic fields.** For additive
characters and additive Haar measures related by `f`, `P` is the p-adic
L-polynomial of `(π, τ)` over `E` exactly when it is the p-adic L-polynomial
of the pulled-back pair over `F`. -/
theorem isPadicPairLPolynomial_comp_iff
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ψ' : letI := E.canonicalTopologicalData.topology; UnitaryAdditiveCharacter E.Carrier}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {ν' : letI := E.canonicalTopologicalData.topology; letI := borel E.Carrier
      AdditiveHaarMeasure E.Carrier}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    {r n : ℕ} (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E.Carrier) W) (P : ℂ[X]) :
    IsPadicPairLPolynomial E ψ' ν' π τ P ↔
      IsPadicPairLPolynomial F ψ ν (π.comp (padicGeneralLinearEquiv F E f (r + 1)).toMonoidHom)
        (τ.comp (padicGeneralLinearEquiv F E f (n + 1)).toMonoidHom) P := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := E.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel E.Carrier
  let : BorelSpace E.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) E.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) E.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) E.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) E.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n E.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n E.Carrier) := ⟨rfl⟩
  let := F.canonicalTopologicalData.sigmaCompactSpace
  let := E.canonicalTopologicalData.sigmaCompactSpace
  have hf := VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv F E f
  have hfs := VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv E F f.symm
  have hO : ∀ x, f.toRingEquiv x ∈ (ValuativeRel.valuation E.Carrier).integer ↔
      x ∈ (ValuativeRel.valuation F.Carrier).integer :=
    algEquiv_mem_integers_iff F E f
  have hU := (unipotentHaar_map f.toRingEquiv hf hfs hO n).symm
  have hG := (generalLinearHaar_map f.toRingEquiv hf hfs hO n).symm
  have habv : ∀ x, normalizedAbsoluteValue E.canonicalTopologicalData (f.toRingEquiv x) =
      normalizedAbsoluteValue F.canonicalTopologicalData x :=
    PadicField.CanonicalTransport.normalizedAbs_map F E f
  have hinv := isMulRightInvariant_unipotentHaar_iff f.toRingEquiv hf hfs hU
  unfold IsPadicPairLPolynomial
  rw [PadicField.CanonicalTransport.residueCardinality_eq F E f]
  constructor
  · rintro ⟨⟨hE, hcE⟩, hall⟩
    have hF := hinv.1 hE
    refine ⟨⟨hF, (compatibleMeasureExists_unipotentHaar_iff f.toRingEquiv hf hfs hG hU).1 hcE⟩,
      ?_⟩
    intro _ μ hμ
    exact (isPairLPolynomial_comp_iff f.toRingEquiv hf hfs hψ habv _ μ ν ν' hν π τ P).1
      (hall (μ.map (quotientHomeomorph f.toRingEquiv hf hfs n))
        ((isCompatible_unipotentHaar_map_iff f.toRingEquiv hf hfs hG hU μ).2 hμ))
  · rintro ⟨⟨hF, hcF⟩, hall⟩
    have hE := hinv.2 hF
    refine ⟨⟨hE, (compatibleMeasureExists_unipotentHaar_iff f.toRingEquiv hf hfs hG hU).2 hcF⟩,
      ?_⟩
    intro _ μ₂ hμ₂
    obtain ⟨μ, rfl⟩ := exists_map_eq (fieldEquiv (n + 1) f.toRingEquiv hf hfs)
      (fieldEquiv_mem_upperUnipotent_iff f.toRingEquiv hf hfs) μ₂
    exact (isPairLPolynomial_comp_iff f.toRingEquiv hf hfs hψ habv _ μ ν ν' hν π τ P).2
      (hall μ ((isCompatible_unipotentHaar_map_iff f.toRingEquiv hf hfs hG hU μ).1 hμ₂))

/-- **p-adic epsilon factors along an isomorphism of p-adic fields.** For
additive characters and additive Haar measures related by `f`, `e` is the p-adic
epsilon factor of `(π, τ)` over `E` exactly when it is the p-adic epsilon factor
of the pulled-back pair over `F`. -/
theorem isPadicPairEpsilonFactor_comp_iff
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ψ' : letI := E.canonicalTopologicalData.topology; UnitaryAdditiveCharacter E.Carrier}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {ν' : letI := E.canonicalTopologicalData.topology; letI := borel E.Carrier
      AdditiveHaarMeasure E.Carrier}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    {r n : ℕ} (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E.Carrier) W) (e : ℂˣ × ℤ) :
    IsPadicPairEpsilonFactor E ψ' ν' π τ e ↔
      IsPadicPairEpsilonFactor F ψ ν
        (π.comp (padicGeneralLinearEquiv F E f (r + 1)).toMonoidHom)
        (τ.comp (padicGeneralLinearEquiv F E f (n + 1)).toMonoidHom) e := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := E.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel E.Carrier
  let : BorelSpace E.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) E.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) E.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) E.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) E.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n E.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n E.Carrier) := ⟨rfl⟩
  let := E.canonicalTopologicalData.sigmaCompactSpace
  have hf := VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv F E f
  have hfs := VirtualRepresentation.PadicSupercuspidal.continuous_algEquiv E F f.symm
  have hO : ∀ x, f.toRingEquiv x ∈ (ValuativeRel.valuation E.Carrier).integer ↔
      x ∈ (ValuativeRel.valuation F.Carrier).integer :=
    algEquiv_mem_integers_iff F E f
  have hU := (unipotentHaar_map f.toRingEquiv hf hfs hO n).symm
  have hG := (generalLinearHaar_map f.toRingEquiv hf hfs hO n).symm
  have habv : ∀ x, normalizedAbsoluteValue E.canonicalTopologicalData (f.toRingEquiv x) =
      normalizedAbsoluteValue F.canonicalTopologicalData x :=
    PadicField.CanonicalTransport.normalizedAbs_map F E f
  unfold IsPadicPairEpsilonFactor
  rw [PadicField.CanonicalTransport.residueCardinality_eq F E f]
  exact isPairEpsilonFactor_comp_iff f.toRingEquiv hf hfs hψ habv _ ν ν' hν hG hU π τ e

/-- The symmetric p-adic L-polynomial relation along an isomorphism of p-adic
fields. -/
theorem isPadicSymmetricLPolynomial_comp_iff
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ψ' : letI := E.canonicalTopologicalData.topology; UnitaryAdditiveCharacter E.Carrier}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {ν' : letI := E.canonicalTopologicalData.topology; letI := borel E.Carrier
      AdditiveHaarMeasure E.Carrier}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    {r n : ℕ} (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E.Carrier) W) (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial E ψ' ν' π τ P ↔
      IsPadicSymmetricLPolynomial F ψ ν
        (π.comp (padicGeneralLinearEquiv F E f (r + 1)).toMonoidHom)
        (τ.comp (padicGeneralLinearEquiv F E f (n + 1)).toMonoidHom) P := by
  unfold IsPadicSymmetricLPolynomial
  split_ifs
  · exact isPadicPairLPolynomial_comp_iff hψ hν π τ P
  · exact isPadicPairLPolynomial_comp_iff hψ hν τ π P

/-- The symmetric p-adic epsilon relation along an isomorphism of p-adic
fields. -/
theorem isPadicSymmetricEpsilonFactor_comp_iff
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ψ' : letI := E.canonicalTopologicalData.topology; UnitaryAdditiveCharacter E.Carrier}
    (hψ : ∀ x, ψ' (f x) = ψ x)
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {ν' : letI := E.canonicalTopologicalData.topology; letI := borel E.Carrier
      AdditiveHaarMeasure E.Carrier}
    (hν : letI := F.canonicalTopologicalData.topology; letI := E.canonicalTopologicalData.topology
      letI := borel F.Carrier; letI := borel E.Carrier; ν'.measure = ν.measure.map f)
    {r n : ℕ} (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E.Carrier) W) (e : ℂˣ × ℤ) :
    IsPadicSymmetricEpsilonFactor E ψ' ν' π τ e ↔
      IsPadicSymmetricEpsilonFactor F ψ ν
        (π.comp (padicGeneralLinearEquiv F E f (r + 1)).toMonoidHom)
        (τ.comp (padicGeneralLinearEquiv F E f (n + 1)).toMonoidHom) e := by
  unfold IsPadicSymmetricEpsilonFactor
  split_ifs
  · exact isPadicPairEpsilonFactor_comp_iff hψ hν π τ e
  · exact isPadicPairEpsilonFactor_comp_iff hψ hν τ π e

end Padic

end Langlands.RankinSelberg.FieldTransport
