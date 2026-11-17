import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionFixedTensor
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket

/-! # Uniform coefficient bounds on a fixed section level -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ uB

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] [DecidableEq J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

set_option hygiene false in
local notation "CompactPicture" => ProductInducedCompactPicture h K π.obj
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "inputSeminorms" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "compactRestriction" => productInducedSmoothOrbitCompactRestriction
  h hU ν π K hP hK hν hr hPK e

/-- Finite coefficient coordinates turn vectorwise uniform bounds into one bound for an
entire section level, controlled by finitely many zero-order input seminorms. -/
theorem exists_levelFamily_bound_of_basis (H : OpenSubgroup G) (hHK : H ≤ K)
    {B : Type uB} [Fintype B] [DecidableEq B]
    (b : Module.Basis B ℂ (orbitSectionFixedCoefficients h K π H))
    (Ξ : G → ℝ)
    (a : (J → Circle) → G → (CompactPicture →ₗ[ℂ] ℂ))
    (ha : ∀ v : orbitSectionFixedCoefficients h K π H, ∃ C : ℝ≥0,
      ∀ (z : J → Circle) (g : G), ‖a z g v.val‖ ≤ (C : ℝ) * Ξ g) :
    ∃ t : Finset (Module.Dual ℂ CompactPicture), ∃ C : ℝ≥0,
      ∀ (q : SectionLevel H) (z : J → Circle) (g : G),
        ‖a z g (compactRestriction (includeLevel H q) z)‖ ≤
          (C : ℝ) * (t.sup fun ℓ => inputSeminorms H ([], ℓ)) q * Ξ g := by
  classical
  choose ℓ hℓ using fun i : B => (b.coord i).exists_extend
  choose C hC using fun i : B => ha (b i)
  let t : Finset (Module.Dual ℂ CompactPicture) := Finset.univ.image ℓ
  let c : ℝ≥0 := ⟨∑ i, (C i : ℝ), Finset.sum_nonneg fun i _ => (C i).coe_nonneg⟩
  refine ⟨t, c, fun q z g => ?_⟩
  let v := orbitSectionLevelFixedRestriction h K π ν e hU hP hK hν hr hPK H hHK q z
  have hcoordinate (i : B) :
      ‖b.coord i v‖ ≤ (t.sup fun ℓ => inputSeminorms H ([], ℓ)) q := by
    have he := LinearMap.congr_fun (hℓ i) v
    have hb := norm_torusPartialDerivList_le_orbitSectionSeminorm ν π e h hU K hP hK hν hr hPK
      [] (ℓ i) (includeLevel H q) z
    have hb' : ‖b.coord i v‖ ≤ (inputSeminorms H ([], ℓ i)) q := by
      change ‖ℓ i v.val‖ ≤ (inputSeminorms H ([], ℓ i)) q at hb
      have he' : ℓ i v.val = b.coord i v := he
      rw [he'] at hb
      exact hb
    exact hb'.trans ((Finset.le_sup (f := fun ℓ => inputSeminorms H ([], ℓ))
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)) q)
  have hexpand : ∑ i, b.coord i v * a z g (b i).val = a z g v.val := by
    have he := congrArg ((a z g).comp (orbitSectionFixedCoefficients h K π H).subtype)
      (b.sum_repr v)
    simpa only [map_sum, map_smul, smul_eq_mul, LinearMap.comp_apply,
      Submodule.subtype_apply, Module.Basis.coord_apply] using he
  change ‖a z g v.val‖ ≤ _
  rw [← hexpand]
  calc ‖∑ i, b.coord i v * a z g (b i).val‖
      ≤ ∑ i, ‖b.coord i v * a z g (b i).val‖ := norm_sum_le _ _
    _ ≤ ∑ i, (t.sup fun ℓ => inputSeminorms H ([], ℓ)) q * ((C i : ℝ) * Ξ g) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul]
      exact mul_le_mul (hcoordinate i) (hC i z g) (norm_nonneg _)
        (apply_nonneg _ _)
    _ = (c : ℝ) * (t.sup fun ℓ => inputSeminorms H ([], ℓ)) q * Ξ g := by
      change _ = (∑ i, (C i : ℝ)) * (t.sup fun ℓ => inputSeminorms H ([], ℓ)) q * Ξ g
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

variable [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))

/-- A unitary-twist coefficient, as a linear functional on the fixed compact picture. -/
def unitaryOrbitCompactCoefficient (z : J → Circle) (g : G) :
    CompactPicture →ₗ[ℂ] ℂ :=
  (LocallyConstant.evalₗ ℂ g).comp
    ((unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr
      (unitaryOrbitParameterRepresentative ν π e z)).comp
        (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
          (unitaryTorusParameter ν e z) π.obj).symm.toLinearMap)

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

set_option hygiene false in
local notation "orbitCoefficient" => unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ
  ν π hν hr C hC μ hsq e
set_option hygiene false in
local notation "compactCoefficient" => unitaryOrbitCompactCoefficient h hU hP K hK hPK ν π hν hr e hG hδ

omit [DecidableEq J] in
/-- The compact functional recovers the actual orbit coefficient on the compact restriction. -/
theorem unitaryOrbitCompactCoefficient_restriction
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (z : J → Circle) (g : G) :
    compactCoefficient z g (compactRestriction q z) =
      orbitCoefficient q (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq)
        (e.symm z)) g := by
  rw [unitaryOrbitCoefficientMap_parameter]
  let E := productInducedCompactEquiv ν h K hP hK hν hr hU hPK
    (unitaryTorusParameter ν e z) π.obj
  let A := unitaryOrbitParameterRepresentative ν π e z
  change unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A
      (E.symm (E (q.val A))) g =
    unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A (q.val A) g
  exact congrArg (fun v => unitaryOrbitRepresentativeCoefficientMap
    h hU hP K hK hPK hG hδ ν π hr A v g) (E.symm_apply_apply (q.val A))

variable {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (hcofinal : CompactOpenCofinal M)
  (hδU : IsUnimodularModulus U hU)
  (hL : LeviData (K : Subgroup G) P₀ P M δ₀
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
  (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
  (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
  (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
    ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)

include hcofinal hδU hL hMK hδ₀ hcoeff in
/-- The VI.2.2 bound, uniform over an entire fixed input level, with explicit
section dependence through finitely many zero-order derivative seminorms. -/
theorem exists_levelOrbitCoefficient_bound (H : OpenSubgroup G) (hHK : H ≤ K) :
    ∃ t : Finset (Module.Dual ℂ CompactPicture), ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H)
        (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) (g : G),
        ‖orbitCoefficient (includeLevel H q) ω g‖ ≤
          (c : ℝ) * (t.sup fun ℓ => inputSeminorms H ([], ℓ)) q * xi hP₀K δ₀ g := by
  let := finiteDimensional_orbitSectionFixedCoefficients h K π hK hcofinal H hHK
  let b := Module.finBasis ℂ (orbitSectionFixedCoefficients h K π H)
  have hPK' : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k := fun g => by
    obtain ⟨p, k, hg⟩ := hPK g
    exact ⟨p, p.property, k, k.property, hg⟩
  have ha (v : orbitSectionFixedCoefficients h K π H) : ∃ c : ℝ≥0,
      ∀ (z : J → Circle) (g : G), ‖compactCoefficient z g v.val‖ ≤ (c : ℝ) * xi hP₀K δ₀ g := by
    obtain ⟨c, hc, hb⟩ := norm_twist_coefficientMap_le_xi h hU π.obj K hK ν hν hP hr hPK'
      hG hδ π.property.2 hδU hL hP₀K hMK hδ₀ hcoeff v.val
    refine ⟨⟨c, hc.le⟩, fun z g => ?_⟩
    exact hb (unitaryTorusParameter ν e z) (norm_unitaryTorusParameter_apply ν e z) g
  obtain ⟨t, c, hb⟩ := exists_levelFamily_bound_of_basis h hU hP K hK hPK ν π hν hr e
    H hHK b (xi hP₀K δ₀) compactCoefficient ha
  refine ⟨t, c, fun q ω g => ?_⟩
  obtain ⟨χ, rfl⟩ :=
    (isOpenQuotientMap_discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq)).surjective ω
  have hbz := hb q (e χ) g
  rw [unitaryOrbitCompactCoefficient_restriction h hU hP K hK hPK ν π hν hr e hG hδ
    C hC μ hsq (includeLevel H q) (e χ) g] at hbz
  simpa only [MulEquiv.symm_apply_apply] using hbz

/-- One continuous input seminorm controlling all coefficients at a fixed level. -/
def orbitSectionLevelCoefficientControl (H : OpenSubgroup G) (hHK : H ≤ K) :
    Seminorm ℂ (SectionLevel H) :=
  let ex := exists_levelOrbitCoefficient_bound h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
    hcofinal hδU hL hP₀K hMK hδ₀ hcoeff H hHK
  let t := Classical.choose ex
  let c := Classical.choose (Classical.choose_spec ex)
  c • t.sup (fun ℓ => inputSeminorms H ([], ℓ))

/-- The chosen finite-seminorm control is uniform over every actual orbit class and group point. -/
theorem norm_levelOrbitCoefficient_le_control (H : OpenSubgroup G) (hHK : H ≤ K)
    (q : SectionLevel H)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) (g : G) :
    ‖orbitCoefficient (includeLevel H q) ω g‖ ≤
      orbitSectionLevelCoefficientControl h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
        hcofinal hδU hL hP₀K hMK hδ₀ hcoeff H hHK q * xi hP₀K δ₀ g := by
  exact Classical.choose_spec (Classical.choose_spec
    (exists_levelOrbitCoefficient_bound h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
      hcofinal hδU hL hP₀K hMK hδ₀ hcoeff H hHK)) q ω g

/-- Continuity uses only a finite supremum of the original zero-order input seminorms. -/
theorem continuous_orbitSectionLevelCoefficientControl (H : OpenSubgroup G) (hHK : H ≤ K) :
    Continuous (orbitSectionLevelCoefficientControl h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
      hcofinal hδU hL hP₀K hMK hδ₀ hcoeff H hHK) := by
  unfold orbitSectionLevelCoefficientControl
  exact (Seminorm.continuous_finsetSup fun ℓ _ =>
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H).continuous_seminorm ([], ℓ)).const_smul _

set_option hygiene false in
local notation "coefficientControl" => orbitSectionLevelCoefficientControl
  h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq hcofinal hδU hL hP₀K hMK hδ₀ hcoeff

variable [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (ρX : Measure (unitaryUnramifiedCharacters ν))

set_option hygiene false in
local notation "orbitMeasure" => discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρX

/-- Fixed-level packet control retaining the actual total orbit mass. -/
def orbitSectionLevelWavePacketControl (B : ℝ≥0) (H : OpenSubgroup G) (hHK : H ≤ K) :
    Seminorm ℂ (SectionLevel H) :=
  (B * ⟨(orbitMeasure).real Set.univ, measureReal_nonneg⟩ : ℝ≥0) • coefficientControl H hHK

/-- A bounded weight and finite character measure give a uniform fixed-level packet bound. -/
theorem norm_levelOrbitWavePacket_le_control [IsFiniteMeasure ρX]
    (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)
    (B : ℝ≥0) (hw : ∀ ω, ‖w ω‖ ≤ B) (H : OpenSubgroup G) (hHK : H ≤ K)
    (q : SectionLevel H) (g : G) :
    ‖inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρX w
      (includeLevel H q) g‖ ≤
        orbitSectionLevelWavePacketControl h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
          hcofinal hδU hL hP₀K hMK hδ₀ hcoeff ρX B H hHK q * xi hP₀K δ₀ g := by
  have := isFiniteMeasure_discreteSeriesOrbitMeasure ν π C hC μ hsq ρX
  have hb : ∀ ω, ‖w ω * orbitCoefficient (includeLevel H q) ω g‖ ≤
      (B : ℝ) * (coefficientControl H hHK q * xi hP₀K δ₀ g) := fun ω => by
    rw [norm_mul]
    exact mul_le_mul (hw ω)
      (norm_levelOrbitCoefficient_le_control h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
        hcofinal hδU hL hP₀K hMK hδ₀ hcoeff H hHK q ω g)
      (norm_nonneg _) B.coe_nonneg
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)).trans_eq ?_
  change (B : ℝ) * (coefficientControl H hHK q * xi hP₀K δ₀ g) * (orbitMeasure).real Set.univ =
    ((B : ℝ) * (orbitMeasure).real Set.univ * coefficientControl H hHK q) * xi hP₀K δ₀ g
  ring

/-- The packet control is continuous in the existing input-level topology. -/
theorem continuous_orbitSectionLevelWavePacketControl (B : ℝ≥0) (H : OpenSubgroup G) (hHK : H ≤ K) :
    Continuous (orbitSectionLevelWavePacketControl h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
      hcofinal hδU hL hP₀K hMK hδ₀ hcoeff ρX B H hHK) :=
  (continuous_orbitSectionLevelCoefficientControl h hU hP K hK hPK ν π hν hr e hG hδ C hC μ hsq
    hcofinal hδU hL hP₀K hMK hδ₀ hcoeff H hHK).const_smul _

end Langlands.HarishChandraSchwartz
