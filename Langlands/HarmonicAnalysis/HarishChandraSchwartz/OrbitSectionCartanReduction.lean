import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelTranslation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionSchwartzSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermCompactCover
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket

/-! # From fixed-level chamber estimates to the full Schwartz estimates -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Langlands.Plancherel Langlands.Aubert.General
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ

/-- For a compact double cover of `G`, only finitely many translations of the middle
set are needed modulo left and right multiplication by a fixed open subgroup. -/
private theorem exists_finite_translates_of_compact_cover
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B S : Set G} (hA : IsCompact A) (hB : IsCompact B)
    (hcover : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, ∃ m ∈ S, g = a * m * b)
    (H : OpenSubgroup G) :
    ∃ E : Finset (G × G), ∀ g : G, ∃ x ∈ E, ∃ m ∈ S, ∃ k₁ k₂ : H,
      g = (k₁ : G) * (x.2⁻¹ * m * x.1) * (k₂ : G) := by
  classical
  obtain ⟨L, hL⟩ := hA.elim_finite_subcover (fun l : G => {y : G | y * l⁻¹ ∈ H})
    (fun l => H.isOpen.preimage (continuous_id.mul continuous_const))
    (fun y _ => Set.mem_iUnion.mpr ⟨y, by simp⟩)
  obtain ⟨R, hR⟩ := hB.elim_finite_subcover (fun k : G => {y : G | k⁻¹ * y ∈ H})
    (fun k => H.isOpen.preimage (continuous_const.mul continuous_id))
    (fun y _ => Set.mem_iUnion.mpr ⟨y, by simp⟩)
  refine ⟨(L.product R).image (fun y => (y.2, y.1⁻¹)), fun g => ?_⟩
  obtain ⟨a, ha, b, hb, m, hm, h⟩ := hcover g
  obtain ⟨l, hl, hla⟩ := Set.mem_iUnion₂.mp (hL ha)
  obtain ⟨k, hk, hkb⟩ := Set.mem_iUnion₂.mp (hR hb)
  refine ⟨(k, l⁻¹), Finset.mem_image.mpr ⟨(l, k), Finset.mem_product.mpr ⟨hl, hk⟩, rfl⟩, m, hm,
    ⟨a * l⁻¹, hla⟩, ⟨k⁻¹ * b, hkb⟩, ?_⟩
  rw [h]
  change a * m * b = (a * l⁻¹) * ((l⁻¹)⁻¹ * m * k) * (k⁻¹ * b)
  group

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
  (he : HasLaurentUnitaryCoordinates ν e)

set_option hygiene false in
local notation "Sections" => OrbitSectionSpace ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "includeLevel" => OrbitSectionSpace.ofLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "inputSeminorms" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "DerivativeIndex" => List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)
set_option hygiene false in
local notation "translateLevel" => orbitSectionLevelTranslate h hU hP K hK hPK ν π hν hr e he

/-- The pointwise derivative estimates on a given middle set in a compact double cover. -/
def OrbitSectionChamberDerivativeEstimates (Ξ σ : G → ℝ) (S : Set G)
    (T : Sections →ₗ[ℂ] (G → ℂ)) : Prop :=
  ∀ (H : {H : OpenSubgroup G // H ≤ K}) (r : ℝ),
    ∃ t : Finset DerivativeIndex, ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H.1) (m : G), m ∈ S →
        ‖T (includeLevel H.1 q) m‖ ≤
          (c : ℝ) * (t.sup (inputSeminorms H.1)) q * (Ξ m * (1 + σ m) ^ (-r))

/-- The chamber bounds yield the original all-group Schwartz seminorm estimates.
The fixed section levels, product covariance and local invariance of the weight
are used to control the finitely many translates in the compact cover. -/
theorem orbitSectionSchwartzEstimates_of_compact_chamber
    (Ξ σ : G → ℝ) (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hσinv : ∀ g, σ g⁻¹ = σ g) (hσmul : ∀ g g', σ (g * g') ≤ σ g + σ g')
    (hXiTranslation : UniformTranslationBound Ξ)
    (D : OpenSubgroup G)
    (hΞD : ∀ k ∈ D, ∀ l ∈ D, ∀ g, Ξ (k * g * l) = Ξ g)
    (hσD : ∀ k ∈ D, ∀ l ∈ D, ∀ g, σ (k * g * l) = σ g)
    {A B S : Set G} (hA : IsCompact A) (hB : IsCompact B)
    (hcover : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, ∃ m ∈ S, g = a * m * b)
    (T : Sections →ₗ[ℂ] (G → ℂ))
    (hfix : ∀ (H : OpenSubgroup G) (q : SectionLevel H), IsBiInvariant H (T (includeLevel H q)))
    (htranslate : ∀ (H : OpenSubgroup G) (x : G × G) (q : SectionLevel H) (g : G),
      T (includeLevel (orbitSectionTranslatedLevel K H x) (translateLevel H x q)) g =
        T (includeLevel H q) (x.2⁻¹ * g * x.1))
    (hchamber : OrbitSectionChamberDerivativeEstimates h hU hP K hK hPK ν π hν hr e Ξ σ S T) :
    OrbitSectionSchwartzEstimates ν π e h hU K hP hK hν hr hPK Ξ σ T := by
  classical
  intro H r
  let W (g : G) := Ξ g * (1 + σ g) ^ (-r)
  have hW (g : G) : 0 ≤ W g :=
    mul_nonneg (hΞ g).le (Real.rpow_nonneg (by linarith [hσ g]) _)
  have hWT : UniformTranslationBound W :=
    hXiTranslation.mul_one_add_rpow (fun g => (hΞ g).le) hσ hσinv hσmul (-r)
  have hHc : IsCompact (H.1 : Set G) := hK.of_isClosed_subset H.1.isClosed H.2
  have hWL : ∀ k ∈ D, ∀ g, W (k * g) = W g := by
    intro k hk g
    have hX := hΞD k hk 1 D.one_mem g
    have hY := hσD k hk 1 D.one_mem g
    simp only [mul_one] at hX hY
    simp only [W, hX, hY]
  have hWR : ∀ k ∈ D, ∀ g, W (g * k) = W g := by
    intro k hk g
    have hX := hΞD 1 D.one_mem k hk g
    have hY := hσD 1 D.one_mem k hk g
    simp only [one_mul] at hX hY
    simp only [W, hX, hY]
  obtain ⟨d, hd⟩ := hWT.exists_uniform_mul hW D.isOpen hWL hWR hHc
  obtain ⟨E, hE⟩ := exists_finite_translates_of_compact_cover hA hB hcover H.1
  let Hx (x : G × G) := orbitSectionTranslatedLevel K H.1 x
  have hHx (x : G × G) : Hx x ≤ K := inf_le_left.trans inf_le_left
  choose s c hc using fun x : G × G => hchamber ⟨Hx x, hHx x⟩ r
  choose t b hb using fun x : G × G => exists_orbitSectionLevelTranslate_finsetSup_bound
    h hU hP K hK hPK ν π hν hr e he H.1 x (s x)
  choose C hC using fun x : G × G => hWT.exists_le_mul x.2⁻¹ x.1
  let F := E.biUnion t
  let A0 (x : G × G) : ℝ≥0 := c x * b x * Real.toNNReal |C x| * d
  let B0 := ∑ x ∈ E, A0 x
  refine ⟨F, B0, fun q => iSup_le fun g => ?_⟩
  obtain ⟨x, hx, m, hm, a, k, hg⟩ := hE g
  have hv : T (includeLevel H.1 q) g = T (includeLevel (Hx x) (translateLevel H.1 x q)) m := by
    rw [hg, hfix H.1 q a a.property k k.property, htranslate]
  have hmid : W (x.2⁻¹ * m * x.1) ≤ (d : ℝ) * W g := by
    have e : (a : G)⁻¹ * g * (k : G)⁻¹ = x.2⁻¹ * m * x.1 := by rw [hg]; group
    rw [← e]
    exact hd _ (H.1.inv_mem a.property) _ (H.1.inv_mem k.property) g
  have hweight : W m ≤ |C x| * ((d : ℝ) * W g) := by
    refine (hC x m).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (hW _)).trans ?_)
    exact mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
  have hsup : (t x).sup (inputSeminorms H.1) q ≤ F.sup (inputSeminorms H.1) q := by
    have hs : (t x).sup (inputSeminorms H.1) ≤ F.sup (inputSeminorms H.1) :=
      Finset.sup_mono fun j hj => Finset.mem_biUnion.mpr ⟨x, hx, hj⟩
    exact hs q
  have hder := (hb x q).trans (mul_le_mul_of_nonneg_left hsup (b x).coe_nonneg)
  let Q := F.sup (inputSeminorms H.1) q
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hB0 : (A0 x : ℝ) ≤ (B0 : ℝ) := by
    exact_mod_cast (Finset.single_le_sum (f := A0) (fun _ _ => bot_le) hx)
  have hbound : ‖T (includeLevel H.1 q) g‖ ≤ ((B0 : ℝ) * Q) * W g := calc
    ‖T (includeLevel H.1 q) g‖ = ‖T (includeLevel (Hx x) (translateLevel H.1 x q)) m‖ := congrArg norm hv
    _ ≤ (c x : ℝ) * ((s x).sup (inputSeminorms (Hx x))) (translateLevel H.1 x q) * W m :=
      hc x (translateLevel H.1 x q) m hm
    _ ≤ (c x : ℝ) * ((b x : ℝ) * Q) * (|C x| * ((d : ℝ) * W g)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hder (c x).coe_nonneg) hweight (hW _)
        (mul_nonneg (c x).coe_nonneg (mul_nonneg (b x).coe_nonneg hQ))
    _ = (A0 x : ℝ) * Q * W g := by
      simp only [A0, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg _)]
      ring
    _ ≤ (B0 : ℝ) * Q * W g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB0 hQ) (hW g)
  have hbound' := ENNReal.ofReal_le_ofReal hbound
  rw [ofReal_norm, ENNReal.ofReal_mul (mul_nonneg B0.coe_nonneg hQ)] at hbound'
  calc ‖T (includeLevel H.1 q) g‖ₑ * weight Ξ σ r g
      ≤ (ENNReal.ofReal ((B0 : ℝ) * Q) * ENNReal.ofReal (W g)) * weight Ξ σ r g :=
        mul_le_mul_left hbound' _
    _ = ENNReal.ofReal ((B0 : ℝ) * (F.sup (inputSeminorms H.1)) q) := by
      rw [mul_assoc, mul_comm (ENNReal.ofReal (W g)), weight_mul_ofReal hΞ hσ r g, mul_one]

section Packet

variable [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (rho : Measure (unitaryUnramifiedCharacters ν))
  (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)

set_option hygiene false in
local notation "packet" => inducedOrbitWavePacket h hU hP K hK hPK hG hδ
  ν π hν hr e C hC μ hsq rho w
set_option hygiene false in
local notation "toSections" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK

omit [DecidableEq J] in
/-- The translated section produces the translated original integral, with the
same weight and orbit measure. -/
theorem inducedOrbitWavePacket_translateLevel (H : OpenSubgroup G) (x : G × G)
    (q : SectionLevel H) (g : G) :
    packet (toSections (orbitSectionTranslatedLevel K H x) (translateLevel H x q)) g =
      packet (toSections H q) (x.2⁻¹ * g * x.1) := by
  rw [orbitSectionLevelTranslate_toSections]
  unfold inducedOrbitWavePacket
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => congrArg (w ω * ·)
    (unitaryOrbitCoefficientMap_action h hU hP K hK hPK hG hδ
      ν π hν hr C hC μ hsq e he x (toSections H q) ω g))

end Packet

end Langlands.HarishChandraSchwartz
