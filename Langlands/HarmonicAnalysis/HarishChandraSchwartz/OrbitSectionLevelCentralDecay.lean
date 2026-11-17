import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacketDecay
import Langlands.HarmonicAnalysis.TorusMonomialSeminormControl

/-! # Central Fourier decay uniform over a fixed section level -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ uL uB

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] [DecidableEq J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters ν))
  (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)


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

omit [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- Finitely many coefficient coordinates and derivative directions are controlled
by a finite subset of the existing input-level seminorms. -/
theorem exists_levelCoordinate_derivative_control (H : OpenSubgroup G)
    {B : Type uB} [Fintype B] (ℓ : B → Module.Dual ℂ CompactPicture) (n : ℕ) :
    ∃ t : Finset (List J × Module.Dual ℂ CompactPicture),
      ∀ (q : SectionLevel H) (i : B),
        smoothTorusDerivativeControl n
          (orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK (ℓ i) (includeLevel H q)) ≤
            (t.sup (inputSeminorms H)) q := by
  classical
  let t : Finset (List J × Module.Dual ℂ CompactPicture) :=
    Finset.univ.biUnion fun i => (torusDerivativeLists (J := J) n).image fun l => (l, ℓ i)
  refine ⟨t, fun q i => ?_⟩
  unfold smoothTorusDerivativeControl
  refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun l hl => ?_
  change inputSeminorms H (l, ℓ i) q ≤ (t.sup (inputSeminorms H)) q
  exact (Finset.le_sup (f := inputSeminorms H) (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩)) q

/-- The central Fourier estimate controlled by finitely many input derivatives,
uniformly for all sections at the prescribed subgroup. -/
theorem exists_levelOrbitWavePacket_central_decay [IsFiniteMeasure ρ] [ρ.IsMulLeftInvariant]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hws : IsSmoothFiniteTorusFunction fun y =>
      w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm y)))
    {L : Type uL} [Fintype L] (nG : G →* Multiplicative (L → ℤ)) (a : J → L → ℤ)
    (hnK : ∀ k ∈ K, nG k = 1) (hnU : ∀ u ∈ U, nG u = 1)
    (hnM : ∀ (m : M) (z : L → Circle),
      ((e.symm (finiteTorusMonomial a z)).val m : ℂ) = torusCharacter (Multiplicative.toAdd (nG m)) z)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (hcofinal : CompactOpenCofinal M) (H : OpenSubgroup G) (hHK : H ≤ K) (r : ℝ) :
    ∃ t : Finset (List J × Module.Dual ℂ CompactPicture), ∃ c : ℝ≥0,
      ∀ (q : SectionLevel H) (g : G),
      ‖inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w (includeLevel H q) g‖ ≤
        (c : ℝ) * (t.sup (inputSeminorms H)) q * xi hP₀K δ₀ g * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := by
  classical
  have hPK' : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k := fun g => by
    obtain ⟨p, k, hg⟩ := hPK g
    exact ⟨p, p.2, k, k.2, hg⟩
  -- the orbit map and the weight in torus coordinates
  set W : (J → Circle) → ℂ := fun y => w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm y)) with hW
  have hWc : Continuous W := hws.continuous
  -- continuity of `w` on the orbit
  have hwc : Continuous w := by
    apply (isOpenQuotientMap_discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq)).isQuotientMap.continuous_iff.mpr
    have ht := hWc.comp he
    simpa only [Function.comp_def, W, e.symm_apply_apply] using ht
  have hwm : AEStronglyMeasurable w (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ) :=
    hwc.aestronglyMeasurable
  -- Choose the coefficient basis and its ambient coordinates before the section.
  let := finiteDimensional_orbitSectionFixedCoefficients h K π hK hcofinal H hHK
  let b := Module.finBasis ℂ (orbitSectionFixedCoefficients h K π H)
  choose ℓ hℓ using fun i => (b.coord i).exists_extend
  let v := fun i => (b i).val
  let f := fun (q : SectionLevel H) i =>
    orbitSectionCoefficient ν π e h hU K hP hK hν hr hPK (ℓ i) (includeLevel H q)
  have hF (q : SectionLevel H) (y : J → Circle) :
      compactRestriction (includeLevel H q) y = ∑ i, (f q i).val y • v i := by
    let u := orbitSectionLevelFixedRestriction h K π ν e hU hP hK hν hr hPK H hHK q y
    change u.val = _
    calc u.val = (∑ i, b.coord i u • b i).val := congrArg Subtype.val (b.sum_repr u).symm
      _ = ∑ i, (f q i).val y • v i := by
        simp only [Submodule.coe_sum, Submodule.coe_smul]
        apply Finset.sum_congr rfl
        intro i _
        have he := LinearMap.congr_fun (hℓ i) u
        exact congrArg (fun c : ℂ => c • v i) he.symm
  -- the coefficients of the fixed compact vectors
  set T : unramifiedCharacters ν → ProductInducedCompactPicture h K π.obj →ₗ[ℂ]
      LocallyConstant G ℂ := fun χ =>
    twistedSectionCoefficient h hU π.obj K hK ν hν hP hr hPK' hG hδ π.property.2 χ with hT
  -- The finite basis expansion is the original orbit coefficient.
  have hcoef (q : SectionLevel H) (y : J → Circle) (g : G) :
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e (includeLevel H q)
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm y)) g =
        ∑ i, (f q i).val y * T (unitaryTorusParameter ν e y) (v i) g := by
    rw [← unitaryOrbitCompactCoefficient_restriction h hU hP K hK hPK ν π hν hr e hG hδ
      C hC μ hsq (includeLevel H q) y g]
    change T (unitaryTorusParameter ν e y) (compactRestriction (includeLevel H q) y) g = _
    rw [hF q y, map_sum, ← LocallyConstant.evalAddMonoidHom_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LocallyConstant.evalAddMonoidHom_apply, map_smul, LocallyConstant.coe_smul,
      Pi.smul_apply, smul_eq_mul]
  -- the measure on the torus
  set μT : Measure (J → Circle) := ρ.map e with hμT
  have hem : Measurable e := he.measurable
  have : IsFiniteMeasure μT := Measure.isFiniteMeasure_map ρ e
  have : μT.IsMulLeftInvariant :=
    isMulLeftInvariant_map e.toMulHom hem e.surjective
  -- the auxiliary probability measure on the torus `Im X(G)`
  let νG : Measure (L → Circle) := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure νG := ⟨by
    have := Measure.haarMeasure_self (G := L → Circle) (K₀ := ⊤)
    simpa using this⟩
  -- continuity, unitarity and equivariance of the coefficients
  have hutpc : ∀ m : M, Continuous fun y => ((unitaryTorusParameter ν e y).val m : ℂ) := by
    intro m
    obtain ⟨k, hk⟩ := hLaurent m
    have heq : (fun y => ((unitaryTorusParameter ν e y).val m : ℂ)) = torusCharacter k :=
      funext hk
    rw [heq]
    exact continuous_torusCharacter k
  have hTc : ∀ i g, Continuous fun y => T (unitaryTorusParameter ν e y) (v i) g := fun i g =>
    continuous_twistedSectionCoefficient h hU π.obj K hK ν hν hP hr hPK' hG hδ π.property.2
      (unitaryTorusParameter ν e) hutpc (fun y m => norm_unitaryTorusParameter_apply ν e y m)
      (v i) g
  have hTn : ∀ i g (z : L → Circle) (y : J → Circle),
      T (unitaryTorusParameter ν e (finiteTorusMonomial a z * y)) (v i) g =
        torusCharacter (Multiplicative.toAdd (nG g)) z *
          T (unitaryTorusParameter ν e y) (v i) g := by
    intro i g z y
    rw [unitaryTorusParameter_mul]
    exact twistedSectionCoefficient_mul h hU π.obj K hK ν hν hP hr hPK' hG hδ π.property.2
      _ _ (latticeTorusCharacter nG z)
      (fun k hk => by rw [latticeTorusCharacter_apply, hnK k hk, toAdd_one, torusCharacter_zero])
      (fun u hu => by rw [latticeTorusCharacter_apply, hnU u hu, toAdd_one, torusCharacter_zero])
      (fun m => hnM m z) (v i) g
  -- the bounds of Lemma VI.2.2 for the fixed vectors
  choose B hB0 hB using fun i => norm_twist_coefficientMap_le_xi h hU π.obj K hK ν hν hP hr hPK'
    hG hδ π.property.2 hδU hL hP₀K hMK hδ₀ hcoeff (v i)
  -- One scalar derivative estimate works for every section and every coordinate.
  let k : ℕ := ⌈r⌉₊
  have hrk : r ≤ k := Nat.le_ceil r
  let Ws : smoothFiniteTorusFunctions J := ⟨W, hws⟩
  obtain ⟨A, hA, hA0, hAd⟩ := exists_weighted_monomial_derivative_control Ws a k
  obtain ⟨t, ht⟩ := exists_levelCoordinate_derivative_control h hU hP K hK hPK ν π hν hr e
    H ℓ k
  set S := Nat.card (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))
  let c₀ : ℝ := (S : ℝ)⁻¹ * ∑ i, 2 ^ k * (1 + Fintype.card L) * A * μT.real Set.univ * B i
  have hc₀ : 0 ≤ c₀ := by
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun i _ => ?_)
    have := (hB0 i).le
    positivity
  refine ⟨t, ⟨c₀, hc₀⟩, fun q g => ?_⟩
  let N : ℝ := (t.sup (inputSeminorms H)) q
  have hφs : ∀ i, IsSmoothFiniteTorusFunction fun y => W y * (f q i).val y := fun i =>
    hws.mul (f q i).property
  have hM0 (i) (y : J → Circle) (z : L → Circle) :
      ‖W (finiteTorusMonomial a z * y) * (f q i).val (finiteTorusMonomial a z * y)‖ ≤ A * N :=
    (hA0 (f q i) y z).trans (mul_le_mul_of_nonneg_left (ht q i) hA)
  have hMd (i) (y : J → Circle) (j : L) (z : L → Circle) :
      ‖(torusPartialDeriv j)^[k] (fun z => W (finiteTorusMonomial a z * y) *
        (f q i).val (finiteTorusMonomial a z * y)) z‖ ≤ A * N :=
    (hAd (f q i) y j z).trans (mul_le_mul_of_nonneg_left (ht q i) hA)
  -- the wave packet as a finite sum of torus integrals
  have hint : ∀ i, Integrable (fun y => (W y * (f q i).val y) * T (unitaryTorusParameter ν e y) (v i) g) μT :=
    fun i => ((hφs i).continuous.mul (hTc i g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpar := inducedOrbitWavePacket_eq_parameterIntegral h hU hP K hK hPK hG hδ ν π hν hr e C
    hC μ hsq ρ w hLaurent he hwm (includeLevel H q) g
  have hmap : ∫ χ, w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) *
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e (includeLevel H q)
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) g ∂ρ =
      ∑ i, ∫ y, (W y * (f q i).val y) * T (unitaryTorusParameter ν e y) (v i) g ∂μT := by
    rw [← integral_finsetSum _ fun i _ => hint i]
    have hcont : Continuous fun y => ∑ i, (W y * (f q i).val y) *
        T (unitaryTorusParameter ν e y) (v i) g :=
      continuous_finsetSum _ fun i _ => ((hφs i).continuous.mul (hTc i g))
    rw [hμT, integral_map hem.aemeasurable hcont.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun χ => ?_)
    simp only [W, e.symm_apply_apply]
    have hc := hcoef q (e χ) g
    rw [e.symm_apply_apply] at hc
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hpar, hmap, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  -- the estimate of each torus integral
  have hbound : ∀ i, ‖∫ y, (W y * (f q i).val y) * T (unitaryTorusParameter ν e y) (v i) g ∂μT‖ ≤
      2 ^ k * (1 + Fintype.card L) * (A * N) * μT.real Set.univ * (B i * xi hP₀K δ₀ g) *
        (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := fun i =>
    norm_integral_mul_le_rpow μT νG (continuous_finiteTorusMonomial a)
      (hφs i).continuous
      (fun χ => isSmoothFiniteTorusFunction_comp_monomial_mul (hφs i) a χ)
      (hTc i g) (hTn i g) hrk (hM0 i) (hMd i)
      (fun χ => hB i (unitaryTorusParameter ν e χ) (norm_unitaryTorusParameter_apply ν e χ) g)
  calc (S : ℝ)⁻¹ * ‖∑ i, ∫ y, (W y * (f q i).val y) * T (unitaryTorusParameter ν e y) (v i) g ∂μT‖
      ≤ (S : ℝ)⁻¹ * ∑ i, 2 ^ k * (1 + Fintype.card L) * (A * N) * μT.real Set.univ *
          (B i * xi hP₀K δ₀ g) * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbound i))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = c₀ * N * xi hP₀K δ₀ g * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := by
        simp only [c₀, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring


variable [IsFiniteMeasure ρ] [ρ.IsMulLeftInvariant]
  (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hws : IsSmoothFiniteTorusFunction fun y =>
      w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm y)))
    {L : Type uL} [Fintype L] (nG : G →* Multiplicative (L → ℤ)) (a : J → L → ℤ)
    (hnK : ∀ k ∈ K, nG k = 1) (hnU : ∀ u ∈ U, nG u = 1)
    (hnM : ∀ (m : M) (z : L → Circle),
      ((e.symm (finiteTorusMonomial a z)).val m : ℂ) = torusCharacter (Multiplicative.toAdd (nG m)) z)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (hcofinal : CompactOpenCofinal M)

/-- A continuous input seminorm controlling the central Fourier decay of the
literal wave packet at a fixed subgroup and a prescribed real order. -/
def orbitSectionLevelCentralControl (H : OpenSubgroup G) (hHK : H ≤ K) (r : ℝ) :
    Seminorm ℂ (SectionLevel H) :=
  let ex := exists_levelOrbitWavePacket_central_decay h hU hP K hK hPK hG hδ ν π hν hr e
    C hC μ hsq ρ w hLaurent he hws nG a hnK hnU hnM hδU hL hP₀K hMK hδ₀ hcoeff
    hcofinal H hHK r
  let t := Classical.choose ex
  let c := Classical.choose (Classical.choose_spec ex)
  c • t.sup (inputSeminorms H)

/-- The chosen control is uniform over all sections at the original input subgroup. -/
theorem norm_levelOrbitWavePacket_le_centralControl (H : OpenSubgroup G) (hHK : H ≤ K)
    (r : ℝ) (q : SectionLevel H) (g : G) :
    ‖inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w
      (includeLevel H q) g‖ ≤
        orbitSectionLevelCentralControl h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w
          hLaurent he hws nG a hnK hnU hnM hδU hL hP₀K hMK hδ₀ hcoeff hcofinal H hHK r q *
            xi hP₀K δ₀ g * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := by
  exact Classical.choose_spec (Classical.choose_spec
    (exists_levelOrbitWavePacket_central_decay h hU hP K hK hPK hG hδ ν π hν hr e
      C hC μ hsq ρ w hLaurent he hws nG a hnK hnU hnM hδU hL hP₀K hMK hδ₀ hcoeff
      hcofinal H hHK r)) q g

/-- Continuity follows from a finite supremum of the original input derivative
seminorms and multiplication by a nonnegative constant. -/
theorem continuous_orbitSectionLevelCentralControl (H : OpenSubgroup G) (hHK : H ≤ K)
    (r : ℝ) :
    Continuous (orbitSectionLevelCentralControl h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w
      hLaurent he hws nG a hnK hnU hnM hδU hL hP₀K hMK hδ₀ hcoeff hcofinal H hHK r) := by
  unfold orbitSectionLevelCentralControl
  exact (Seminorm.continuous_finsetSup fun i _ =>
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H).continuous_seminorm i).const_smul _

end Langlands.HarishChandraSchwartz
