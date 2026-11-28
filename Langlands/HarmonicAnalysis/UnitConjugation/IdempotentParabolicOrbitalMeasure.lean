import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicHaarFactorization
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicOrbitChange
import Langlands.Analysis.Local.QuotientFactorizationProduct

/-! # The measure on a regular orbit in Levi, upper-corner and compact coordinates -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Set QuotientIntegration _root_.Topology
open scoped ENNReal

universe u v

section OrbitPoint

variable {A : Type v} [Ring A]

/-- The value of the orbit map on a left coset of the stabilizer of `x`. -/
def orbitalPoint (x : A) : LeftQuotient (conjugationCentralizer x) → A :=
  descend (conjugationCentralizer x) (fun g : Aˣ => ((g⁻¹ : Aˣ) : A) * x * (g : A))
    (by
      intro h g
      have hh := (mem_conjugationCentralizer_iff x h.val).mp h.property
      have hx : ((h.val⁻¹ : Aˣ) : A) * x * (h.val : A) = x := by
        rw [mul_assoc, ← hh, ← mul_assoc, Units.inv_mul, one_mul]
      simp only [mul_inv_rev, Units.val_mul]
      calc
        _ = ((g⁻¹ : Aˣ) : A) * (((h.val⁻¹ : Aˣ) : A) * x * (h.val : A)) * (g : A) := by
          simp only [mul_assoc]
        _ = _ := by rw [hx])

@[simp]
theorem orbitalPoint_mk (x : A) (g : Aˣ) :
    orbitalPoint x (leftQuotientMap (conjugationCentralizer x) g) =
      ((g⁻¹ : Aˣ) : A) * x * (g : A) := rfl

theorem orbitalIntegrand_eq_comp_orbitalPoint (x : A) (f : A → ℂ) :
    orbitalIntegrand x f = f ∘ orbitalPoint x := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => rfl

theorem continuous_orbitalPoint [TopologicalSpace A] [IsTopologicalRing A] (x : A) :
    Continuous (orbitalPoint x) := by
  apply (leftQuotient_isOpenQuotientMap (conjugationCentralizer x)).isQuotientMap.continuous_iff.mpr
  change Continuous fun g : Aˣ => ((g⁻¹ : Aˣ) : A) * x * (g : A)
  exact (Units.continuous_coe_inv.mul_const x).mul Units.continuous_val

private theorem isClosed_centralizer [TopologicalSpace A] [T2Space A] [IsTopologicalRing A]
    (x : A) : IsClosed ((conjugationCentralizer x : Subgroup Aˣ) : Set Aˣ) := by
  have h : ((conjugationCentralizer x : Subgroup Aˣ) : Set Aˣ) =
      {g : Aˣ | (g : A) * x = x * (g : A)} :=
    Set.ext (mem_conjugationCentralizer_iff x)
  rw [h]
  exact isClosed_eq (Units.continuous_val.mul_const x) (continuous_const.mul Units.continuous_val)

end OrbitPoint

namespace IdempotentCentralizer

variable (F : Type u) [NontriviallyNormedField F] {A : Type v} [NormedRing A] [NormedAlgebra F A]
  [FiniteDimensional F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

/-- The point obtained by adding an upper-corner coordinate to a point of the Levi orbit
and conjugating by the inverse compact coordinate. -/
def parabolicOrbitalPoint (X : Levi) (K : OpenSubgroup Aˣ)
    (p : LeftQuotient (conjugationCentralizer X) × (Upper × K)) : A :=
  ((p.2.2.val⁻¹ : Aˣ) : A) * (((orbitalPoint X p.1 : Levi) : A) + (p.2.1 : A)) *
    (p.2.2.val : A)

omit [FiniteDimensional F A] in
theorem continuous_parabolicOrbitalPoint (X : Levi) (K : OpenSubgroup Aˣ) :
    Continuous (parabolicOrbitalPoint F X K) := by
  have hK : Continuous fun p : LeftQuotient (conjugationCentralizer X) × (Upper × K) =>
      p.2.2.val := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hY : Continuous fun p : LeftQuotient (conjugationCentralizer X) × (Upper × K) =>
      ((orbitalPoint X p.1 : Levi) : A) :=
    continuous_subtype_val.comp ((continuous_orbitalPoint X).comp continuous_fst)
  have hZ : Continuous fun p : LeftQuotient (conjugationCentralizer X) × (Upper × K) =>
      (p.2.1 : A) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  exact ((Units.continuous_coe_inv.comp hK).mul (hY.add hZ)).mul (Units.continuous_val.comp hK)

private def parabolicCompactFactor (he : IsIdempotentElem e) (K : OpenSubgroup Aˣ)
    (p : Upper × K) : Aˣ := upperCornerUnit F he p.1 * p.2.val

omit [FiniteDimensional F A] in
private theorem continuous_parabolicCompactFactor (he : IsIdempotentElem e) (K : OpenSubgroup Aˣ) :
    Continuous (parabolicCompactFactor F he K) := by
  have hu : Continuous (upperCornerUnit F he) :=
    Units.continuous_iff.mpr
      ⟨continuous_const.add continuous_subtype_val, continuous_const.sub continuous_subtype_val⟩
  exact (hu.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

private theorem orbitalPoint_mul_coordinates (he : IsIdempotentElem e)
    (X : Levi) (hX : (X : A) ∈ regularSet F A) (K : OpenSubgroup Aˣ)
    (q : LeftQuotient (conjugationCentralizer X)) (p : Upper × K) :
    orbitalPoint (X : A)
      (quotientFactorizationProductMap (conjugationCentralizer (X : A))
        (conjugationCentralizer X) (Units.map (Levi).val.toMonoidHom)
        (conjugationCentralizerEquiv he X hX).toMulEquiv
        (conjugationCentralizerEquiv_apply_val he X hX) (parabolicCompactFactor F he K) (q, p)) =
      parabolicOrbitalPoint F X K (q, upperCornerAdjoint F (orbitalPoint X q) p.1, p.2) := by
  induction q using Quotient.inductionOn with
  | h m =>
    change orbitalPoint (X : A) (quotientFactorizationProductMap _ _ _ _ _ _
      (leftQuotientMap (conjugationCentralizer X) m, p)) =
      parabolicOrbitalPoint F X K (leftQuotientMap (conjugationCentralizer X) m,
        upperCornerAdjoint F (orbitalPoint X (leftQuotientMap (conjugationCentralizer X) m)) p.1,
          p.2)
    rw [quotientFactorizationProductMap_mk, orbitalPoint_mk]
    let y : Levi := (m⁻¹ : Leviˣ).val * X * m.val
    let n := upperCornerUnit F he p.1
    let k := p.2.val
    let mG := Units.map (Levi).val.toMonoidHom m
    have hm : (mG : A) = (m.val : A) := rfl
    have hmInv : ((mG⁻¹ : Aˣ) : A) = ((m⁻¹ : Leviˣ).val : A) := rfl
    change (((mG * (n * k))⁻¹ : Aˣ) : A) * (X : A) * (mG * (n * k) : Aˣ).val =
      ((k⁻¹ : Aˣ) : A) * ((y : A) + (upperCornerAdjoint F y p.1 : A)) * (k : A)
    calc
      _ = ((k⁻¹ : Aˣ) : A) * (((n⁻¹ : Aˣ) : A) * (y : A) * (n : A)) * (k : A) := by
        simp only [mul_inv_rev, Units.val_mul, hm, hmInv, y, Subalgebra.coe_mul, mul_assoc]
      _ = _ := by
        dsimp only [n]
        rw [upperCornerUnit_inv_conj, upperCornerAdjoint_apply]

variable [ProperSpace F] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [MeasurableSpace (Subalgebra.centralizer F ({e} : Set A))ˣ]
  [BorelSpace (Subalgebra.centralizer F ({e} : Set A))ˣ]

/-- The measure obtained on the ambient orbit from a compatible quotient measure is the
pushforward of the Levi quotient, upper-corner and compact measures, up to the Haar
factorization scalar. -/
theorem map_parabolicOrbitalPoint (he : IsIdempotentElem e)
    (X : Levi) (hX : (X : A) ∈ regularSet F A) (K : OpenSubgroup Aˣ)
    (hK : IsCompact (K : Set Aˣ))
    (hfac : ∀ g : Aˣ, ∃ p ∈ parabolicUnits F he, ∃ k ∈ K, g = p * k)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
    [BorelSpace (LeftQuotient (conjugationCentralizer X))]
    [MeasurableSpace (LeftQuotient (conjugationCentralizer (X : A)))]
    [BorelSpace (LeftQuotient (conjugationCentralizer (X : A)))]
    (μG : Measure Aˣ) [μG.IsHaarMeasure] (μM : Measure Leviˣ) [μM.IsHaarMeasure]
    (μH : Measure (conjugationCentralizer (X : A))) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (μJ : Measure (conjugationCentralizer X)) [μJ.IsHaarMeasure] [μJ.IsMulRightInvariant]
    (hE : MeasurePreserving (conjugationCentralizerEquiv he X hX) μJ μH)
    (νG : Measure (LeftQuotient (conjugationCentralizer (X : A))))
    (νM : Measure (LeftQuotient (conjugationCentralizer X)))
    (hG : IsCompatible _ μG μH νG) (hM : IsCompatible _ μM μJ νM) :
    ∃ (ν : Measure Upper) (c : ℝ≥0∞), ν.IsAddHaarMeasure ∧ c ≠ 0 ∧ c ≠ ∞ ∧
      (νM.prod (ν.prod (μG.comap (K.toSubgroup.subtype : K →* Aˣ)))).map
        (parabolicOrbitalPoint F X K) = c • νG.map (orbitalPoint (X : A)) := by
  have : ProperSpace A := FiniteDimensional.proper F A
  have : ProperSpace Levi := FiniteDimensional.proper F Levi
  have : ProperSpace Upper := FiniteDimensional.proper F Upper
  have : SecondCountableTopology Aᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology Aˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  have : SecondCountableTopology (leviUnits F (e := e)) :=
    (IsEmbedding.subtypeVal (p := fun g : Aˣ => g ∈ leviUnits F (e := e))).secondCountableTopology
  have : SecondCountableTopology Leviˣ :=
    (leviUnitsEquiv F (e := e)).toHomeomorph.isEmbedding.secondCountableTopology
  have : SecondCountableTopology K :=
    (IsEmbedding.subtypeVal (p := fun g : Aˣ => g ∈ K)).secondCountableTopology
  let μ₀ : Measure Upper := Measure.addHaar
  have : μ₀.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure Upper).IsAddHaarMeasure
  let μK := μG.comap (K.toSubgroup.subtype : K →* Aˣ)
  have : μK.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) (f := K.toSubgroup.subtype) μG
      K.isOpen.isOpenEmbedding_subtypeVal
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨c, hc₀, hcTop, hc⟩ := idempotentParabolicHaarFactorization F he K hK hfac μG μM μ₀
  obtain ⟨ν, hν, hChange⟩ := idempotentParabolicOrbitChange F e he X hX μ₀
  have : ν.IsAddHaarMeasure := hν
  let H := conjugationCentralizer (X : A)
  let J := conjugationCentralizer X
  let j : Leviˣ →* Aˣ := Units.map (Levi).val.toMonoidHom
  let E := (conjugationCentralizerEquiv he X hX).toMulEquiv
  have heq (g : J) : (E g : Aˣ) = j (g : Leviˣ) := conjugationCentralizerEquiv_apply_val he X hX g
  have hH : IsClosed (H : Set Aˣ) := isClosed_centralizer (X : A)
  have hJ : IsClosed (J : Set Leviˣ) := isClosed_centralizer X
  let k := parabolicCompactFactor F he K
  have hk : Continuous k := continuous_parabolicCompactFactor F he K
  have hj : Continuous j := continuous_subtype_val.units_map _
  obtain ⟨r, _, hr, _⟩ := exists_continuous_isNormalizingFunction H hH μH
  let Ψ := quotientFactorizationProductMap H J j E heq k
  have hΨ : Measurable Ψ := (continuous_quotientFactorizationProductMap H J j E heq k hj hk).measurable
  have hProd : (νM.prod (μ₀.prod μK)).map Ψ = c • νG :=
    hG.map_quotientFactorizationProduct H J j E heq k hH hJ hj hk hE hM
      (μ₀.prod μK) c hc _ hr
  let Φ := parabolicOrbitalPoint F X K
  let Ω := orbitalPoint (X : A)
  have hΩ : Measurable Ω := (continuous_orbitalPoint (X : A)).measurable
  have hΦ : Measurable Φ := (continuous_parabolicOrbitalPoint F X K).measurable
  refine ⟨ν, c, hν, hc₀, hcTop, ?_⟩
  have hΩΨ := congrArg (Measure.map Ω) hProd
  rw [Measure.map_map hΩ hΨ, Measure.map_smul _ hΩ.aemeasurable] at hΩΨ
  rw [← hΩΨ]
  have hIntegral (f : A → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ a, f a ∂(νM.prod (ν.prod μK)).map Φ) =
      ∫⁻ a, f a ∂(νM.prod (μ₀.prod μK)).map (Ω ∘ Ψ) := by
    have hFiber (q : LeftQuotient J) :
        (∫⁻ p, f (Φ (q, p)) ∂ν.prod μK) = ∫⁻ p, f (Ω (Ψ (q, p))) ∂μ₀.prod μK := by
      let L := upperCornerAdjoint F (orbitalPoint X q)
      have hL : Measurable L := (LinearMap.toContinuousLinearMap L).continuous.measurable
      have hmap : μ₀.map L = ν := by
        induction q using Quotient.inductionOn with
        | h m => exact (hChange m).1
      have hF : Measurable fun p : Upper × K => f (Φ (q, p)) :=
        (hf.comp hΦ).comp (measurable_const.prodMk measurable_id)
      calc
        _ = ∫⁻ p, f (Φ (q, p)) ∂(μ₀.map L).prod (μK.map id) := by
          rw [hmap, Measure.map_id]
        _ = ∫⁻ p, f (Φ (q, L p.1, p.2)) ∂μ₀.prod μK := by
          rw [Measure.map_prod_map _ _ hL measurable_id]
          exact lintegral_map hF (hL.prodMap measurable_id)
        _ = _ := lintegral_congr fun p =>
          congrArg f (orbitalPoint_mul_coordinates F he X hX K q p).symm
    calc
      _ = ∫⁻ p, f (Φ p) ∂νM.prod (ν.prod μK) := lintegral_map hf hΦ
      _ = ∫⁻ q, ∫⁻ p, f (Φ (q, p)) ∂ν.prod μK ∂νM :=
        lintegral_prod _ (hf.comp hΦ).aemeasurable
      _ = ∫⁻ q, ∫⁻ p, f (Ω (Ψ (q, p))) ∂μ₀.prod μK ∂νM := lintegral_congr hFiber
      _ = ∫⁻ p, f ((Ω ∘ Ψ) p) ∂νM.prod (μ₀.prod μK) :=
        (lintegral_prod _ (hf.comp (hΩ.comp hΨ)).aemeasurable).symm
      _ = _ := (lintegral_map hf (hΩ.comp hΨ)).symm
  ext s hs
  simpa only [lintegral_indicator_one hs] using hIntegral (s.indicator 1)
    (measurable_one.indicator hs)

end IdempotentCentralizer

end Langlands.HarmonicAnalysis.UnitConjugation
