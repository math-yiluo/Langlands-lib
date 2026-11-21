import Langlands.Global.EisensteinConstantTerm.Reduction
import Langlands.Global.AdelicRepresentationHeightPropernessProof

/-! # Absolute bounds for the unfolded Bruhat terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth
  Langlands.Automorphic.GroupSchemeFunctions EisensteinConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G P Q V : GroupScheme (Spec (CommRingCat.of F))}
  (p : P ⟶ G) (q : Q ⟶ G) (iV : V ⟶ Q)

local notation "j" => (iV ≫ q)
local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
local notation "Vᵣ" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)
local notation "Points" => AdelicGroupPoints F G

/-- The integrand on the full rational stabilizer quotient before the
geometric-lemma identification of intertwining terms. -/
def eisensteinStabilizerIntegrand (w : Points) (Φ : Points → ℂ) (g : Points)
    (v : LeftCosetSpace (stabilizerRationalSubgroup F p j w)) : ℂ :=
  Φ (w⁻¹ * (v.out : Vₐ).val * g)

/-- The integrand is independent of the rational stabilizer representative. -/
theorem eisensteinStabilizerIntegrand_mk (w : Points) (Φ : Points → ℂ)
    (hΦ : IsLeftInvariantUnder F G (rationalImage F p) Φ) (g : Points) (v : Vₐ) :
    eisensteinStabilizerIntegrand p q iV w Φ g (LeftCosetSpace.mk _ v) = Φ (w⁻¹ * v.val * g) := by
  let Λ := stabilizerRationalSubgroup F p j w
  let o := (LeftCosetSpace.mk Λ v).out
  have ho : o * v⁻¹ ∈ Λ :=
    (LeftCosetSpace.mk_eq_mk_iff Λ v o).mp (Quotient.out_eq (LeftCosetSpace.mk Λ v)).symm
  have hR : w⁻¹ * (o * v⁻¹ : Vₐ).val * w ∈ rationalImage F p :=
    ((mem_stabilizerRationalSubgroup_iff F p j w (o * v⁻¹)).mp ho).2
  change Φ (w⁻¹ * o.val * g) = Φ (w⁻¹ * v.val * g)
  rw [← hΦ _ hR (w⁻¹ * v.val * g)]
  congr 1
  change w⁻¹ * o.val * g =
    (w⁻¹ * (o.val * v.val⁻¹) * w) * (w⁻¹ * v.val * g)
  group

/-- Joint continuity after descent to the actual stabilizer quotient. -/
theorem continuous_eisensteinStabilizerIntegrand [IsAffine G.X.left] (w : Points) (Φ : Points → ℂ)
    (hΦ : IsLeftInvariantUnder F G (rationalImage F p) Φ) (hΦc : Continuous Φ) :
    Continuous fun x : LeftCosetSpace (stabilizerRationalSubgroup F p j w) × Points =>
      eisensteinStabilizerIntegrand p q iV w Φ x.2 x.1 := by
  have hm := (LeftCosetSpace.isOpenQuotientMap_mk (stabilizerRationalSubgroup F p j w)).prodMap
    (show IsOpenQuotientMap (id : Points → Points) from IsOpenQuotientMap.id)
  apply hm.continuous_comp_iff.mp
  change Continuous fun x : Vₐ × Points =>
    eisensteinStabilizerIntegrand p q iV w Φ x.2 (LeftCosetSpace.mk _ x.1)
  simp_rw [eisensteinStabilizerIntegrand_mk p q iV w Φ hΦ]
  exact hΦc.comp ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).mul
    continuous_snd)

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine V.X.left]
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {I : Type u} [Fintype I]

local notation "RationalPoint" => (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

/-- The absolute norm integrals for one Bruhat piece are bounded by the
original absolute series on the target radical at the original parameter. -/
theorem eisensteinBruhatAbsoluteBoundAt (w : I → RationalPoint) (pieces : I → Subgroup Points)
    (hw : IsDoubleCosetRepresentatives F q p w)
    (hpieces : ∀ i, pieces i = (rationalImage F q ⊓ (rationalImage F p).map
      (MulAut.conj (innerAdelicPoint F G (w i))).toMonoidHom) ⊔ rationalImage F j)
    (hN : (SubgroupFunctor.range iV).IsNormal)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]
    (Φ : Points → ℂ) (hΦ : IsLeftInvariantUnder F G (rationalImage F p) Φ)
    (hΦc : Continuous Φ) (g : Points) (B : ℝ≥0∞) (hB : B ≠ ∞)
    (hBound : ∀ v : Vₐ, ∑' c : ParabolicRationalCosets F p,
      ‖Φ ((c.out : rationalSubgroup F G).val * (v.val * g))‖ₑ ≤ B) (i : I) :
    ∑' c : OuterCosets (rationalImage F q) (pieces i), ∫⁻ v, ‖eisensteinStabilizerIntegrand p q iV (innerAdelicPoint F G (w i)) Φ
      ((c.out : rationalImage F q).val * g) v‖ₑ ∂stabilizerMeasure F p j (innerAdelicPoint F G (w i)) ≤ B := by
  classical
  let absΦ : Points → ℂ := fun x => (‖Φ x‖ : ℂ)
  have habs : Continuous absΦ := Complex.continuous_ofReal.comp hΦc.norm
  have habsInv : IsLeftInvariantUnder F G (rationalImage F p) absΦ := by
    intro z hz x
    simp only [absΦ, hΦ z hz x]
  have habsNorm (x : Points) : ‖absΦ x‖ₑ = ‖Φ x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg ENNReal.ofReal (Complex.norm_of_nonneg (norm_nonneg (Φ x)))
  let lower (k : I) (y : Points) :=
    ∫⁻ v, ‖eisensteinStabilizerIntegrand p q iV (innerAdelicPoint F G (w k)) Φ y v‖ₑ ∂stabilizerMeasure F p j (innerAdelicPoint F G (w k))
  let R (k : I) (y : Points) : ℂ := (lower k y).toReal
  have hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (Vₐ : Set Points) := hClosed
  let : LocallyCompactSpace Vₐ := hClosed.locallyCompactSpace
  let : PolishSpace Vₐ := hClosed.polishSpace
  have hCore := constantTerm_series_eq hw pieces hpieces hN habs habsInv g B hB
    (fun v => by simpa only [habsNorm] using hBound v) R (fun k y => lower k y < ∞)
    (fun k y hfin => by
      have hv (v : LeftCosetSpace (stabilizerRationalSubgroup F p j (innerAdelicPoint F G (w k)))) :
          ‖absΦ ((innerAdelicPoint F G (w k))⁻¹ * (v.out : Vₐ).val * y)‖ₑ =
            ‖eisensteinStabilizerIntegrand p q iV (innerAdelicPoint F G (w k)) Φ y v‖ₑ := habsNorm _
      have hfin' : lower k y < ∞ := by
        simpa only [hv] using hfin
      refine ⟨hfin', ?_⟩
      let normIntegrand := fun v => ‖eisensteinStabilizerIntegrand p q iV (innerAdelicPoint F G (w k)) Φ y v‖
      have hcont : Continuous normIntegrand :=
        ((continuous_eisensteinStabilizerIntegrand p q iV (innerAdelicPoint F G (w k)) Φ hΦ hΦc).comp
          (continuous_id.prodMk continuous_const)).norm
      let : BorelSpace (LeftCosetSpace (stabilizerRationalSubgroup F p j (innerAdelicPoint F G (w k)))) :=
        LeftCosetSpace.discreteQuotientBorelSpace _ (isDiscrete_stabilizerRationalSubgroup F p j _)
      have hNorm : Integrable normIntegrand (stabilizerMeasure F p j (innerAdelicPoint F G (w k))) := by
        refine ⟨hcont.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        simpa only [normIntegrand, Real.enorm_of_nonneg (norm_nonneg _), ofReal_norm] using hfin'
      change (((lower k y).toReal : ℝ) : ℂ) =
        ∫ v, (normIntegrand v : ℂ) ∂stabilizerMeasure F p j (innerAdelicPoint F G (w k))
      rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae _
        hNorm.aestronglyMeasurable]
      · simp only [lower, normIntegrand, ofReal_norm]
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _)
  let Li (k : I) : ℝ := ∑' c : OuterCosets (rationalImage F q) (pieces k), (lower k ((c.out : rationalImage F q).val * g)).toReal
  have hLi (k : I) : 0 ≤ Li k := tsum_nonneg fun _ => ENNReal.toReal_nonneg
  have hRel (k : I) : (∑' c : OuterCosets (rationalImage F q) (pieces k), lower k ((c.out : rationalImage F q).val * g)) =
      ENNReal.ofReal (Li k) := by
    simp only [Li, ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg)
      ((hCore.2.1 k).mapL Complex.reCLM)]
    exact tsum_congr fun c => (ENNReal.ofReal_toReal (hCore.1 k c).ne).symm
  let Eabs (y : Points) :=
    ∑' c : ParabolicRationalCosets F p, absΦ ((c.out : rationalSubgroup F G).val * y)
  have hReal : (subgroupConstantTerm F j Eabs g).re = ∑ k : I, Li k := by
    change Complex.reCLM (subgroupConstantTerm F j Eabs g) = _
    rw [hCore.2.2, map_sum]
    exact Finset.sum_congr rfl fun k _ => Complex.reCLM.map_tsum (hCore.2.1 k)
  let : IsProbabilityMeasure
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (SubgroupFunctor.range j)) :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G (SubgroupFunctor.range j)
  have hCTbound : ‖subgroupConstantTerm F j Eabs g‖ₑ ≤ B := by
    unfold subgroupConstantTerm
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc
      _ ≤ ∫⁻ _, B ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
            (SubgroupFunctor.range j) := by
        apply lintegral_mono
        intro x
        refine enorm_tsum_le_tsum_enorm.trans ?_
        simpa only [habsNorm] using hBound (x.out : Vₐ)
      _ = B := by rw [lintegral_const, measure_univ, mul_one]
  change (∑' c : OuterCosets (rationalImage F q) (pieces i), lower i ((c.out : rationalImage F q).val * g)) ≤ B
  rw [hRel i]
  refine (ENNReal.ofReal_le_ofReal (Finset.single_le_sum (fun k _ => hLi k) (Finset.mem_univ i))).trans ?_
  rw [← hReal]
  refine (ENNReal.ofReal_le_ofReal (Complex.re_le_norm (subgroupConstantTerm F j Eabs g))).trans ?_
  simpa only [ofReal_norm] using hCTbound

/-- For every rational Bruhat piece, the sum of absolute stabilizer
integrals has a fixed polynomial weight in the external argument. -/
def EisensteinBruhatAbsoluteBoundStatement (w : I → RationalPoint) (pieces : I → Subgroup Points)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) : Prop :=
  0 < N → IsDoubleCosetRepresentatives F q p w →
  (∀ i, pieces i = (rationalImage F q ⊓ (rationalImage F p).map
    (MulAut.conj (innerAdelicPoint F G (w i))).toMonoidHom) ⊔ rationalImage F j) →
  (SubgroupFunctor.range iV).IsNormal →
  CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)) →
  ∀ Φ : Points → ℂ, Continuous Φ → IsLeftInvariantUnder F G (rationalImage F p) Φ →
    ∀ (b : ParabolicRationalCosets F p → ℝ) (d : ℝ), Summable b → (∀ c, 0 ≤ b c) → 0 ≤ d →
    (∀ (g : Points) (c : ParabolicRationalCosets F p),
      ‖Φ ((c.out : rationalSubgroup F G).val * g)‖ ≤ b c * adelicHeight F G rho g ^ d) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Points) (i : I),
      ∑' c : OuterCosets (rationalImage F q) (pieces i), ∫⁻ v, ‖eisensteinStabilizerIntegrand p q iV (innerAdelicPoint F G (w i)) Φ
        ((c.out : rationalImage F q).val * g) v‖ₑ ∂stabilizerMeasure F p j (innerAdelicPoint F G (w i)) ≤
          ENNReal.ofReal (C * adelicHeight F G rho g ^ d)

set_option maxHeartbeats 1600000 in
theorem eisensteinBruhatAbsoluteBound (w : I → RationalPoint) (pieces : I → Subgroup Points)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) :
    EisensteinBruhatAbsoluteBoundStatement p q iV w pieces rho := by
  intro hN hw hpieces hV hCompact Φ hΦc hΦ b d hb hb₀ hd hbound
  let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace Vₐ := hClosed.locallyCompactSpace
  obtain ⟨D, hD, hcover⟩ := exists_isCompact_mul_mem Vᵣ
  let H := adelicHeight F G rho
  obtain ⟨B, hB⟩ := ((hD.image continuous_subtype_val).image (continuous_adelicHeight F G rho hN)).bddAbove
  let L := max B 1
  have hL : 0 ≤ L := zero_le_one.trans (le_max_right _ _)
  let C := (∑' c, b c) * L ^ d
  refine ⟨C, mul_nonneg (tsum_nonneg hb₀) (Real.rpow_nonneg hL _), fun g i => ?_⟩
  refine eisensteinBruhatAbsoluteBoundAt p q iV w pieces hw hpieces hV Φ hΦ hΦc g _ ENNReal.ofReal_ne_top
    (fun v => ?_) i
  obtain ⟨a, ha, v₀, hv₀, rfl⟩ := hcover v
  have hAG : a.val ∈ rationalSubgroup F G :=
    rationalImage_le_rationalSubgroup j ((mem_rationalSubgroup_range_iff j a).mp ha)
  let Pm := (rationalSubgroup F P).map (map F P G p).toMonoidHom
  have hInvNorm : ∀ z ∈ Pm, ∀ x, ‖Φ (z * x)‖ₑ = ‖Φ x‖ₑ := by
    change ∀ z ∈ (rationalSubgroup F P).map (map F P G p).toMonoidHom, ∀ x, ‖Φ (z * x)‖ₑ = ‖Φ x‖ₑ
    rw [← rationalImage_eq_map]
    intro z hz x
    rw [hΦ z hz x]
  rw [show ((a * v₀ : Vₐ).val * g) = a.val * (v₀.val * g) from mul_assoc _ _ _,
    show (∑' c : ParabolicRationalCosets F p, ‖Φ (c.out.val * (a.val * (v₀.val * g)))‖ₑ) =
      ∑' c : ParabolicRationalCosets F p, ‖Φ (c.out.val * (v₀.val * g))‖ₑ from
        tsum_out_mul_left (P := Pm) (g := fun z => ‖Φ z‖ₑ) hInvNorm hAG _]
  have hg : 0 ≤ H g := zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  have hLow : 0 ≤ H (v₀.val * g) := zero_le_one.trans (one_le_adelicHeight F G rho hN _)
  have hvH : H v₀.val ≤ L := (hB ⟨v₀.val, ⟨v₀, hv₀, rfl⟩, rfl⟩).trans (le_max_left _ _)
  have hVg : H (v₀.val * g) ≤ L * H g :=
    (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_right hvH hg)
  have hScale (c : ParabolicRationalCosets F p) :
      ‖Φ ((c.out : rationalSubgroup F G).val * (v₀.val * g))‖ₑ ≤
        ENNReal.ofReal (b c * (L ^ d * H g ^ d)) := by
    rw [← ofReal_norm, ← Real.mul_rpow hL hg]
    exact ENNReal.ofReal_le_ofReal ((hbound _ _).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hLow hVg hd) (hb₀ c)))
  exact (ENNReal.tsum_le_tsum hScale).trans_eq (by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun c => mul_nonneg (hb₀ c) (mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg hg _)))
      (hb.mul_right _), tsum_mul_right]
    unfold C H
    rw [mul_assoc])

end Langlands.Global
