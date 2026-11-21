import Langlands.BaseChange.RankOneCyclicOrbitalGeometry
import Langlands.Analysis.Local.QuotientAutomorphismProof

/-! # Relative quotient Haar masses for rank-one concordance -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped CompactlySupported

namespace Langlands.BaseChange

open GeneralLinear QuotientIntegration RankinSelberg TraceFormula
open ClassFieldTheory.Local

attribute [local instance] rankOneCommGroup
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

section CompactQuotient

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p} (S : E.TopologicalData)
  {F : Type u} [Field F] [Algebra F E.Carrier]

private theorem rankOne_scalar_fixed {a : E.Carrierˣ} (σ : E.Carrier ≃ₐ[F] E.Carrier)
    (ha : σ (a : E.Carrier) = a) : entrywiseAut σ 1 (scalar a) = scalar a := by
  ext i j
  fin_cases i
  fin_cases j
  rw [entrywiseAut_apply_apply]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, ha]

/-- Every coset modulo the twisted centralizer has a representative whose
normalized order lies in a fixed finite interval. Thus the left quotient is compact. -/
theorem isCompact_rankOneTwistedCentralizerQuotient (σ : E.Carrier ≃ₐ[F] E.Carrier)
    (δ : GeneralLinear 1 E.Carrier) :
    letI := S.topology
    IsCompact (Set.univ : Set (LeftQuotient (sigmaCentralizer σ 1 δ))) := by
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let H := sigmaCentralizer σ 1 δ
  let e := S.ord (p : E.Carrier)
  have he : 0 < e := S.ord_prime_pos
  have hp : (p : E.Carrier) ≠ 0 := by
    intro h
    change 0 < S.ord (p : E.Carrier) at he
    rw [h, S.ord_zero] at he
    exact (lt_irrefl 0) he
  let a : E.Carrierˣ := Units.mk0 (p : E.Carrier) hp
  have ha : scalar (n := 1) a ∈ H := (mem_sigmaCentralizer_rankOne σ δ _).mpr
    (rankOne_scalar_fixed σ (by change σ (p : E.Carrier) = _; exact map_natCast σ p))
  have hπ : S.uniformizer ≠ 0 := by
    intro hz
    have hh := S.ord_uniformizer
    rw [hz, S.ord_zero] at hh
    omega
  let π : E.Carrierˣ := Units.mk0 S.uniformizer hπ
  let K := ⋃ i : Fin e.toNat, (fun x : E.Carrierˣ => π ^ ((i : ℕ) : ℤ) * x) ''
    (S.unitSubgroup : Set E.Carrierˣ)
  have hU : IsCompact (S.unitSubgroup : Set E.Carrierˣ) := by
    rw [← S.unitFiltration_zero]
    exact S.isCompact_unitFiltration 0
  have hK : IsCompact K := isCompact_iUnion (fun _ => hU.image (continuous_const.mul continuous_id))
  have hcover : (leftQuotientMap H ∘ (rankOneDeterminantEquiv E.Carrier).symm) '' K =
      (Set.univ : Set (LeftQuotient H)) := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      let n := S.ord (determinant g : E.Carrier)
      let i := n % e
      have hi0 : 0 ≤ i := Int.emod_nonneg n he.ne'
      have hi1 : i < e := Int.emod_lt_of_pos n he
      let I : Fin e.toNat := ⟨i.toNat, (Int.toNat_lt_toNat he).mpr hi1⟩
      let y := a ^ (-(n / e)) * determinant g
      have hy : S.ord (y : E.Carrier) = i := by
        change S.ord (((a ^ (-(n / e)) : E.Carrierˣ) : E.Carrier) * (determinant g : E.Carrier)) = i
        rw [S.ord_mul (a ^ (-(n / e))).ne_zero (determinant g).ne_zero,
          Units.val_zpow_eq_zpow_val, S.ord_zpow]
        change -(n / e) * e + n = n % e
        have hi := Int.emod_add_mul_ediv n e
        linear_combination -hi
      have hyk : y ∈ K := by
        apply Set.mem_iUnion.mpr
        refine ⟨I, (π ^ ((I : ℕ) : ℤ))⁻¹ * y, ?_, by simp⟩
        apply (mem_unitSubgroup_iff_ord_eq_zero E S _).mpr
        rw [Units.val_mul, S.ord_mul ((π ^ ((I : ℕ) : ℤ))⁻¹).ne_zero y.ne_zero,
          ← zpow_neg, Units.val_zpow_eq_zpow_val, S.ord_zpow]
        change (-((I : ℕ) : ℤ)) * S.ord S.uniformizer + S.ord (y : E.Carrier) = 0
        rw [S.ord_uniformizer, hy]
        change (-(i.toNat : ℤ)) * 1 + i = 0
        rw [Int.toNat_of_nonneg hi0]
        ring
      refine ⟨y, hyk, ?_⟩
      let h : H := ⟨(scalar a) ^ (-(n / e)), H.zpow_mem ha _⟩
      change leftQuotientMap H (scalar y) = Quotient.mk _ g
      have hsy : scalar y = h.val * g := by
        change scalar (a ^ (-(n / e)) * determinant g) = (scalar a) ^ (-(n / e)) * g
        rw [map_mul, map_zpow, scalar_determinant_rankOne]
      rw [hsy, leftQuotientMap_subgroup_mul]
      rfl
  rw [← hcover]
  exact hK.image ((leftQuotient_isOpenQuotientMap H).continuous.comp
    (rankOneDeterminantEquiv E.Carrier).symm.continuous)

end CompactQuotient

section RelativeMass

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {E : Type v} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  [Algebra F E] [IsModuleTopology F E]
  [MeasurableSpace (GeneralLinear 1 F)] [BorelSpace (GeneralLinear 1 F)]
  [MeasurableSpace (GeneralLinear 1 E)] [BorelSpace (GeneralLinear 1 E)]
  [LocallyCompactSpace (GeneralLinear 1 E)]
  {σ : E ≃ₐ[F] E} {l : ℕ}

/-- For rank-one cyclic norm pairs the two compatible quotient masses have a
positive ratio that depends only on the ambient Haar measures. -/
theorem IsCyclicAlgebra.exists_rankOne_quotientMassRatio (hcyc : IsCyclicAlgebra σ l)
    (hK : IsCompact (Set.univ : Set (LeftQuotient (sigmaCentralizer σ 1 1))))
    (μF : Measure (GeneralLinear 1 F)) [μF.IsHaarMeasure] [μF.Regular]
    (μE : Measure (GeneralLinear 1 E)) [μE.IsHaarMeasure] :
    ∃ r : ℝ, 0 < r ∧
      ∀ (δ : GeneralLinear 1 E) (γ : GeneralLinear 1 F)
        (μδ : Measure (sigmaCentralizer σ 1 δ)) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
        (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
        (νδ : Measure (LeftQuotient (sigmaCentralizer σ 1 δ)))
        (νγ : Measure (LeftQuotient (glCentralizer γ))),
        IsCompatible (sigmaCentralizer σ 1 δ) μE μδ νδ →
        IsCompatible (glCentralizer γ) μF μγ νγ →
        IsAssociatedMeasure σ l δ γ μδ μγ →
        (νδ Set.univ).toReal = r * (νγ Set.univ).toReal := by
  let H := sigmaCentralizer σ 1 (1 : GeneralLinear 1 E)
  let j := baseChange F E 1
  let j₀ := hcyc.rankOneCentralizerEquiv (1 : GeneralLinear 1 E)
  let μ₀ : Measure H := Measure.map j₀ μF
  let : μ₀.IsHaarMeasure := j₀.isHaarMeasure_map μF
  let : μ₀.Regular := Measure.Regular.map j₀.toHomeomorph
  let : μ₀.IsMulRightInvariant := ⟨fun g => by
    simpa only [mul_comm] using (map_mul_left_eq_self (μ := μ₀) g)⟩
  have hH : IsClosed (H : Set (GeneralLinear 1 E)) := isClosed_sigmaCentralizer_rankOne σ 1
  obtain ⟨b, hb, hb₀⟩ := realQuotientCompactNormalization H hH μ₀ Set.univ hK
  have hb₁ (x : GeneralLinear 1 E) : (∫ g, b (j g * x) ∂μF) = 1 := by
    calc
      _ = ∫ c : H, b (c.val * x) ∂μ₀ :=
        (integral_map_equiv j₀.toHomeomorph.toMeasurableEquiv (fun c => b (c.val * x))).symm
      _ = 1 := hb₀ x (Set.mem_univ _)
  have hj : IsClosedEmbedding j :=
    hH.isClosedEmbedding_subtypeVal.comp j₀.toHomeomorph.isClosedEmbedding
  let r := ∫ x, b x ∂μE
  have hr : 0 < r := by
    obtain ⟨x, hx⟩ : ∃ x, b x ≠ 0 := by
      by_contra! h
      simpa only [h, integral_zero, zero_ne_one] using hb₁ 1
    exact b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero b.hasCompactSupport hb hx
  refine ⟨r, hr, ?_⟩
  intro δ γ μδ _ _ μγ _ _ νδ νγ hδ hγ hassoc
  let jγ := glCentralizerRankOneEquiv γ
  let μ' : Measure (GeneralLinear 1 F) := μγ.map jγ
  let : μ'.IsHaarMeasure := jγ.isHaarMeasure_map μγ
  have hmap : μδ.map Subtype.val = μ'.map j := by
    obtain ⟨x, -, hx⟩ := hassoc
    simp only [rankOne_inv_mul_mul_eq] at hx
    have hjγ : Measurable (jγ : glCentralizer γ → GeneralLinear 1 F) := jγ.continuous.measurable
    change _ = Measure.map j (Measure.map jγ μγ)
    rw [Measure.map_map hj.continuous.measurable hjγ]
    exact hx
  let scale := (haarScalarFactor μ' μF : ℝ)
  have hscale (f : GeneralLinear 1 F → ℝ) (hf : Continuous f) (hcomp : HasCompactSupport f) :
      (∫ g, f g ∂μ') = scale * (∫ g, f g ∂μF) := by
    rw [integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μF hf hcomp,
      integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have habove (x : GeneralLinear 1 E) : (∫ c : sigmaCentralizer σ 1 δ, b (c.val * x) ∂μδ) = scale := by
    let f : GeneralLinear 1 E → ℝ := fun y => b (y * x)
    have hf : Continuous f :=
      b.continuous.comp (continuous_id.mul continuous_const : Continuous (· * x))
    have hsupport : HasCompactSupport f :=
      b.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight x)
    calc
      _ = ∫ y, f y ∂(μδ.map Subtype.val) :=
        (integral_map continuous_subtype_val.measurable.aemeasurable
          hf.aestronglyMeasurable).symm
      _ = ∫ g, f (j g) ∂μ' := by
        rw [hmap, integral_map hj.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
      _ = scale := by
        rw [hscale (fun g => f (j g)) (hf.comp hj.continuous) (hsupport.comp_isClosedEmbedding hj)]
        change scale * (∫ g, b (j g * x) ∂μF) = scale
        rw [hb₁ x, mul_one]
  let f₀ : GeneralLinear 1 F → ℝ := fun g => b (j g)
  have hf₀ : Continuous f₀ := b.continuous.comp hj.continuous
  have hf₀c : HasCompactSupport f₀ := b.hasCompactSupport.comp_isClosedEmbedding hj
  have hf₀i : (∫ g, f₀ g ∂μF) = 1 := by simpa [f₀] using hb₁ 1
  have hbelow (x : GeneralLinear 1 F) :
      (∫ c : glCentralizer γ, f₀ (c.val * x) ∂μγ) = scale := by
    calc
      _ = ∫ g, f₀ (g * x) ∂μ' := by
        exact (integral_map_equiv jγ.toHomeomorph.toMeasurableEquiv (fun g => f₀ (g * x))).symm
      _ = ∫ g, f₀ g ∂μ' := by
        simpa only [mul_comm] using (integral_mul_left_eq_self (μ := μ') f₀ x)
      _ = scale := by rw [hscale _ hf₀ hf₀c, hf₀i, mul_one]
  have hδavg (q : LeftQuotient (sigmaCentralizer σ 1 δ)) :
      quotientAverageReal (sigmaCentralizer σ 1 δ) μδ b q = scale := by
    induction q using Quotient.inductionOn with
    | h x => exact habove x
  have hγavg (q : LeftQuotient (glCentralizer γ)) :
      quotientAverageReal (glCentralizer γ) μγ f₀ q = scale := by
    induction q using Quotient.inductionOn with
    | h x => exact hbelow x
  have hδi := hδ.integral_quotientAverageReal b b.continuous b.hasCompactSupport
  have hγi := hγ.integral_quotientAverageReal f₀ hf₀ hf₀c
  simp_rw [hδavg, integral_const, measureReal_def, smul_eq_mul] at hδi
  simp_rw [hγavg, integral_const, measureReal_def, smul_eq_mul, hf₀i] at hγi
  calc
    _ = (νδ Set.univ).toReal * ((νγ Set.univ).toReal * scale) := by rw [hγi, mul_one]
    _ = ((νδ Set.univ).toReal * scale) * (νγ Set.univ).toReal := by ring
    _ = _ := by rw [hδi]

end RelativeMass

section Concordance

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {E : Type v} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  [Algebra F E] [IsModuleTopology F E] [FiniteDimensional F E]
  [MeasurableSpace (GeneralLinear 1 F)] [BorelSpace (GeneralLinear 1 F)]
  [MeasurableSpace (GeneralLinear 1 E)] [BorelSpace (GeneralLinear 1 E)]
  [LocallyCompactSpace (GeneralLinear 1 E)]
  {σ : E ≃ₐ[F] E} {l : ℕ}

/-- Rank-one norm pullback, with the quotient mass ratio as scale, gives
concordance for all compatible choices of associated measures. -/
theorem IsCyclicAlgebra.exists_rankOne_concordanceScale (hcyc : IsCyclicAlgebra σ l)
    (hK : IsCompact (Set.univ : Set (LeftQuotient (sigmaCentralizer σ 1 1))))
    (μF : Measure (GeneralLinear 1 F)) [μF.IsHaarMeasure] [μF.Regular]
    (μE : Measure (GeneralLinear 1 E)) [μE.IsHaarMeasure] :
    ∃ r : ℝ, 0 < r ∧
      ∀ (φ : GeneralLinear 1 E → ℂ) (f : GeneralLinear 1 F → ℂ),
        (∀ δ, f (rankOneNorm δ) = (r : ℂ) * φ δ) →
        (∀ γ, f γ ≠ 0 → γ ∈ Set.range (rankOneNorm (F := F) (E := E))) →
        AreConcordant σ l μF μE φ f := by
  obtain ⟨r, hr, hmass⟩ := hcyc.exists_rankOne_quotientMassRatio hK μF μE
  refine ⟨r, hr, fun φ f hpull hoff => ?_⟩
  have hordinary (γ : GeneralLinear 1 F) (ν : Measure (LeftQuotient (glCentralizer γ))) :
      orbitalIntegral γ ν f = (ν Set.univ).toReal • f γ := by
    have h (q : LeftQuotient (glCentralizer γ)) :
        twistedOrbitFunction (MonoidHom.id (GeneralLinear 1 F)) γ f q = f γ := by
      induction q using Quotient.inductionOn with
      | h x => simp only [twistedOrbitFunction_mk, MonoidHom.id_apply, rankOne_inv_mul_mul_eq]
    simp_rw [orbitalIntegral, twistedOrbitalIntegral, h, integral_const, measureReal_def]
  constructor
  · intro γ _ hnot μγ _ _ ν _
    rw [hordinary]
    have hzero : f γ = 0 := by
      by_contra hn
      obtain ⟨δ, hδ⟩ := hoff γ hn
      exact hnot ⟨δ, (hcyc.isNormAssociated_rankOne_iff δ γ).mpr hδ⟩
    rw [hzero, smul_zero]
  · intro δ γ hassoc _ μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    have hnorm (x : GeneralLinear 1 E) :
        rankOneNorm (x⁻¹ * δ * entrywiseAut σ 1 x) = rankOneNorm (F := F) δ := by
      apply (hcyc.isNormAssociated_rankOne_iff _ _).mp
      have h := (hcyc.isNormAssociated_rankOne_iff δ (rankOneNorm δ)).mpr rfl
      simpa only [inv_one, one_mul, mul_one] using h.twistedConj hcyc.pow_eq_one x (1 : GeneralLinear 1 F)
    have htwisted (q : LeftQuotient (sigmaCentralizer σ 1 δ)) :
        twistedOrbitFunction (entrywiseAut σ 1) δ φ q = φ δ := by
      induction q using Quotient.inductionOn with
      | h x =>
        rw [twistedOrbitFunction_mk]
        apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
        rw [← hpull, ← hpull, hnorm]
    have hδ : sigmaOrbitalIntegral σ 1 δ νδ φ = (νδ Set.univ).toReal • φ δ := by
      simp_rw [sigmaOrbitalIntegral, twistedOrbitalIntegral, htwisted, integral_const, measureReal_def]
    have heq := congrArg f ((hcyc.isNormAssociated_rankOne_iff δ γ).mp hassoc)
    rw [hpull] at heq
    rw [hδ, hordinary, hmass δ γ μδ μγ νδ νγ hνδ hνγ hμ, ← heq]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring

end Concordance

end Langlands.BaseChange
