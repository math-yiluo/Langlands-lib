import Langlands.BaseChange.RankOneCyclicQuotientMass
import Langlands.LocalFactor.Abelian.LocalAnalysisHelpers
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof

/-! # Rank-one character pullback from distributional concordance -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis JacquetLanglands RankinSelberg
open LocalClassField ClassFieldTheory.Local

universe u v uV uW

private theorem determinant_rankOne_scalar {K : Type*} [Field K] (x : Kˣ) :
    determinant (scalar (n := 1) x) = x := by
  simp [determinant, Matrix.GeneralLinearGroup.det_scalar]

private theorem rankOne_action_in_character_coordinates
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear 1 K) V} {χ : Kˣ →* ℂˣ}
    (e : ρ.Equiv (rankOneCharacter χ)) (g : GeneralLinear 1 K) :
    ρ g = (χ (determinant g) : ℂ) • LinearMap.id := by
  ext x
  apply e.toLinearEquiv.injective
  change e (ρ g x) = e ((χ (determinant g) : ℂ) • x)
  rw [Conductor.rankOneCharacterEquiv_apply e, map_smul, smul_eq_mul]

private theorem rankOne_action_eq_of_ratio
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear 1 K) V} {χ : Kˣ →* ℂˣ}
    (e : ρ.Equiv (rankOneCharacter χ)) (a g : GeneralLinear 1 K)
    (ha : χ (determinant (a⁻¹ * g)) = 1) : ρ g = ρ a := by
  have h : χ (determinant g) = χ (determinant a) := by
    conv_lhs => rw [← mul_inv_cancel_left a g]
    rw [map_mul, map_mul, ha, mul_one]
  simp only [rankOne_action_in_character_coordinates e, h]

private theorem rankOne_character_invariant
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {σ : E ≃ₐ[F] E}
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {P : Representation ℂ (GeneralLinear 1 E) W} {η : Eˣ →* ℂˣ}
    (e : P.Equiv (rankOneCharacter η)) (A : SigmaIntertwiner σ 1 P) (x : Eˣ) :
    η (Units.map σ.toMonoidHom x) = η x := by
  have hdet : determinant (entrywiseAut σ 1 (scalar x)) = Units.map σ.toMonoidHom x := by
    apply Units.ext
    change ((entrywiseAut σ 1 (scalar x) : GeneralLinear 1 E) :
      Matrix (Fin 1) (Fin 1) E).det = σ (x : E)
    simp [entrywiseAut_apply_apply, Matrix.GeneralLinearGroup.coe_scalar]
  have h := A.comp_apply_eq (scalar x)
  simp only [rankOne_action_in_character_coordinates e, determinant_rankOne_scalar, hdet,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_id, LinearMap.id_comp] at h
  have hv := LinearMap.congr_fun h (A.toLinearEquiv.symm (e.toLinearEquiv.symm 1))
  change (η x : ℂ) • A.toLinearEquiv (A.toLinearEquiv.symm (e.toLinearEquiv.symm 1)) =
    (η (Units.map σ.toMonoidHom x) : ℂ) •
      A.toLinearEquiv (A.toLinearEquiv.symm (e.toLinearEquiv.symm 1)) at hv
  rw [LinearEquiv.apply_symm_apply] at hv
  apply Units.ext
  have h' := congrArg (e.toLinearEquiv : W → ℂ) hv
  simpa only [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, mul_one] using h'.symm

private theorem twistedDistribution_of_constant_action_on_support
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (A T : Module.End ℂ V) (f : SchwartzBruhat G)
    (hconst : ∀ x, f x ≠ 0 → ρ x = T) :
    twistedDistribution μ ρ hρ A f = LinearMap.trace ℂ V (T ∘ₗ A) * ∫ y, f y ∂μ := by
  let b := Module.finBasis ℂ V
  have hact : Hecke.integratedAction μ ρ hρ.1 f = (∫ y, f y ∂μ) • T := by
    ext v
    refine b.ext_elem fun i => ?_
    rw [← b.coord_apply, ← b.coord_apply, Hecke.integratedAction_dual, LinearMap.smul_apply,
      map_smul, smul_eq_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : f y = 0
    · simp [hy]
    · simp only
      rw [hconst y hy]
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_ambient]
  change LinearMap.trace ℂ V ((Hecke.integratedAction μ ρ hρ.1 f) ∘ₗ A) = _
  rw [hact, LinearMap.smul_comp, map_smul, smul_eq_mul, mul_comm]

/-- On supplied p-adic field carriers, the character of a rank-one
distributional sigma-lift is the pullback by the actual field norm. -/
def RankOneSigmaLiftNormPullbackStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    (T : F.TopologicalData) (S : E.TopologicalData)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier],
    letI := T.topology
    letI := S.topology
    ∀ [IsModuleTopology F.Carrier E.Carrier]
      (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear 1 F.Carrier) V) (hπ : IsAdmissible π)
      (P : Representation ℂ (GeneralLinear 1 E.Carrier) W) (hP : IsAdmissible P)
      (A : SigmaIntertwiner σ 1 P) (c : ℂ),
      (letI := T.valuativeRel
       letI := S.valuativeRel
       letI := T.localField
       letI := S.localField
       haveI := LocalFieldTopology.generalLinear_t2Space F.Carrier 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier 1
       haveI := LocalFieldTopology.generalLinear_t2Space E.Carrier 1
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier 1
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier 1
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ (χ : Quasicharacter F.Carrier) (η : Quasicharacter E.Carrier),
      π.Equiv (rankOneCharacter χ.toMonoidHom) → P.Equiv (rankOneCharacter η.toMonoidHom) →
        η.toMonoidHom = χ.toMonoidHom.comp (Units.map (Algebra.norm F.Carrier : E.Carrier →* F.Carrier))

theorem rankOneSigmaLiftNormPullback : RankOneSigmaLiftNormPullbackStatement.{u, v, uV, uW} := by
  intro p _ F E T S _ _
  let := T.topology
  let := S.topology
  intro _ σ l hcyc V _ _ W _ _ π hπ P hP A c hlift χ η eπ eP
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  let := S.fieldT2
  let := LocalFieldTopology.generalLinear_t2Space F.Carrier 1
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier 1
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier 1
  let := LocalFieldTopology.generalLinear_t2Space E.Carrier 1
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier 1
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier 1
  let : MeasurableSpace (GeneralLinear 1 F.Carrier) := borel _
  have : BorelSpace (GeneralLinear 1 F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear 1 E.Carrier) := borel _
  have : BorelSpace (GeneralLinear 1 E.Carrier) := ⟨rfl⟩
  let : FiniteDimensional F.Carrier E.Carrier := hcyc.1
  let : IsGalois F.Carrier E.Carrier := hcyc.isGalois
  let : IsCyclic (E.Carrier ≃ₐ[F.Carrier] E.Carrier) := by
    refine isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨σ, ?_⟩
    rw [IsGalois.card_aut_eq_finrank, hcyc.2.1, hcyc.2.2.2.1]
  let : IsAbelianGalois F.Carrier E.Carrier := IsAbelianGalois.of_isCyclic F.Carrier E.Carrier
  let : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective eπ.toLinearEquiv.toLinearMap eπ.toLinearEquiv.injective
  let : FiniteDimensional ℂ W :=
    FiniteDimensional.of_injective eP.toLinearEquiv.toLinearMap eP.toLinearEquiv.injective
  let μF : Measure (GeneralLinear 1 F.Carrier) := Measure.haar
  let μE : Measure (GeneralLinear 1 E.Carrier) := Measure.haar
  obtain ⟨r, hr, hconcord⟩ := hcyc.exists_rankOne_concordanceScale
    (isCompact_rankOneTwistedCentralizerQuotient S σ 1) μF μE
  have hηker : (localNorm T S) ⁻¹' {1} ⊆ {x | η x = 1} := by
    intro x hx
    exact hcyc.character_eq_one_of_norm_eq_one η.toMonoidHom
      (rankOne_character_invariant eP A) x hx
  obtain ⟨D, hDo, hDc, hD₁, hDχ, hDN, hNo, hNc, hNη⟩ :=
    exists_compactOpen_normPreimage T S {x | χ x = 1} {x | η x = 1}
      (LocalFactor.PadicAbelian.quasicharacter_open_kernel T χ) (map_one χ)
      (LocalFactor.PadicAbelian.quasicharacter_open_kernel S η) hηker
  let detF := rankOneDeterminantEquiv F.Carrier
  let detE := rankOneDeterminantEquiv E.Carrier
  let N := rankOneNorm (F := F.Carrier) (E := E.Carrier)
  have hdetN (g : GeneralLinear 1 E.Carrier) :
      determinant (N g) = localNorm T S (determinant g) :=
    detF.apply_symm_apply _
  let B := detF ⁻¹' D
  let C := detE ⁻¹' ((localNorm T S) ⁻¹' D)
  have hBo : IsOpen B := hDo.preimage detF.continuous
  have hCo : IsOpen C := hNo.preimage detE.continuous
  have hBc : IsCompact B := detF.toHomeomorph.isCompact_preimage.mpr hDc
  have hCc : IsCompact C := detE.toHomeomorph.isCompact_preimage.mpr hNc
  have hB₁ : (1 : GeneralLinear 1 F.Carrier) ∈ B := by
    change determinant (1 : GeneralLinear 1 F.Carrier) ∈ D
    rwa [map_one]
  have hCB (g : GeneralLinear 1 E.Carrier) : g ∈ C ↔ N g ∈ B := by
    change localNorm T S (determinant g) ∈ D ↔ determinant (N g) ∈ D
    rw [hdetN]
  have hBrange {g : GeneralLinear 1 F.Carrier} (hg : g ∈ B) : g ∈ Set.range N := by
    obtain ⟨x, hx⟩ := hDN hg
    change localNorm T S x = determinant g at hx
    refine ⟨scalar x, detF.injective ?_⟩
    change determinant (N (scalar x)) = determinant g
    rw [hdetN, determinant_rankOne_scalar, hx]
  let φ₀ := compactOpenIndicator C hCc hCo
  let f₀ := (r : ℂ) • compactOpenIndicator B hBc hBo
  have hφ₀ (g : GeneralLinear 1 E.Carrier) : φ₀ g = C.indicator (fun _ => (1 : ℂ)) g := rfl
  have hf₀ (g : GeneralLinear 1 F.Carrier) :
      f₀ g = (r : ℂ) * B.indicator (fun _ => (1 : ℂ)) g := rfl
  let IE := ∫ y, φ₀ y ∂μE
  let IF := ∫ y, f₀ y ∂μF
  have hIF : IF ≠ 0 := by
    change (∫ y, f₀ y ∂μF) ≠ 0
    simp_rw [hf₀]
    rw [integral_const_mul, integral_indicator hBo.measurableSet, setIntegral_const,
      measureReal_def, Complex.real_smul, mul_one]
    have hpos := ENNReal.toReal_pos (hBo.measure_pos μF ⟨1, hB₁⟩).ne' hBc.measure_lt_top.ne
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.ofReal_ne_zero.mpr hpos.ne')
  have hdim : Module.finrank ℂ V = 1 :=
    eπ.toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)
  have hpoint (δ : GeneralLinear 1 E.Carrier) :
      (η (determinant δ) : ℂ) * (LinearMap.trace ℂ W A.toLinearMap * IE) =
        (χ (determinant (N δ)) : ℂ) * (c * IF) := by
    let γ := N δ
    let φ := Hecke.TestFunction.leftTranslate δ φ₀
    let f := Hecke.TestFunction.leftTranslate γ f₀
    have hpull (x : GeneralLinear 1 E.Carrier) : f (N x) = (r : ℂ) * φ x := by
      change f₀ (γ⁻¹ * N x) = (r : ℂ) * φ₀ (δ⁻¹ * x)
      rw [← map_inv N, ← map_mul N, hf₀, hφ₀]
      by_cases hx : δ⁻¹ * x ∈ C
      · rw [Set.indicator_of_mem ((hCB _).mp hx), Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem (fun h => hx ((hCB _).mpr h)), Set.indicator_of_notMem hx]
    have hoff (g : GeneralLinear 1 F.Carrier) (hg : f g ≠ 0) : g ∈ Set.range N := by
      have hx : γ⁻¹ * g ∈ B := by
        by_contra h
        exact hg (by change f₀ (γ⁻¹ * g) = 0; rw [hf₀, Set.indicator_of_notMem h, mul_zero])
      obtain ⟨x, hx⟩ := hBrange hx
      refine ⟨δ * x, ?_⟩
      rw [map_mul, hx, mul_inv_cancel_left]
    have hEact (g : GeneralLinear 1 E.Carrier) (hg : φ g ≠ 0) : P g = P δ := by
      apply rankOne_action_eq_of_ratio eP
      apply hNη
      change δ⁻¹ * g ∈ C
      by_contra h
      exact hg (by change φ₀ (δ⁻¹ * g) = 0; rw [hφ₀, Set.indicator_of_notMem h])
    have hFact (g : GeneralLinear 1 F.Carrier) (hg : f g ≠ 0) : π g = π γ := by
      apply rankOne_action_eq_of_ratio eπ
      apply hDχ
      change γ⁻¹ * g ∈ B
      by_contra h
      exact hg (by change f₀ (γ⁻¹ * g) = 0; rw [hf₀, Set.indicator_of_notMem h, mul_zero])
    have hIE : (∫ y, φ y ∂μE) = IE := integral_mul_left_eq_self (μ := μE) φ₀ δ⁻¹
    have hIF' : (∫ y, f y ∂μF) = IF := integral_mul_left_eq_self (μ := μF) f₀ γ⁻¹
    have hE := twistedDistribution_of_constant_action_on_support μE P hP A.toLinearMap (P δ) φ hEact
    rw [rankOne_action_in_character_coordinates eP, LinearMap.smul_comp, LinearMap.id_comp,
      map_smul, smul_eq_mul, hIE] at hE
    have hF := twistedDistribution_of_constant_action_on_support μF π hπ LinearMap.id (π γ) f hFact
    rw [LinearMap.comp_id, show (LinearMap.id : Module.End ℂ V) = 1 from rfl, twistedDistribution_one,
      rankOne_action_in_character_coordinates eπ, map_smul, LinearMap.trace_id, hdim,
      Nat.cast_one, smul_eq_mul, mul_one, hIF'] at hF
    calc
      _ = twistedDistribution μE P hP A.toLinearMap φ := by
        rw [hE]
        exact (mul_assoc _ _ _).symm
      _ = c * Character.distribution μF π hπ f :=
        hlift.2 μF μE φ f (hconcord φ f hpull hoff)
      _ = _ := by
        rw [hF]
        exact mul_left_comm _ _ _
  have hcalibration : LinearMap.trace ℂ W A.toLinearMap * IE = c * IF := by
    simpa only [map_one, Units.val_one, one_mul] using hpoint 1
  ext x
  apply mul_right_cancel₀ (mul_ne_zero hlift.1 hIF)
  have h := hpoint (scalar x)
  rw [hcalibration, hdetN, determinant_rankOne_scalar] at h
  exact h

end Langlands.BaseChange
