import Langlands.BaseChange.TwistedCharacter.CyclicAdjointFrequency
import Langlands.BaseChange.TwistedCharacter.CompactNormDescentWitness
import Langlands.BaseChange.TwistedCharacter.SliceNormOrbitMatching
import Langlands.BaseChange.TwistedCharacter.FiniteSemidirectHaar
import Langlands.BaseChange.TwistedCharacter.SemisimpleOrbitControl
import Langlands.HarmonicAnalysis.UnitConjugation.ProjectedOrbitNilpotence

/-! # Localization of the compact trace tests in cyclic semisimple descent -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis UnitConjugation Character
  Function Filter Set Metric _root_.Topology
open scoped SemidirectProduct _root_.Topology

local notation "L(" A "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)

/-- For the actual cyclic descent distribution, a nonzero small slice trace
has a frequency in its orbit that is bounded or rescales near a nilpotent. -/
def CyclicCompactTraceLocalizationStatement.{u, v, w} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (hE : IsCyclicAlgebra σ l),
    haveI : NeZero l := ⟨hE.pos.ne'⟩
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    haveI := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
    let Mat := Matrix (Fin n) (Fin n) E
    let G := GeneralLinear n E
    let H := CyclicGLSemidirect σ hE.pow_eq_one n
    letI : NontriviallyNormedField F := LocalGalois.localNormedField F
    letI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
    letI : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
    letI : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
    letI : NormedRing Mat := finiteAlgebraNormedRing F Mat
    letI : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
    letI : CompleteSpace Mat := FiniteDimensional.complete F Mat
    letI : IsUltrametricDist Mat := finiteAlgebraNormedRing_ultrametric F Mat
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace H := borel H
    haveI : BorelSpace H := ⟨rfl⟩
    ExponentialProductStraighteningStatement F Mat →
    ∀ {W : Type w} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ H W) (hπ : IsAdmissible π),
      π.IsIrreducible → ∀ (s : H), IsCyclicGLSemisimple s → ∀ (ν : Measure H) [ν.IsHaarMeasure],
        let α := cyclicAdjointAlgEquiv s
        let S := adjointFixedAlgebra α
        let U := adjointConjugationDomain α
        let i : G →* H := SemidirectProduct.inl
        let hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
        let j := translatedCosetEmbedding i s
        let μ := ν.comap j
        let D := translatedCosetDistribution i hi s (Character.distribution ν π hπ)
        letI : MeasurableSpace S := borel S
        letI : ProperSpace S := FiniteDimensional.proper F S
        letI : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : Mat => x ∈ S)
        ∀ (ρ : AdditiveHaarMeasure S) (P : SchwartzBruhat (G × U) →ₗ[ℂ] SchwartzBruhat G) (T : Distribution U),
          SchwartzBruhat.IsTestPushforward (μ.prod (ρ.measure.comap Subtype.val)) μ
            (adjointConjugationOnUnits α) P →
          (letI : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap' ν
              (isOpenEmbedding_translatedCoset i hi s).continuous (isOpenEmbedding_translatedCoset i hi s).measurableEmbedding
           D.comp P = Distribution.tensor (Distribution.ofMeasure μ) T) →
          ∀ (ψ : UnitaryAdditiveCharacter F) (d : F), 1 < ‖d‖ → ∀ (V : Set S), IsOpen V →
          (∀ x : S, 1 / ‖d‖ ≤ ‖x‖ → ‖x‖ ≤ 1 → IsNilpotent x → x ∈ V) →
          let BS := adjointFixedTracePairing α
          let eS := pairingCharacter ψ BS
          ∃ ε > (0 : ℝ), ∃ b > (0 : ℝ),
            ∀ (t : ℝ) (ht : 0 < t) (ht₁ : t < 1), t ≤ ε →
            ∀ htU : closedBall (0 : S) t ⊆ U,
              let M := normUnitCongruence (R := S) ht.le ht₁
              letI : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence ht.le ht₁)
              let hb := isOpenEmbedding_adjointNormSlice α ht ht₁ htU
              ∀ (heS : IsSelfDualBicharacter eS) (Z : S) (B : Subgroup Sˣ)
                (O : Finset (AddChar L(S, ht) ℂ)) (τ : SmoothRep.{0, v, v} ℂ M) [FiniteDimensional ℂ τ],
              (O : Set (AddChar L(S, ht) ℂ)) = latticeCharacterOrbit heS L(S, ht) B Z →
              (∀ (x : L(S, ht)) (k : M), (k.val : S) = NormedSpace.exp (x : S) →
                τ.representation.character k = ∑ χ ∈ O, χ x) →
              T (openEmbeddingTestExtension hb (compactTraceTest τ.representation τ.isSmooth)) ≠ 0 →
              ∃ Y ∈ conjugationCosetOrbit B (heS.annihilator (L(S, ht) : Set S)) Z,
                b < ‖Y‖ → ∃ a : F, a ≠ 0 ∧ 1 / ‖d‖ ≤ ‖a • Y‖ ∧ ‖a • Y‖ ≤ 1 ∧ a • Y ∈ V

private theorem normCongruence_preserves_dual {A : Type*} [NormedRing A] [IsUltrametricDist A]
    {e : A → A → ℂ} (he : IsSelfDualBicharacter e)
    (hinv : ∀ k : Aˣ, ∀ x z, e (conjugationHomeomorph k x) (conjugationHomeomorph k z) = e x z)
    {r q : ℝ} (hr : 0 < r) (hq : 0 ≤ q) (hq₁ : q < 1) (hsmall : max 1 ‖(1 : A)‖ * q < 1) :
    ∀ k ∈ normUnitCongruence (R := A) hq hq₁,
      ∀ z ∈ he.annihilator (L(A, hr) : Set A), conjugationHomeomorph k z ∈ he.annihilator (L(A, hr) : Set A) := by
  intro k hk z hz
  apply he.mem_annihilator.mpr
  intro x hx
  let w := conjugationHomeomorph k⁻¹ x
  have hw : w ∈ L(A, hr) := by
    change dist w 0 ≤ r
    rw [dist_zero_right, norm_conjugation_eq_of_mem_normUnitCongruence hq hq₁ hsmall
      ((normUnitCongruence hq hq₁).inv_mem hk)]
    exact dist_zero_right x ▸ hx
  have hcancel : conjugationHomeomorph k w = x := by
    rw [show w = conjugationHomeomorph k⁻¹ x from rfl, ← conjugationHomeomorph_mul,
      mul_inv_cancel, conjugationHomeomorph_one]
  rw [← hcancel, hinv]
  exact he.mem_annihilator.mp hz w hw

set_option maxHeartbeats 2800000 in
theorem cyclicCompactTraceLocalization.{u, v, w} : CyclicCompactTraceLocalizationStatement.{u, v, w} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE Mat G H
  let : NeZero l := ⟨hE.pos.ne'⟩
  let : Module.Finite F E := hE.1
  let : IsReduced E := hE.2.2.1
  let : IsArtinianRing E := IsArtinianRing.of_finite F E
  let : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E
  let : T2Space (GeneralLinear n E) := generalLinear_t2Space_of_finite F E n
  let : LocallyCompactSpace (GeneralLinear n E) := generalLinear_locallyCompactSpace_of_finite F E n
  let : TotallyDisconnectedSpace (GeneralLinear n E) := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedRing Mat := finiteAlgebraNormedRing F Mat
  let : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
  let : CompleteSpace Mat := FiniteDimensional.complete F Mat
  let : IsUltrametricDist Mat := finiteAlgebraNormedRing_ultrametric F Mat
  let : ProperSpace Mat := FiniteDimensional.proper F Mat
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology E := (finiteAlgebraTopology F E).2.2
  let : SecondCountableTopology Mat := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let : SecondCountableTopology G := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace Mat := borel Mat
  let : BorelSpace Mat := ⟨rfl⟩
  let : CompactOpenExhaustion Mat := compactOpenExhaustion_of_finiteDimensional F Mat
  intro hStraighten W _ _ π hπ hirr s hs ν hν α S U i hi j μ D
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : MeasurableSpace Sˣ := borel Sˣ
  let : BorelSpace Sˣ := ⟨rfl⟩
  let : ProperSpace S := FiniteDimensional.proper F S
  let : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : Mat => x ∈ S)
  let : IsModuleTopology F S := isModuleTopologyOfFiniteDimensional
  let : CompactOpenExhaustion S := compactOpenExhaustion_of_finiteDimensional F S
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  let : (ν.comap i).IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) ν hi
  let : ν.IsMulRightInvariant := finiteSemidirectHaar (cyclicGLAction σ hE.pow_eq_one n) ν
    (generalLinear_haar_rightInvariant E n (ν.comap i))
  intro ρ P T hP hT ψ d hd V hV hNil BS eS
  have hα : Module.End.IsSemisimple α.toLinearMap := hs
  let BMat := Langlands.Algebra.regularTraceForm F Mat
  let eMat := pairingCharacter ψ BMat
  have hBMat : IsInvariantPairing BMat := isInvariantPairing_regularTraceForm
  have heMat : IsSelfDualBicharacter eMat := isSelfDualBicharacter_pairingCharacter ψ hBMat.isSymm hBMat.nondegenerate
  have heS : IsSelfDualBicharacter eS := isSelfDualBicharacter_pairingCharacter ψ
    (adjointFixedTracePairing_isSymm α) (adjointFixedTracePairing_nondegenerate α hα)
  have heMatInv (k : G) (x z : Mat) : eMat (conjugationHomeomorph k x) (conjugationHomeomorph k z) = eMat x z :=
    congrArg (fun a : F => ψ.complex a) (hBMat.conj_invariant k x z)
  obtain ⟨p, C, hC, hpS, hpId, hpα, hTrans⟩ := semisimpleTransverseEstimate α hα
  let pr : Mat →ₗ[F] S := p.toLinearMap.codRestrict S.toSubmodule hpS
  let Q : Mat →L[F] S := pr.toContinuousLinearMap
  have hQ (x : Mat) : (Q x).val = p x := rfl
  have hpFix (x : S) : pr x.val = x := Subtype.ext (hpId x.val x.property)
  have hpInv (x : Mat) : pr (α x) = pr x := Subtype.ext (hpα x)
  have hAdj (x : Mat) (y : S) : eS (Q x) y = eMat x y.val :=
    congrArg (fun a : F => ψ.complex a) (fixedTraceProjection α pr hpFix hpInv x y)
  obtain ⟨c, hc, ε₀, hε₀, dM, hdM, hsmall, hWitness⟩ :=
    compactNormDescentWitness α i hi s ν ρ.measure π hπ heMat P T
      (cyclicAdjointAlgEquiv_onUnits s) hStraighten heMatInv hirr hP hT
  obtain ⟨εS, hεS, εG, hεG, hSlice⟩ :=
    sliceNormOrbitMatching i hi S.val Q.toLinearMap.toAddMonoidHom heS heMat Q.continuous hAdj
  obtain ⟨εI, hεI, hSelf⟩ := conjugateNormOrbitMatching (F := F) i hi heMat
  obtain ⟨εF, hεF, hFixed⟩ := conjugateNormFixedOrbit (F := F) i hi heMat
  obtain ⟨r₀, hr₀, hr₀₁, hr₀ε, hK₀⟩ := exists_fixedVector_normUnitOpenSubgroupImage i hi π hπ.1 hirr εF hεF
  let L₀ := L(Mat, hr₀)
  let D₀ := heMat.annihilator (L₀ : Set Mat)
  have hD₀ : IsCompact (D₀ : Set Mat) := heMat.isCompact_annihilator_compactOpen L₀
    (IsUltrametricDist.isOpen_closedBall _ hr₀.ne') (isCompact_closedBall _ _)
  obtain ⟨ω, hω, hωAdj⟩ := cyclicAdjointCompactSaturation (σ := σ) (hσ := hE.pow_eq_one) (D₀ : Set Mat) hD₀
  let V' := Q ⁻¹' V
  have hV' : IsOpen V' := hV.preimage Q.continuous
  have hNil' : ∀ x ∈ projectedAnnulus p d, IsNilpotent x → x ∈ V' := by
    intro x hx hn
    have hfx : α x = x := by
      obtain ⟨y, hy⟩ := hx.2.1
      exact hy ▸ hpS y
    have hQx : (Q x).val = x := (hQ x).trans (hpId x hfx)
    apply hNil (Q x)
    · change 1 / ‖d‖ ≤ ‖(Q x).val‖
      rw [hQx]
      exact hx.2.2
    · change ‖(Q x).val‖ ≤ 1
      rw [hQx]
      exact dist_zero_right x ▸ hx.1
    · apply (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp
      change IsNilpotent (Q x).val
      rwa [hQx]
  obtain ⟨b₀, hb₀, η, hη, hOrbit⟩ := projectedOrbitNearNilpotents p d ω V' C hd hω hV' hC hNil'
  let Dmax := max 1 ‖(1 : Mat)‖
  have hDmax : 1 ≤ Dmax := le_max_left _ _
  have hDpos : 0 < Dmax := zero_lt_one.trans_le hDmax
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let R := min 1 (min ε₀ (min εG (min εI (min εF (η / (Dmax * c))))))
  have hR : 0 < R := lt_min zero_lt_one (lt_min hε₀ (lt_min hεG (lt_min hεI (lt_min hεF
    (div_pos hη (mul_pos hDpos hcpos))))))
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrBounds : r < 1 ∧ r < ε₀ ∧ r < εG ∧ r < εI ∧ r < εF ∧ r < η / (Dmax * c) := by
    simpa only [R, lt_min_iff] using (half_lt_self hR : r < R)
  obtain ⟨hr₁, hrε₀, hrεG, hrεI, hrεF, hrη⟩ := hrBounds
  have hSmallR : Dmax * (c * r) < 1 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrε₀.le hcpos.le) hDpos.le).trans_lt hsmall
  have hcr : c * r < 1 := (le_mul_of_one_le_left (mul_nonneg hcpos.le hr.le) hDmax).trans_lt hSmallR
  have hrD : Dmax * (c * r) < η := by
    have h := (lt_div_iff₀ (mul_pos hDpos hcpos)).mp hrη
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  let Br := normUnitCongruence (R := Mat) (mul_nonneg (zero_le_one.trans hc) hr.le) hcr
  let Lr := L(Mat, hr)
  let Dr := heMat.annihilator (Lr : Set Mat)
  have hDr : IsCompact (Dr : Set Mat) := heMat.isCompact_annihilator_compactOpen Lr
    (IsUltrametricDist.isOpen_closedBall _ hr.ne') (isCompact_closedBall _ _)
  obtain ⟨bA, hbA⟩ := hDr.exists_bound_of_continuousOn (continuous_id : Continuous (id : Mat → Mat)).continuousOn
  obtain ⟨t₀, ht₀, ht₀₁, hMtrans⟩ := exists_normUnitCongruence_subset hTrans
  refine ⟨min dM (min εS t₀), lt_min hdM (lt_min hεS ht₀), b₀ * max 1 bA,
    mul_pos hb₀ (zero_lt_one.trans_le (le_max_left _ _)), ?_⟩
  intro t ht ht₁ htε htU
  let M := normUnitCongruence (R := S) ht.le ht₁
  let B' := normUnitOpenSubgroup (A := Mat) hr hr₁
  let K' := openSubgroupImage B' i hi
  let ι := adjointNormSliceHom α ht ht₁ i
  let hb := isOpenEmbedding_adjointNormSlice α ht ht₁ htU
  let : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence ht.le ht₁)
  change ∀ (hS : IsSelfDualBicharacter eS) (Z : S) (B : Subgroup Sˣ)
    (O : Finset (AddChar L(S, ht) ℂ)) (τ : SmoothRep.{0, v, v} ℂ M) [FiniteDimensional ℂ τ], _
  intro hS Z B O τ hτfd hO hEval hNZ
  obtain ⟨z, O', τ', hτfd', hO', hEval', hInt, m, _, hInter, hFix⟩ :=
    hWitness r hr hr₁ hcr hrε₀.le t ht ht₁ (htε.trans (min_le_left _ _)) htU τ hNZ
  let : FiniteDimensional ℂ τ' := hτfd'
  let y := s * ι m
  let γ := cyclicAdjointAlgEquiv y
  obtain ⟨Y, hY, hproj⟩ := hSlice t ht ht₁ r hr hr₁
    (htε.trans ((min_le_right _ _).trans (min_le_left _ _))) hrεG.le
    τ'.representation τ.representation τ'.isSmooth τ.isSmooth B Br Z z O O' hO hO' hEval hEval' hInt
  obtain ⟨X, hX, hγX⟩ := hSelf r hr hr₁ r hr hr₁ hrεI.le hrεI.le y γ
    (cyclicAdjointAlgEquiv_symm_onUnits y) (cyclicAdjoint_pairingCharacter ψ y)
    τ'.representation τ'.representation τ'.isSmooth τ'.isSmooth Br Br z z O' O' hO' hO' hEval' hEval' hInter
  obtain ⟨g, hJg⟩ := hFix (openSubgroupImage (normUnitOpenSubgroup hr₀ hr₀₁) i hi) hK₀
  obtain ⟨x, hx, hxg⟩ := hFixed r hr hr₁ r₀ hr₀ hr₀₁ hrεF.le hr₀ε g (cyclicAdjointAlgEquiv g)
    (cyclicAdjointAlgEquiv_symm_onUnits g) (cyclicAdjoint_pairingCharacter ψ g)
    τ'.representation τ'.isSmooth Br z O' hO' hEval' hJg
  have hβ (u : Mat) : ‖u - p u‖ ≤ C * ‖γ u - u‖ := by
    have hm₀ : m.val ∈ normUnitCongruence (R := S) ht₀.le ht₀₁ := by
      exact (show ‖(m.val : S) - 1‖ ≤ t from m.property).trans
        (htε.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hm := hMtrans hm₀ u
    change ‖u - p u‖ ≤ C * ‖fixedUnitAdjoint α m.val u - u‖ at hm
    rw [show γ u = fixedUnitAdjoint α m.val u from cyclicAdjointAlgEquiv_mul_fixedUnit s m.val u]
    exact hm
  refine ⟨Q Y, hproj, fun hYlarge => ?_⟩
  have hA (k : Matˣ) (hk : k ∈ Br) (z : Mat) : ‖conjugationHomeomorph k z - z‖ ≤ Dmax * (c * r) * ‖z‖ :=
    normUnitConjugationDisplacement (mul_nonneg (zero_le_one.trans hc) hr.le) hcr k hk z
  obtain ⟨a, ha, hAnn, hVY⟩ := hOrbit Br Dr z γ bA (Dmax * (c * r))
    (normCongruence_preserves_dual heMat heMatInv hr _ hcr hSmallR)
    hbA hA hβ hrD ⟨X, hX, hγX⟩ ⟨cyclicAdjointAlgEquiv g x, hxg, hωAdj g x hx⟩ Y hY hYlarge
  have hLower : 1 / ‖d‖ ≤ ‖a • Q Y‖ := hAnn.2.2
  have hUpper : ‖a • Q Y‖ ≤ 1 := dist_zero_right (a • p Y) ▸ hAnn.1
  have hImg : Q (a • p Y) = a • Q Y := by
    rw [map_smul]
    exact congrArg (a • ·) (Subtype.ext (show (Q (p Y)).val = (Q Y).val from hpId (p Y) (hpS Y)))
  change Q (a • p Y) ∈ V at hVY
  rw [hImg] at hVY
  exact ⟨a, ha, hLower, hUpper, hVY⟩

end Langlands.BaseChange
