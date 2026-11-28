import Langlands.Global.AdelicEisensteinTemperedTruncationEstimate
import Langlands.Global.AdelicTopEisensteinContinuation
import Langlands.Global.AdelicNormOneQuotientIso
import Langlands.Global.AdelicCharacteristicRegionCovering
import Langlands.Global.AdelicCharacteristicRegionCompact
import Langlands.Global.AdelicGoodPositionIwasawaCompactProof
import Langlands.Global.AdelicSquareIntegrableInducedNormOne

/-! # The characteristic truncation estimate in relative rank zero -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus
  AdelicSiegelFactors ArthurTruncation Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "T" => fam.T
local notation "P" => fam.P fam.top
local notation "M" => fam.M fam.top
local notation "pG" => fam.p fam.top
local notation "jG" => fam.l fam.top ≫ fam.p fam.top
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "G₁" => normOneSubgroup F G
local notation "Γ" => rationalNormOneSubgroup F G
local notation "ΓM" => rationalNormOneSubgroup F M
local notation "QG" => NormOneRationalQuotient F G
local notation "QM" => NormOneRationalQuotient F M
local notation "dG" => normOneRationalQuotientHaarMeasure F G
local notation "dM" => normOneRationalQuotientHaarMeasure F M
local notation "QZ" => fam.positiveSplitComponent fam.top

omit [NumberField F] in
private theorem eq_top_of_empty_simpleRoots (hΔ : Δ = ∅) (J : Idx) : J = fam.top := by
  apply Subtype.ext
  change J.val = Δ
  refine le_antisymm J.property fun α hα => ?_
  have h : α ∈ (∅ : Set (characterLattice T)) := hΔ ▸ hα
  exact h.elim

omit [NumberField F] in
private theorem relativeSimpleRoots_top_eq_empty : fam.relativeSimpleRoots fam.top = ∅ := by
  classical
  ext α
  rw [relativeSimpleRoots, Finset.mem_filter, mem_simpleFinset]
  change (α ∈ Δ ∧ α ∉ Δ) ↔ _
  simp

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (fam.p fam.bot) K)

local instance : IsIso jG := fam.isIso_topLevi
local instance : IsClosedImmersion (pG).hom.hom.left := fam.isClosedImmersion_p fam.top

private theorem exists_truncationCompact_rankZero (hΔ : Δ = ∅) :
    ∃ (L : Subgroup (AdelicGroupPoints F G)), IsParabolicIwasawaCompact F G (fam.P fam.bot)
      (fam.p fam.bot) L ∧
      (∀ J, IsMaximalCompactSubgroup F (fam.M J)
        (L.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) ∧
      IsPositiveTorusCompatible F G T fam.i fam.ν T (𝟙 T) L := by
  have hBT : Geometry.Building.BruhatTitsAvailabilityStatement :=
    Geometry.Building.bruhatTitsAvailabilityReduction
      (Geometry.Building.groupAxiomsExistenceReduction
        Geometry.Building.rootValuationBuildingConstruction
        Geometry.Building.rootGroupActionAxiom Geometry.Building.iwahoriDecompositionAxiom
        Geometry.Building.integralModelAxioms)
  have hex : ∀ v : Place F, ∃ L : Subgroup (PlaceGroupPoints F G v),
      fam.IsStandardLeviCompact v L := by
    rintro (v | v)
    · exact InfinitePlaceGroupPoints.infinitePlaceStandardLeviCompact F G fam v
    · exact FinitePlaceGroupPoints.finitePlaceStandardLeviCompactReduction hBT F G fam v
  obtain ⟨L, hL, hLevi⟩ := fam.standardLeviCompactAssembly hex
  refine ⟨L, hL, hLevi, ?_⟩
  let e := emptyRootStandardLeviIso F G T fam.i fam.ν fam.connectedReductive fam.maximalSplit fam.generic hΔ
  let iL := standardLeviTorusFactor fam.i fam.ν ∅ (Standard.isRepresentedBy_leviHom fam.i fam.ν ∅)
  have he : e.hom = Standard.leviHom fam.i fam.ν ∅ :=
    emptyRootStandardLeviIso_hom F G T fam.i fam.ν fam.connectedReductive fam.maximalSplit fam.generic hΔ
  have hc : IsCentral iL := by
    apply isCentral_of_range_le_torusCentralizer (Standard.isRepresentedBy_leviHom fam.i fam.ν ∅).1
    rw [standardLeviTorusFactor_comp, (Standard.isRepresentedBy_leviHom fam.i fam.ν ∅).2,
      standardLevi_empty_eq_torusCentralizer_of_generic fam.i fam.ν fam.connectedReductive
        fam.maximalSplit fam.generic]
  have hi : IsCentral fam.i := by
    have hh : iL ≫ e.hom = fam.i := by
      rw [he]
      exact standardLeviTorusFactor_comp _ _ _ _
    rw [← hh]
    exact hc.comp_iso e
  intro k _ _ b
  have hmap : positiveMap F G T fam.i T (𝟙 T) b = positivePointMap F G T fam.i b := by
    change map F (T).toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ fam.i) b.val = _
    rw [show CommGroupScheme.groupHom (𝟙 T) = 𝟙 (T).toGrp from rfl, Category.id_comp]
    rfl
  rw [hmap]
  exact (positivePointMap_commute F G T fam.i hi b k).symm

private theorem characteristicRegion_rankZero
    (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅) (Standard.leviScheme fam.i fam.ν ∅))
    (hΔ : Δ = ∅) (T₀ : V T) (hcov : ∀ q : QG, ∃ Tp, q ∈ fam.truncationRegion hK C T₀ Tp)
    (Tp : V T) : fam.truncationRegion hK C T₀ Tp = Set.univ := by
  have hC (S S' : V T) :
      characteristicChamber fam.ν fam.connectedReductive fam.maximalSplit fam.coroots T₀ S =
      characteristicChamber fam.ν fam.connectedReductive fam.maximalSplit fam.coroots T₀ S' := by
    ext x
    simp only [characteristicChamber, Set.mem_ofPred_eq, mem_simpleFinset, hΔ,
      Set.notMem_empty, false_implies, implies_true, and_true]
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨S, hq⟩ := hcov q
  unfold truncationRegion characteristicRegion characteristicProduct at hq ⊢
  rwa [hC Tp S]

private theorem pairingOnNormOne_continuous (z : QZ) {f g : AdelicGroupPoints F G → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hfr : IsLeftInvariantUnder F G (rationalSubgroup F G) f)
    (hgr : IsLeftInvariantUnder F G (rationalSubgroup F G) g) :
    Continuous (fam.truncatedPairingIntegrand z f g) := by
  let b (m : G₁) := fam.centralTranslate z f m.val * starRingEnd ℂ (fam.centralTranslate z g m.val)
  have hbc : Continuous b := (hf.comp (continuous_subtype_val.mul_const _)).mul
    (continuous_star.comp (hg.comp (continuous_subtype_val.mul_const _)))
  have hInv : ∀ r ∈ Γ, ∀ m, b (r * m) = b m := by
    rintro _ ⟨q, rfl⟩ m
    change f (rational F G q * m.val * fam.centralPoint z) *
      starRingEnd ℂ (g (rational F G q * m.val * fam.centralPoint z)) = b m
    rw [mul_assoc, hfr _ ⟨q, rfl⟩, hgr _ ⟨q, rfl⟩]
    rfl
  apply (LeftCosetSpace.continuous_iff Γ).mpr
  exact hbc.congr (fun m => (LeftCosetSpace.out_mk_of_invariant Γ b hInv m).symm)

omit [IsAffineHom G.X.hom] in
private theorem continuous_mulStar {X : Type} [TopologicalSpace X] {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * starRingEnd ℂ (g x)) := hf.mul (continuous_star.comp hg)

set_option maxHeartbeats 1800000 in
private theorem topPairingTransport (hMcomp : CompactSpace QM) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (z : QZ) {f g : AdelicGroupPoints F G → ℂ},
      Continuous f → Continuous g →
      IsLeftInvariantUnder F G (rationalSubgroup F G) f →
      IsLeftInvariantUnder F G (rationalSubgroup F G) g →
      ∀ x : AdelicGroupPoints F P,
        (∀ y, f (map F P G pG x * y) = f y) →
        (∀ y, g (map F P G pG x * y) = g y) →
        let B := fam.truncatedPairingIntegrand z f g
        let fz := fam.centralTranslate z f
        let gz := fam.centralTranslate z g
        Integrable (fam.squareIntegrablePairingIntegrand K fam.top x fz gz)
          (fam.squareIntegrablePairingMeasure K hK.isCompact fam.top) ∧
        fam.normalizedPairing K hK.isCompact fam.top x fz gz =
          (c : ℂ) * ∫ q, B q ∂dG := by
  let e := asIso jG
  let eQ := normOneQuotientIso e
  obtain ⟨c, hc, hmap⟩ := normOneQuotientIsoHaar e
  refine ⟨c, hc, fun z f g hf hg hfr hgr x hxf hxg => ?_⟩
  let b (m : G₁) := fam.centralTranslate z f m.val * starRingEnd ℂ (fam.centralTranslate z g m.val)
  let B := fam.truncatedPairingIntegrand z f g
  let dK := compactHaarProbability F G K hK.isCompact
  let k₁ (k : K) : G₁ := ⟨k.val, compactSubgroup_le_normOneSubgroup F G K hK.isCompact k.property⟩
  let r (k : K) := LeftCosetSpace.rightTranslateHomeomorph Γ (k₁ k)
  let I := fam.squareIntegrablePairingIntegrand K fam.top x (fam.centralTranslate z f) (fam.centralTranslate z g)
  let h (k : K) (m : normOneSubgroup F M) := b (normOnePointsIso e m * k₁ k)
  have hInv : ∀ t ∈ Γ, ∀ m, b (t * m) = b m := by
    rintro _ ⟨q, rfl⟩ m
    change f (rational F G q * m.val * fam.centralPoint z) *
      starRingEnd ℂ (g (rational F G q * m.val * fam.centralPoint z)) = b m
    rw [mul_assoc, hfr _ ⟨q, rfl⟩, hgr _ ⟨q, rfl⟩]
    rfl
  have hIval (k : K) (q : QM) : I (k, q) = h k q.out := by
    let m := map F M G (jG) (q.out : normOneSubgroup F M).val
    let a := map F P G pG x
    let v := fam.centralPoint z
    change f ((a * m * k.val) * v) * starRingEnd ℂ (g ((a * m * k.val) * v)) =
      f ((m * k.val) * v) * starRingEnd ℂ (g ((m * k.val) * v))
    simp only [mul_assoc, a, hxf, hxg]
  have hCont : Continuous (fun z' : K × normOneSubgroup F M => h z'.1 z'.2) := by
    have hcK : Continuous k₁ := continuous_subtype_val.subtype_mk _
    have hb : Continuous b := continuous_mulStar
      (hf.comp (continuous_subtype_val.mul_const _)) (hg.comp (continuous_subtype_val.mul_const _))
    exact hb.comp (((normOnePointsIso e).continuous.comp continuous_snd).mul
      (hcK.comp continuous_fst))
  have hInvariant (k : K) (t : normOneSubgroup F M) (ht : t ∈ ΓM) (m : normOneSubgroup F M) :
      h k (t * m) = h k m := by
    dsimp only [h]
    rw [map_mul, mul_assoc]
    exact hInv _ ((normOnePointsIso_rational e t).mpr ht) _
  have hcI : Continuous I :=
    (LeftCosetSpace.continuous_out_of_invariant ΓM h hCont hInvariant).congr
      (fun w => (hIval w.1 w.2).symm)
  let : CompactSpace QM := hMcomp
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let : IsFiniteMeasure dM := by infer_instance
  have hI : Integrable I (dK.prod dM) :=
    hcI.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hI, ?_⟩
  have hSection (k : K) (q : QM) : I (k, q) = B (r k (eQ q)) := by
    have hh : r k (eQ q) = LeftCosetSpace.mk Γ (normOnePointsIso e q.out * k₁ k) := by
      change LeftCosetSpace.rightTranslate Γ (k₁ k) (normOneQuotientIso e q) = _
      conv_lhs => rw [← show LeftCosetSpace.mk ΓM q.out = q from Quotient.out_eq q]
      rw [normOneQuotientIso_mk, LeftCosetSpace.rightTranslate_mk]
    rw [hh, hIval]
    exact (LeftCosetSpace.out_mk_of_invariant Γ b hInv _).symm
  have hInner (k : K) : (∫ q, I (k, q) ∂dM) = (c : ℂ) * ∫ q, B q ∂dG := by
    simp_rw [hSection]
    rw [← integral_map_equiv eQ (fun q => B (r k q)), hmap, integral_smul_measure]
    have := normOneHaarRightInvariant F G fam.connectedReductive.smooth fam.connectedReductive.connectedSpace
    have hr : MeasurePreserving (r k) dG dG :=
      measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure F G (k₁ k)
    rw [hr.integral_comp (r k).measurableEmbedding B]
    rfl
  change (fam.halfModulus fam.top x ^ 2)⁻¹ * (∫ w, I w ∂(dK.prod dM)) = _
  rw [halfModulus, fam.halfModulusParameter_top_eq_zero, InducedInnerProductIntegrable.parameterPower_zero,
    one_pow, inv_one, one_mul, integral_prod _ hI]
  simp_rw [hInner]
  simp [B]

end StandardParabolicFamily

open StandardParabolicFamily

/-- The characteristic-to-regularized truncation estimate for groups with no
simple relative roots. The compact, covering factors and Haar scale are fixed before
the inducing and tested forms. -/
def EisensteinTemperedTruncationEstimateRankZeroStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G),
  simpleRelativeRoots fam.i fam.ν = ∅ →
  ∃ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p fam.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅))
    (T₀ : V fam.T) (vol : StandardIndex F G fam.i fam.ν → ℝ),
    IsMaximalCompactSubgroup F G K ∧
    (∀ J, IsMaximalCompactSubgroup F (fam.M J)
      (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) ∧
    IsPositiveTorusCompatible F G fam.T fam.i fam.ν fam.T (𝟙 fam.T) K ∧
    C.compactSubgroup = K ∧ ArthurTruncation.IsRationalCovering C ∧
    (∀ q : NormOneRationalQuotient F G, ∃ T, q ∈ fam.truncationRegion hK C T₀ T) ∧
    (∀ Q, 0 < vol Q) ∧
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho →
  ∀ (P : StandardIndex F G fam.i fam.ν) (Φ φ : AdelicGroupPoints F G → ℂ),
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p P) (fam.iU P) (fam.l P) φ →
  ∀ (_ : IsClosedImmersion (fam.p P).hom.hom.left)
    (hKP : IsIwasawaCompact (fam.p P) K)
    (r : ParabolicRootPresentation (fam.p P) (fam.l P) (fam.a P))
    (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
    (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    (hA : IsSplitTorus (fam.A P).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (E : ComplexCharacterParameter F (fam.P P) → AdelicGroupPoints F G → ℂ)
    (DE : Set (ComplexCharacterParameter F (fam.P P))),
    Set.range (imaginaryParameter F (fam.P P)) ⊆ DE →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKP.eisensteinSeries φ lam) →
  ∀ {n nT nZ : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (fam.P P))
    (ec : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P P))
    (eT : V fam.T ≃ₗ[ℝ] (Fin nT → ℝ))
    (eZ : RealCharacterDual F (fam.P fam.top) ≃ₗ[ℝ] (Fin nZ → ℝ)),
    let ix (x : Fin n → ℝ) : Fin n → ℂ := fun j => (x j : ℂ) * Complex.I
    (∀ x, ec (ix x) = imaginaryParameter F (fam.P P) (e x)) →
    ∃ (R : ℝ) (L : ∀ Q, fam.AffineExponentLabels P Q)
      (expansion : (Fin n → ℝ) → fam.positiveSplitComponent fam.top →
        ∀ Q, fam.UnitaryPairingExpansion Q)
      (ω : V fam.T → fam.positiveSplitComponent fam.top → (Fin n → ℂ) → ℂ)
      (Dω : V fam.T → fam.positiveSplitComponent fam.top → Set (Fin n → ℂ)),
    let generic := {x | ec (ix x) ∈ fam.genericParameterRegion P L}
    0 < R ∧ IsOpen generic ∧ Dense generic ∧
    (∀ x ∈ generic, ∀ Z,
      fam.IsWeakConstantTermPairingExpansion hsmooth hcalc rho hK Z
        (E (ec (ix x))) Φ (expansion x Z) ∧
      ∀ Q, (expansion x Z Q).IsLabelledBy (L Q) (ec (ix x))) ∧
    (∀ T, fam.IsRegularTruncationParameter R T → ∀ Z,
      IsOpen (Dω T Z) ∧ Set.range ix ⊆ Dω T Z ∧ DifferentiableOn ℂ (ω T Z) (Dω T Z) ∧
      ∀ x ∈ generic, ω T Z (ix x) = fam.regularizedPairing vol (expansion x Z) T) ∧
    ∀ δ : ℝ, 0 < δ → ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
      ∃ (B ε : ℝ) (k : ℕ), 0 < B ∧ 0 < ε ∧
      ∀ T, fam.IsRegularTruncationParameter R T →
      (∀ α ∈ simpleRelativeRoots fam.i fam.ν, δ * ‖eT T‖ ≤ eval fam.T α T) →
      ∀ Z, ∀ x ∈ Λ,
        IntegrableOn (fam.truncatedPairingIntegrand Z (E (ec (ix x))) Φ)
          (fam.truncationRegion hK C T₀ T) (normOneRationalQuotientHaarMeasure F G) ∧
        ‖fam.truncatedPairing hK C T₀ T Z (E (ec (ix x))) Φ - ω T Z (ix x)‖ ≤
          B * Real.exp (-ε * ‖eT T‖) *
            (1 + ‖eZ (characterLog F (fam.P fam.top) Z.val)‖ ^ k)

set_option maxHeartbeats 2800000 in
/-- In relative rank zero the characteristic region is the entire norm-one quotient.
The only normalized pairing is its full-group term and the zero-dimensional cone integral
recovers the same value. -/
theorem eisensteinTemperedTruncationEstimateRankZero :
    EisensteinTemperedTruncationEstimateRankZeroStatement := by
  classical
  intro F _ _ G _ _ _ fam hΔ
  let Idx := StandardIndex F G fam.i fam.ν
  have htop (J : Idx) : J = fam.top := fam.eq_top_of_empty_simpleRoots hΔ J
  let : IsIso (fam.p fam.top) := fam.isIso_topParabolic
  have hMcomp : CompactSpace (NormOneRationalQuotient F (fam.M fam.top)) := by
    rw [← htop fam.bot]
    exact fam.compactSpace_normOneRationalQuotient_bot
  obtain ⟨K, hL, hLevi, hpos⟩ := fam.exists_truncationCompact_rankZero hΔ
  let hK : IsIwasawaCompact (fam.p fam.bot) K := hL.isIwasawaCompact
  have hstd := fam.isIwasawaCompact_standardBot hK
  have hρ := fam.bijective_restrictToTorus_bot
  obtain ⟨C, T₀, hC, hcov, hcover⟩ := characteristicRegion_covering fam.connectedReductive
    fam.maximalSplit fam.coroots hstd hρ fam.generic
  have hfull (Tp : V fam.T) : fam.truncationRegion hK C T₀ Tp = Set.univ :=
    fam.characteristicRegion_rankZero hK C hΔ T₀ hcover Tp
  have hcompact : IsCompact (fam.truncationRegion hK C T₀ (0 : V fam.T)) :=
    characteristicRegion_compact fam.connectedReductive fam.maximalSplit fam.coroots hstd hρ
      fam.generic C hC hcov T₀ 0
  rw [hfull] at hcompact
  let : CompactSpace (NormOneRationalQuotient F G) := ⟨hcompact⟩
  obtain ⟨c, hc, hPair⟩ := fam.topPairingTransport hK hMcomp
  let vol : Idx → ℝ := fun _ => (c : ℝ)⁻¹
  refine ⟨K, hK, C, T₀, vol, hL.1, hLevi, hpos, hC, hcov, hcover,
    fun _ => inv_pos.mpr (by exact_mod_cast hc), ?_⟩
  intro N d rho hsmooth hcalc hrho J Φ φ hΦ hφ hp hKP r hi hW hr hA hT E DE hAxis hMer hSeries
    n nT nZ e ec eT eZ
  have hJ := htop J
  subst J
  dsimp only
  intro hCoord
  let P := fam.P fam.top
  let Q := NormOneRationalQuotient F G
  let QZ := fam.positiveSplitComponent fam.top
  let dG := normOneRationalQuotientHaarMeasure F G
  let ix (x : Fin n → ℝ) : Fin n → ℂ := fun j => (x j : ℂ) * Complex.I
  let ℒ (z : QZ) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun y => complexParameterPairing F P (ec y) (hKP.height (fam.centralPoint z))
      map_add' := fun y y' => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun b y => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  let I₀ (z : QZ) := ∫ q : Q, fam.truncatedPairingIntegrand z φ Φ q ∂dG
  let I (y : Fin n → ℂ) (z : QZ) := ∫ q : Q, fam.truncatedPairingIntegrand z (E (ec y)) Φ q ∂dG
  let ω (z : QZ) (y : Fin n → ℂ) : ℂ := Complex.exp (ℒ z y) * I₀ z
  obtain ⟨hE, hEweak⟩ := fam.topEisensteinContinuation hKP (φ := φ)
    (rho := rho) (hsmooth := hsmooth) (hcalc := hcalc) hL.1 hrho hφ r hA hT E hSeries
  obtain ⟨hφrat, hφcent⟩ := fam.topInducingInvariance hKP hφ
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  have hφaut : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho φ :=
    ⟨hφrat, hφ.1.2⟩
  have hEaut (lam : ComplexCharacterParameter F P) :
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho (E lam) := by
    rw [hE lam]
    exact hKP.isAutomorphicFunctionOn_parameterTwist_of_isIso hsmooth hcalc hL.1 rho hrho hφaut lam
  have hI (y : Fin n → ℂ) (z : QZ) : I y z = ω z y := by
    change (∫ q : Q, fam.truncatedPairingIntegrand z (E (ec y)) Φ q ∂dG) =
      Complex.exp (ℒ z y) * I₀ z
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by
      let m : normOneSubgroup F G := q.out
      let b := fam.centralPoint z
      have h1 : hKP.heightPower (ec y) m.val = 1 := by
        rw [hKP.heightPower_eq_parameterPower_of_isIso]
        exact InducedInnerProductIntegrable.parameterPower_of_characterLog_eq_zero _
          ((characterLog_eq_zero_iff F G _).mpr m.property)
      change E (ec y) (m.val * b) * starRingEnd ℂ (Φ (m.val * b)) =
        hKP.heightPower (ec y) b * (φ (m.val * b) * starRingEnd ℂ (Φ (m.val * b)))
      rw [hE, IsIwasawaCompact.parameterTwist, hKP.heightPower_mul_of_isIso, h1, one_mul]
      ac_rfl
  have hIint (y : Fin n → ℂ) (z : QZ) :
      Integrable (fam.truncatedPairingIntegrand z (E (ec y)) Φ) dG :=
    (fam.pairingOnNormOne_continuous z (hEaut _).2.1.1 hΦ.1.2.1.1 (hEaut _).1 hΦ.1.1)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L (J : Idx) : fam.AffineExponentLabels fam.top J := ⟨1, fun _ => 0, fun _ => 0⟩
  let expn (x : Fin n → ℝ) (z : QZ) (J : Idx) : fam.UnitaryPairingExpansion J :=
    { exponents := {0}
      coefficient := fun _ => MvPolynomial.C ((c : ℂ) * I (ix x) z)
      unitary := by intro lam h; rw [Finset.mem_singleton.mp h, map_zero] }
  let : IsEmpty (fam.relativeSimpleRoots fam.top : Type) :=
    ⟨fun α => Finset.notMem_empty _
      ((congrArg (fun s : Finset (characterLattice fam.T) => α.val ∈ s)
        fam.relativeSimpleRoots_top_eq_empty).mp α.property)⟩
  have hgen : {x | ec (ix x) ∈ fam.genericParameterRegion fam.top L} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x Q j
    obtain rfl := htop Q
    exact isEmptyElim
  have hReg (x : Fin n → ℝ) (z : QZ) (Tp : V fam.T) :
      fam.regularizedPairing vol (expn x z) Tp = ω z (ix x) := by
    rw [regularizedPairing, finsum_eq_single _ fam.top (fun J hJ => (hJ (htop J)).elim)]
    let A := (c : ℂ) * I (ix x) z
    have hCone : (expn x z fam.top).regularizedConeIntegral Tp = A := by
      simp only [expn, UnitaryPairingExpansion.regularizedConeIntegral, Finset.sum_singleton,
        Finset.sum_of_isEmpty, Complex.exp_zero, one_mul, polynomialShift, MvPolynomial.aeval_C]
      by_cases hA : A = 0
      · simp [negativeOrthantRegularizedIntegral, ← show A = (c : ℂ) * I (ix x) z from rfl, hA]
      · rw [show (c : ℂ) * I (ix x) z = A from rfl, negativeOrthantRegularizedIntegral,
          ← MvPolynomial.C_eq_algebraMap, MvPolynomial.support_C, ite_eq_right hA,
          Finset.sum_singleton, MvPolynomial.coeff_C, ite_eq_left rfl, Finset.prod_of_isEmpty,
          mul_one]
    rw [hCone, ← hI]
    have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    change (↑((c : ℝ)⁻¹) : ℂ) * ((c : ℂ) * I (ix x) z) = I (ix x) z
    rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hcℂ, one_mul]
  refine ⟨1, L, expn, fun _ => ω, fun _ _ => Set.univ, one_pos, ?_, ?_, ?_, ?_, ?_⟩
  · change IsOpen {x | ec (ix x) ∈ fam.genericParameterRegion fam.top L}
    rw [hgen]
    exact isOpen_univ
  · change Dense {x | ec (ix x) ∈ fam.genericParameterRegion fam.top L}
    rw [hgen]
    exact dense_univ
  · intro x hx z
    refine ⟨?_, ?_⟩
    · intro J
      obtain rfl := htop J
      let lam := ec (ix x)
      let H := fam.isIwasawaCompact_index hK fam.top
      have hWk : fam.IsWeakConstantTerm hsmooth Kinf rho fam.top (E lam) (E lam) := by
        change fam.IsWeakConstantTerm hsmooth Kinf rho fam.top (E (ec (ix x))) (E (ec (ix x)))
        rw [hCoord x]
        exact hEweak (e x)
      have hTw : H.parameterTwist φ lam = E lam := (hE lam).symm
      refine ⟨E lam, Φ, {lam}, fun _ => φ, hWk, fam.isWeakConstantTerm_top hΦ, ?_, ?_⟩
      · refine ⟨fun _ _ => hφ, ?_⟩
        rw [Finset.sum_singleton, hTw, sub_self]
        intro g hg a ha
        have hZero : fam.squareIntegrablePairingIntegrand K fam.top a g 0 = 0 := by
          funext w
          simp [squareIntegrablePairingIntegrand]
        rw [hZero]
        simp
      · intro a ha v hv
        have ha0 : characterLog F P a = 0 :=
          hv.trans (Finset.sum_of_isEmpty _)
        have haC := fam.topPositive_mem_canonical ha
        have hShiftE (g : AdelicGroupPoints F G) :
            E lam (map F P G (fam.p fam.top) a * g) = E lam g := by
          have hp1 : hKP.heightPower lam (map F P G (fam.p fam.top) a) = 1 := by
            rw [IsIwasawaCompact.heightPower, hKP.height_map, ha0, map_zero, Complex.exp_zero]
          rw [hE lam]
          change φ (map F P G (fam.p fam.top) a * g) *
            hKP.heightPower lam (map F P G (fam.p fam.top) a * g) = _
          rw [hφcent _ haC g, hKP.heightPower_mul_of_isIso, hp1, one_mul]
          rfl
        obtain ⟨ν, hν⟩ := hΦ.2.1
        have hShiftΦ (g : AdelicGroupPoints F G) :
            Φ (map F P G (fam.p fam.top) a * g) = Φ g := by
          rw [hν _ haC, InducedInnerProductIntegrable.parameterPower_of_characterLog_eq_zero]
          · exact one_mul _
          · rw [characterLog_map, ha0, map_zero]
        obtain ⟨hInt, hEq⟩ := hPair z (hEaut lam).2.1.1 hΦ.1.2.1.1 (hEaut lam).1 hΦ.1.1 a hShiftE hShiftΦ
        refine ⟨?_, ?_⟩
        · intro j hj
          obtain rfl := Finset.mem_singleton.mp hj
          change Integrable
            (fam.squareIntegrablePairingIntegrand K fam.top a
              (fam.centralTranslate z (H.parameterTwist φ lam)) (fam.centralTranslate z Φ)) _
          rw [hTw]
          exact hInt
        · rw [Finset.sum_singleton]
          change fam.normalizedPairing K hK.isCompact fam.top a
            (fam.centralTranslate z (H.parameterTwist φ lam)) (fam.centralTranslate z Φ) = _
          rw [hTw, hEq]
          change (c : ℂ) * I (ix x) z = _
          simp [expn, UnitaryPairingExpansion.eval]
    · intro J lam hlam
      exact ⟨0, by simpa [L, AffineExponentLabels.label, expn] using (Finset.mem_singleton.mp hlam).symm⟩
  · intro Tp _ z
    refine ⟨isOpen_univ, Set.subset_univ _, ?_, fun x _ => (hReg x z Tp).symm⟩
    exact (((LinearMap.toContinuousLinearMap (ℒ z)).differentiable.cexp).mul
      (differentiable_const _)).differentiableOn
  · intro δ hδ Λ hΛ
    refine ⟨1, 1, 0, one_pos, one_pos, fun Tp hTp hδTp z x hx => ?_⟩
    rw [hfull Tp]
    refine ⟨(hIint (ix x) z).integrableOn, ?_⟩
    rw [truncatedPairing, hfull Tp, Measure.restrict_univ]
    change ‖I (ix x) z - ω z (ix x)‖ ≤ _
    rw [hI (ix x) z, sub_self, norm_zero]
    positivity

end Langlands.Global
