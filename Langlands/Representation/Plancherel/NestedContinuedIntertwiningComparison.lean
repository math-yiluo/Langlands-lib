import Langlands.Representation.Plancherel.NestedStandardIntertwiningContinuation
import Langlands.Representation.Plancherel.StandardIntertwiningMeasure

/-! # Continued operators through a nested pair of parabolics -/

noncomputable section

set_option maxHeartbeats 3600000
set_option maxRecDepth 4096
set_option quotPrecheck false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.Aubert.General Langlands.Induction
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel.StandardIntertwining

open UnramifiedOperatorFamily

universe u uV

local notation "liftOperator(" E "," F "," J ")" => (F).symm.toLinearMap.comp ((J).comp (E).toLinearMap)

section IntegralNormalization

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (A : SmoothRep.{0, u, uV} ℂ M)
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]

local notation "V" => ((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A)
local notation "W" => ((DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A)

/-- A quotient-measure rescaling changes the representing map by the same scalar. -/
theorem RepresentsStandardIntegral.smul_nnreal {muG : Measure (QuotientSpace (U := U₀) U₁)}
    {J : V →ₗ[ℂ] W} (hJ : RepresentsStandardIntegral h₀ hU₀ h₁ hU₁ A muG J) (c : ℝ≥0) :
    RepresentsStandardIntegral h₀ hU₀ h₁ hU₁ A (c • muG) ((c : ℂ) • J) :=
  fun f => HasIntegral.smul_measure_nnreal h₀ hU₀ U₁ A muG (hJ f) c

/-- Two everywhere-defined representatives of the same weak integral agree. -/
theorem RepresentsStandardIntegral.eq (hM : IsClosed (M : Set G))
    {muG : Measure (QuotientSpace (U := U₀) U₁)} {J J' : V →ₗ[ℂ] W}
    (hJ : RepresentsStandardIntegral h₀ hU₀ h₁ hU₁ A muG J)
    (hJ' : RepresentsStandardIntegral h₀ hU₀ h₁ hU₁ A muG J') : J = J' := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) (J f) g =
    eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) (J' f) g
  exact (hJ f g).unique (compactCofinal hM) A.property (hJ' f g)

end IntegralNormalization

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ Q L N : Subgroup G} [LocallyCompactSpace L]
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hQ : IsSemidirectDecomposition Q L N) (hLc : IsClosed (L : Set G)) (hML : M ≤ L)
  (h₀i : IsSemidirectDecomposition (P₀.subgroupOf L) (M.subgroupOf L) (U₀.subgroupOf L))
  (h₁i : IsSemidirectDecomposition (P₁.subgroupOf L) (M.subgroupOf L) (U₁.subgroupOf L))
  (hN : IsClosed (N : Set G)) (hP₀Q : P₀ ≤ Q) (hP₁Q : P₁ ≤ Q)
  (hNU₀ : N ≤ U₀) (hNU₁ : N ≤ U₁) (hπ : Continuous hQ.projection)
  (hδ₀ : IsUnimodularModulus U₀ hU₀) (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (hδN : IsUnimodularModulus N hN)
  (hhalf₀ : NestedInduction.HalfCharacterProduct h₀ hQ hLc h₀i hU₀ hN)
  (hhalf₁ : NestedInduction.HalfCharacterProduct h₁ hQ hLc h₁i hU₁ hN)
  (A : SmoothRep.{0, u, uV} ℂ M)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [TopologicalSpace (rationalPoints H)]
  (hp : Continuous (rationalValuationImageProjection H)) (hH : IsConnectedReductive H)
  (e : rationalPoints H ≃ₜ* M)
  (hη : ∀ i, Continuous (rationalNormCharacters H i).toMul)

set_option hygiene false in
local notation "η" => fun i => (rationalNormCharacters H i).toMul
set_option hygiene false in
local notation "X" => unramifiedCharacters η

set_option hygiene false in
local notation "hU₀i" => hU₀.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "hU₁i" => hU₁.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "Ki" => K.comap L.subtype continuous_subtype_val
set_option hygiene false in
local notation "eM" => subgroupOfContinuousEquiv hML
set_option hygiene false in
local notation "Ai" => SmoothRep.pullback (eM) A
set_option hygiene false in
local notation "ηM" => (fun i => (η i).comp e.symm.toMonoidHom)
set_option hygiene false in
local notation "hηM" => (fun i => (hη i).comp e.symm.continuous)
set_option hygiene false in
local notation "ηi" => (fun i => (ηM i).comp (eM).toMonoidHom)
set_option hygiene false in
local notation "χM" => unramifiedCharactersHomeomorph e η
set_option hygiene false in
local notation "χi" => unramifiedCharactersHomeomorph (eM).symm (ηM)

variable (hδ₀i : IsUnimodularModulus (U₀.subgroupOf L) hU₀i)
  (hδ₁i : IsUnimodularModulus (U₁.subgroupOf L) hU₁i)
  (hP₀iKi : ∀ l : L, ∃ p : P₀.subgroupOf L, ∃ k : Ki, l = (p : L) * (k : L))
  (hP₁iKi : ∀ l : L, ∃ p : P₁.subgroupOf L, ∃ k : Ki, l = (p : L) * (k : L))
  (hr₀i : Continuous h₀i.projection) (hr₁i : Continuous h₁i.projection)

set_option hygiene false in
local notation "hP₀i" => hP₀.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "hP₁i" => hP₁.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "hKi" => hLc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
set_option quotPrecheck false in
set_option hygiene false in
local notation "Aχ" z => A.twist (χM z).val.toMonoidHom (unramifiedCharacter_isOpen_ker (ηM) (χM z))
set_option hygiene false in
local notation "E₀" z => unramifiedLeviInductionCompactEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  (ηM) (hηM) hr₀ (χM z) A
set_option hygiene false in
local notation "E₁" z => unramifiedLeviInductionCompactEquiv h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  (ηM) (hηM) hr₁ (χM z) A
set_option quotPrecheck false in
set_option hygiene false in
local notation "F₀" z => unramifiedLeviInductionCompactEquiv h₀i hU₀i hδ₀i Ki hP₀i hKi hP₀iKi
  (ηi) (fun i => (hηM i).comp (eM).continuous) hr₀i (χi (χM z)) (Ai)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F₁" z => unramifiedLeviInductionCompactEquiv h₁i hU₁i hδ₁i Ki hP₁i hKi hP₁iKi
  (ηi) (fun i => (hηM i).comp (eM).continuous) hr₁i (χi (χM z)) (Ai)
set_option hygiene false in
local notation "R₀" z => compactStagesRestriction h₀ hQ hLc hML h₀i hU₀ hN hP₀Q hNU₀ hπ
  hδ₀ hδN hhalf₀ A K hK hP₀ hP₀K hr₀ (ηM) (hηM) hδ₀i hP₀iKi hr₀i z
set_option hygiene false in
local notation "R₁" z => compactStagesRestriction h₁ hQ hLc hML h₁i hU₁ hN hP₁Q hNU₁ hπ
  hδ₁ hδN hhalf₁ A K hK hP₁ hP₁K hr₁ (ηM) (hηM) hδ₁i hP₁iKi hr₁i z
set_option hygiene false in
local notation "C₀" => CompactInductionPicture h₀ K A
set_option hygiene false in
local notation "C₁" => CompactInductionPicture h₁ K A
set_option hygiene false in
local notation "C₀i" => CompactInductionPicture h₀i Ki (Ai)
set_option hygiene false in
local notation "C₁i" => CompactInductionPicture h₁i Ki (Ai)

local instance nestedComparisonAmbientMeasurable : MeasurableSpace (QuotientSpace (U := U₀) U₁) :=
  borel _
local instance nestedComparisonInnerMeasurable :
    MeasurableSpace (QuotientSpace (U := U₀.subgroupOf L) (U₁.subgroupOf L)) := borel _

variable (muG : Measure (QuotientSpace (U := U₀) U₁))

set_option hygiene false in
local notation "μi" => nestedQuotientMeasure hQ (h₁.unipotent_le.trans hP₁Q) hNU₀ hNU₁ hπ muG

variable (μL : Measure (QuotientSpace (U := U₀.subgroupOf L) (U₁.subgroupOf L)))

include hp hH in
set_option backward.isDefEq.respectTransparency.types false in
/-- The rational compact continuation commutes with the fixed lower
restriction. The lower quotient has a separately specified measure and
the square includes the pushforward's scalar. -/
theorem nestedContinuedOperators_scaled_square
    {Ω Λ : Set X} (J : Ω → C₀ →ₗ[ℂ] C₁) (J' : Λ → C₀i →ₗ[ℂ] C₁i)
    (p : RationalOperatorContinuationData Ω J) (q : RationalOperatorContinuationData Λ J')
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hsub : Ω ⊆ Λ)
    (hM : IsClosed (M : Set G)) (hU₁c : Jacquet.Localization.IsLimitOfCompactSubgroups U₁)
    (hJ : ∀ z : Ω, RepresentsStandardIntegral h₀ hU₀ h₁ hU₁ (Aχ z.val) muG
      (liftOperator(E₀ z.val, E₁ z.val, J z)))
    (hJ' : ∀ z : Ω, RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i
      (SmoothRep.pullback (eM) (Aχ z.val)) μL
      (liftOperator(F₀ z.val, F₁ z.val, J' ⟨z.val, hsub z.property⟩)))
    (c : ℝ≥0) (hscale : μi = c • μL) (z : ↥(p.regularRegion ∩ q.regularRegion)) :
    (q.continuedOperator ⟨z.val, z.property.2⟩).comp ((c : ℂ) • (R₀ 1)) =
      (R₁ 1).comp (p.continuedOperator ⟨z.val, z.property.1⟩) := by
  obtain ⟨Ji, _, _, hJi, hsquare⟩ := hasNestedCompactContinuation h₀ hU₀ h₁ hU₁ hQ hLc hML h₀i h₁i
    hN hP₀Q hP₁Q hNU₀ hNU₁ hπ hδ₀ hδ₁ hδN hhalf₀ hhalf₁ A K hK hP₀ hP₁ hP₀K hP₁K
    hr₀ hr₁ η hη e hδ₀i hδ₁i hP₀iKi hP₁iKi hr₀i hr₁i muG J p hM hU₁c hJ
  refine rationalOperatorContinuationData_natural H hp hH p q ((c : ℂ) • (R₀ 1)) (R₁ 1)
    hΩ hne subset_rfl hsub (fun w hw => ?_) z
  let wz : Ω := ⟨w, hw⟩
  let σ := SmoothRep.pullback (eM) (Aχ w)
  have hI : RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i σ μi
      (liftOperator(F₀ w, F₁ w, (c : ℂ) • J' ⟨w, hsub hw⟩)) := by
    rw [hscale]
    change RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i σ (c • μL)
      (liftOperator(F₀ w, F₁ w, (c : ℂ) • J' ⟨w, hsub hw⟩))
    have ht := RepresentsStandardIntegral.smul_nnreal h₀i hU₀i h₁i hU₁i σ (hJ' wz) c
    rw [LinearMap.smul_comp, LinearMap.comp_smul]
    exact ht
  have hEq := RepresentsStandardIntegral.eq h₀i hU₀i h₁i hU₁i σ
    (hM.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))) (hJi wz) hI
  have hcomp : Ji wz = (c : ℂ) • J' ⟨w, hsub hw⟩ := by
    apply LinearMap.ext
    intro f
    apply (F₁ w).symm.injective
    have ht := LinearMap.congr_fun hEq ((F₀ w).symm f)
    change (F₁ w).symm (Ji wz ((F₀ w) ((F₀ w).symm f))) =
      (F₁ w).symm (((c : ℂ) • J' ⟨w, hsub hw⟩) ((F₀ w) ((F₀ w).symm f))) at ht
    rwa [LinearEquiv.apply_symm_apply] at ht
  change (J' ⟨w, hsub hw⟩).comp ((c : ℂ) • (R₀ 1)) = (R₁ 1).comp (J wz)
  rw [← hsquare wz, hcomp, LinearMap.smul_comp, LinearMap.comp_smul]

end Langlands.Plancherel.StandardIntertwining
