import Langlands.Representation.Plancherel.NestedStandardIntertwiningCompact
import Langlands.Representation.Plancherel.NestedStandardIntertwiningOperator
import Langlands.Representation.Plancherel.ContinuedIntertwiningNaturality

/-! # Rational continuation under normalized restriction to an intermediate Levi -/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Induction
open scoped NNReal

namespace Langlands.Plancherel.StandardIntertwining

open UnramifiedOperatorFamily

universe u uV uH uI

set_option quotPrecheck false in
local notation "liftOperator(" E "," F "," J ")" => (F).symm.toLinearMap.comp ((J).comp (E).toLinearMap)

section Conjugation

variable {X Y Xi Yi C D Ci Di : Type*}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Xi] [Module ℂ Xi] [AddCommGroup Yi] [Module ℂ Yi]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup Ci] [Module ℂ Ci] [AddCommGroup Di] [Module ℂ Di]
  (E : X ≃ₗ[ℂ] C) (F : Y ≃ₗ[ℂ] D) (Ei : Xi ≃ₗ[ℂ] Ci) (Fi : Yi ≃ₗ[ℂ] Di)
  (r : X →ₗ[ℂ] Xi) (t : Y →ₗ[ℂ] Yi) (R : C →ₗ[ℂ] Ci) (T : D →ₗ[ℂ] Di)
  (hR : ∀ x, R (E x) = Ei (r x)) (hT : ∀ y, T (F y) = Fi (t y))
  (J : C →ₗ[ℂ] D)

include hR hT in
private theorem lift_comp (S : Ci →ₗ[ℂ] C) (hS : R.comp S = LinearMap.id) :
    ∃ Si : Xi →ₗ[ℂ] X, r.comp Si = LinearMap.id ∧
      liftOperator(Ei, Fi, T.comp (J.comp S)) = t.comp ((liftOperator(E, F, J)).comp Si) := by
  let Si := E.symm.toLinearMap.comp (S.comp Ei.toLinearMap)
  refine ⟨Si, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply Ei.injective
    change Ei (r (E.symm (S (Ei x)))) = Ei x
    rw [← hR, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun hS (Ei x)
  · apply LinearMap.ext
    intro x
    apply Fi.injective
    change Fi (Fi.symm (T (J (S (Ei x))))) = Fi (t (F.symm (J (E (E.symm (S (Ei x)))))))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← hT,
      LinearEquiv.apply_symm_apply]

include hR hT in
private theorem compact_square (Ji : Ci →ₗ[ℂ] Di)
    (h : (liftOperator(Ei, Fi, Ji)).comp r = t.comp (liftOperator(E, F, J))) :
    Ji.comp R = T.comp J := by
  apply LinearMap.ext
  intro f
  have he := congrArg Fi (LinearMap.congr_fun h (E.symm f))
  change Fi (Fi.symm (Ji (Ei (r (E.symm f))))) =
    Fi (t (F.symm (J (E (E.symm f))))) at he
  rw [LinearEquiv.apply_symm_apply, ← hR, ← hT, LinearEquiv.apply_symm_apply] at he
  simpa only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply] using he

end Conjugation

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
  {H : Type uH} [Group H] [TopologicalSpace H] {I : Type uI}
  (η : I → (H →* ℝ≥0ˣ)) (hη : ∀ i, Continuous (η i)) (e : H ≃ₜ* M)

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

local notation "hP₀i" => hP₀.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
local notation "hP₁i" => hP₁.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
local notation "hKi" => hLc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
set_option quotPrecheck false in
local notation "Aχ" z => A.twist (χM z).val.toMonoidHom (unramifiedCharacter_isOpen_ker (ηM) (χM z))
local notation "E₀" z => unramifiedLeviInductionCompactEquiv h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  (ηM) (hηM) hr₀ (χM z) A
local notation "E₁" z => unramifiedLeviInductionCompactEquiv h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  (ηM) (hηM) hr₁ (χM z) A
set_option quotPrecheck false in
local notation "F₀" z => unramifiedLeviInductionCompactEquiv h₀i hU₀i hδ₀i Ki hP₀i hKi hP₀iKi
  (ηi) (fun i => (hηM i).comp (eM).continuous) hr₀i (χi (χM z)) (Ai)
set_option quotPrecheck false in
local notation "F₁" z => unramifiedLeviInductionCompactEquiv h₁i hU₁i hδ₁i Ki hP₁i hKi hP₁iKi
  (ηi) (fun i => (hηM i).comp (eM).continuous) hr₁i (χi (χM z)) (Ai)
local notation "r₀" z => nestedStagesRestriction h₀ hQ hLc hML h₀i hU₀ hN hP₀Q hNU₀ hπ
  hδ₀ hδN hhalf₀ (Aχ z) hδ₀i 1
local notation "r₁" z => nestedStagesRestriction h₁ hQ hLc hML h₁i hU₁ hN hP₁Q hNU₁ hπ
  hδ₁ hδN hhalf₁ (Aχ z) hδ₁i 1
local notation "R₀" z => compactStagesRestriction h₀ hQ hLc hML h₀i hU₀ hN hP₀Q hNU₀ hπ
  hδ₀ hδN hhalf₀ A K hK hP₀ hP₀K hr₀ (ηM) (hηM) hδ₀i hP₀iKi hr₀i z
local notation "R₁" z => compactStagesRestriction h₁ hQ hLc hML h₁i hU₁ hN hP₁Q hNU₁ hπ
  hδ₁ hδN hhalf₁ A K hK hP₁ hP₁K hr₁ (ηM) (hηM) hδ₁i hP₁iKi hr₁i z
local notation "C₀" => CompactInductionPicture h₀ K A
local notation "C₁" => CompactInductionPicture h₁ K A
local notation "C₀i" => CompactInductionPicture h₀i Ki (Ai)
local notation "C₁i" => CompactInductionPicture h₁i Ki (Ai)

local instance nestedContinuationAmbientMeasurable : MeasurableSpace (QuotientSpace (U := U₀) U₁) :=
  borel _
local instance nestedContinuationInnerMeasurable :
    MeasurableSpace (QuotientSpace (U := U₀.subgroupOf L) (U₁.subgroupOf L)) := borel _

variable (μ : Measure (QuotientSpace (U := U₀) U₁))

local notation "μi" => nestedQuotientMeasure hQ (h₁.unipotent_le.trans hP₁Q) hNU₀ hNU₁ hπ μ

/-- A compact continuation descends to the actual weak standard integral on
an intermediate Levi, with unchanged denominator and a fixed restriction square. -/
def HasNestedCompactContinuation {Ω : Set (unramifiedCharacters η)}
    (J : Ω → C₀ →ₗ[ℂ] C₁) (p : RationalOperatorContinuationData Ω J) : Prop :=
  ∃ (Ji : Ω → C₀i →ₗ[ℂ] C₁i) (pi : RationalOperatorContinuationData Ω Ji),
    pi.denominator = p.denominator ∧
    (∀ z : Ω, RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i
      (SmoothRep.pullback (eM) (Aχ z.val)) (μi) (liftOperator(F₀ z.val, F₁ z.val, Ji z))) ∧
    ∀ z : Ω, (Ji z).comp (R₀ 1) = (R₁ 1).comp (J z)

set_option maxHeartbeats 600000 in
/-- The linear section is chosen once on the compact carriers. Its lift
at each parameter gives the exact inner weak-integral operator. -/
theorem hasNestedCompactContinuation {Ω : Set (unramifiedCharacters η)}
    (J : Ω → C₀ →ₗ[ℂ] C₁) (p : RationalOperatorContinuationData Ω J)
    (hM : IsClosed (M : Set G)) (hU₁c : Jacquet.Localization.IsLimitOfCompactSubgroups U₁)
    (hJ : ∀ z : Ω, RepresentsStandardIntegral h₀ hU₀ h₁ hU₁ (Aχ z.val) μ
      (liftOperator(E₀ z.val, E₁ z.val, J z))) :
    HasNestedCompactContinuation h₀ hU₀ h₁ hU₁ hQ hLc hML h₀i h₁i hN hP₀Q hP₁Q
      hNU₀ hNU₁ hπ hδ₀ hδ₁ hδN hhalf₀ hhalf₁ A K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁
      η hη e hδ₀i hδ₁i hP₀iKi hP₁iKi hr₀i hr₁i μ J p := by
  obtain ⟨S, hS⟩ := exists_compactStagesRestriction_rightInverse h₀ hQ hLc hML h₀i hU₀ hN
    hP₀Q hNU₀ hπ hδ₀ hδN hhalf₀ A K hK hP₀ hP₀K hr₀ (ηM) (hηM) hδ₀i hP₀iKi hr₀i
  let Ji : Ω → C₀i →ₗ[ℂ] C₁i := fun z => (R₁ 1).comp ((J z).comp S)
  refine ⟨Ji, p.map S (R₁ 1), rfl, ?_⟩
  have hconj₀ (z : Ω) (f : UnramifiedLeviInduction h₀ hU₀ (ηM) (χM z.val) A) :
      (R₀ 1) ((E₀ z.val) f) = (F₀ z.val) ((r₀ z.val) f) := by
    have hR := compactStagesRestriction_independent h₀ hQ hLc hML h₀i hU₀ hN hP₀Q hNU₀ hπ
      hδ₀ hδN hhalf₀ A K hK hP₀ hP₀K hr₀ (ηM) (hηM) hδ₀i hP₀iKi hr₀i 1 (χM z.val)
    exact (LinearMap.congr_fun hR ((E₀ z.val) f)).trans
      (congrArg (fun x => (F₀ z.val) ((r₀ z.val) x)) ((E₀ z.val).symm_apply_apply f))
  have hconj₁ (z : Ω) (f : UnramifiedLeviInduction h₁ hU₁ (ηM) (χM z.val) A) :
      (R₁ 1) ((E₁ z.val) f) = (F₁ z.val) ((r₁ z.val) f) := by
    have hR := compactStagesRestriction_independent h₁ hQ hLc hML h₁i hU₁ hN hP₁Q hNU₁ hπ
      hδ₁ hδN hhalf₁ A K hK hP₁ hP₁K hr₁ (ηM) (hηM) hδ₁i hP₁iKi hr₁i 1 (χM z.val)
    exact (LinearMap.congr_fun hR ((E₁ z.val) f)).trans
      (congrArg (fun x => (F₁ z.val) ((r₁ z.val) x)) ((E₁ z.val).symm_apply_apply f))
  have hc := outerHalfCharacter_one_on_innerTargetRadical hQ hN (h₁.unipotent_le.trans hP₁Q) hU₁c
  have hinner (z : Ω) : RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i
      (SmoothRep.pullback (eM) (Aχ z.val)) (μi) (liftOperator(F₀ z.val, F₁ z.val, Ji z)) := by
    obtain ⟨Si, hSi, he⟩ := lift_comp (E₀ z.val) (E₁ z.val) (F₀ z.val) (F₁ z.val)
      (r₀ z.val) (r₁ z.val) (R₀ 1) (R₁ 1) (hconj₀ z) (hconj₁ z) (J z) S (hS 1)
    have hinner := RepresentsStandardIntegral.nested_comp h₀ hU₀ h₁ hU₁ h₀i h₁i
      hML hQ (h₁.unipotent_le.trans hP₁Q) hNU₀ hNU₁ hπ (Aχ z.val) μ _ hc (r₀ z.val) (r₁ z.val)
      (fun f => nestedStagesRestriction_formula h₀ hQ hLc hML h₀i hU₀ hN hP₀Q hNU₀ hπ
        hδ₀ hδN hhalf₀ (Aχ z.val) hδ₀i f 1)
      (fun f => nestedStagesRestriction_formula h₁ hQ hLc hML h₁i hU₁ hN hP₁Q hNU₁ hπ
        hδ₁ hδN hhalf₁ (Aχ z.val) hδ₁i f 1)
      (liftOperator(E₀ z.val, E₁ z.val, J z)) (hJ z) Si hSi
    exact (congrArg (RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i
      (SmoothRep.pullback (eM) (Aχ z.val)) (μi)) he).mpr hinner
  refine ⟨hinner, fun z => ?_⟩
  have hsq := RepresentsStandardIntegral.nested_square h₀ hU₀ h₁ hU₁ h₀i h₁i
    hML hQ (h₁.unipotent_le.trans hP₁Q) hNU₀ hNU₁ hπ (Aχ z.val) μ _ hc (r₀ z.val) (r₁ z.val)
    (fun f => nestedStagesRestriction_formula h₀ hQ hLc hML h₀i hU₀ hN hP₀Q hNU₀ hπ
      hδ₀ hδN hhalf₀ (Aχ z.val) hδ₀i f 1)
    (fun f => nestedStagesRestriction_formula h₁ hQ hLc hML h₁i hU₁ hN hP₁Q hNU₁ hπ
      hδ₁ hδN hhalf₁ (Aχ z.val) hδ₁i f 1)
    (liftOperator(E₀ z.val, E₁ z.val, J z)) (hJ z) hM
    (liftOperator(F₀ z.val, F₁ z.val, Ji z)) (hinner z)
  exact compact_square (E₀ z.val) (E₁ z.val) (F₀ z.val) (F₁ z.val)
    (r₀ z.val) (r₁ z.val) (R₀ 1) (R₁ 1) (hconj₀ z) (hconj₁ z) (J z) (Ji z) hsq

end Langlands.Plancherel.StandardIntertwining
