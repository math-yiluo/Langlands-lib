import Langlands.Geometry.Building.KPTorusCharacterFiltration
import Langlands.Geometry.Building.KPLocalNormIndependence
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.LocalField.AlgebraicExtensionValuation

/-! # A common geometric-character filtration of all unramified-field tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalField
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section Logarithm

variable {k : Type u} [Field k] (v : Valuation k ℝ≥0)
  (c : ℝ) (hc : 0 < c) (G : GroupScheme (Spec (CommRingCat.of k)))

/-- At zero depth, logarithmic character congruence is the existing
multiplicative character-valuation kernel. -/
theorem characterCongruence_log_zero :
    characterCongruence (logAdditiveValuation v c hc) G 0 =
      characterValuationKernel v G := by
  ext g
  simp only [mem_characterCongruence_zero, mem_characterValuationKernel,
    logAdditiveValuation_apply, negativeLogValue_eq_zero_iff hc]

end Logarithm

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "K" => UnramifiedClosure F
local notation "Ω" => SeparableClosure F

/-- Positive geometric-character conditions in one fixed separable closure,
with the additive valuation normalized by the original local-field order. -/
def localGeometricCharacterCongruence
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (r : ℝ≥0) :
    Subgroup (rationalPoints T.toGrp) :=
  extendedCharacterCongruence K Ω (algebraicExtensionAddValuation F Ω) T.toGrp r

theorem localGeometricCharacterCongruence_antitone
    (T : CommGroupScheme (Spec (CommRingCat.of K))) :
    Antitone (localGeometricCharacterCongruence F T) :=
  extendedCharacterCongruence_antitone K Ω _ T.toGrp

/-- Even the geometric zero-depth conditions force every original character
to have multiplicative value one. -/
theorem localGeometricCharacterCongruence_le_characterValuationKernel
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (r : ℝ≥0) :
    localGeometricCharacterCongruence F T r ≤
      characterValuationKernel (fixedFieldValuation F) T.toGrp := by
  apply le_trans (localGeometricCharacterCongruence_antitone F T
    (zero_le : (0 : ℝ≥0) ≤ r))
  change (characterCongruence (algebraicExtensionAddValuation F Ω)
    (baseChanged K Ω T.toGrp) 0).comap (rationalExtend K Ω T.toGrp) ≤ _
  rw [algebraicExtensionAddValuation]
  change (characterCongruence
    (logAdditiveValuation (sepClosureValuation F) (localLogScale F) (localLogScale_pos F))
    (baseChanged K Ω T.toGrp) 0).comap (rationalExtend K Ω T.toGrp) ≤ _
  rw [characterCongruence_log_zero]
  exact comap_characterValuationKernel_le (fixedFieldValuation F) (sepClosureValuation F) _

variable (E : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) E] [IsGalois (UnramifiedClosure F) E]
  (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffine T.X.left]

/-- The actual norm Iwahori at zero, intersected at positive depths with
characters tested in the common separable closure. -/
def localTorusFiltrationAtSplitting (r : ℝ≥0) : Subgroup (rationalPoints T.toGrp) :=
  if r = 0 then torusNormIwahori K E (intermediateValuation F E) T else
    torusNormIwahori K E (intermediateValuation F E) T ⊓
      localGeometricCharacterCongruence F T r

@[simp] theorem localTorusFiltrationAtSplitting_zero :
    localTorusFiltrationAtSplitting F E T 0 =
      torusNormIwahori K E (intermediateValuation F E) T := by
  simp [localTorusFiltrationAtSplitting]

theorem localTorusFiltrationAtSplitting_antitone :
    Antitone (localTorusFiltrationAtSplitting F E T) := by
  intro r s hrs
  by_cases hr : r = 0
  · subst r
    rw [localTorusFiltrationAtSplitting_zero]
    by_cases hs : s = 0
    · simp only [hs, localTorusFiltrationAtSplitting_zero, le_refl]
    · simp only [localTorusFiltrationAtSplitting, ite_eq_right hs]
      exact inf_le_left
  · have hs : s ≠ 0 := fun hs => hr
      (le_antisymm (hs ▸ hrs) (zero_le : (0 : ℝ≥0) ≤ r))
    simp only [localTorusFiltrationAtSplitting, ite_eq_right hr, ite_eq_right hs]
    exact inf_le_inf_left _ (localGeometricCharacterCongruence_antitone F T hrs)

theorem iInf_localTorusFiltrationAtSplitting_eq_bot
    (hE : IsSplitTorus (baseChanged K E T.toGrp)) :
    ⨅ r : ℝ≥0, localTorusFiltrationAtSplitting F E T r = ⊥ := by
  have hΩ : IsSplitTorus (baseChanged K Ω T.toGrp) :=
    hE.baseChange_fieldTower K E Ω T.toGrp
  apply le_antisymm _ bot_le
  rw [← iInf_extendedCharacterCongruence_eq_bot K Ω
    (algebraicExtensionAddValuation F Ω) T hΩ]
  intro t ht
  simp only [Subgroup.mem_iInf] at ht ⊢
  intro r
  have hr : r + 1 ≠ 0 := ne_of_gt (by positivity)
  have h := ht (r + 1)
  simp only [localTorusFiltrationAtSplitting, ite_eq_right hr, Subgroup.mem_inf] at h
  exact localGeometricCharacterCongruence_antitone F T
    (le_add_of_nonneg_right zero_le) h.2

/-- The whole family is independent of the finite Galois splitting field:
only its zero subgroup uses that choice. -/
theorem localTorusFiltrationAtSplitting_eq
    (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    (hE : IsSplitTorus (baseChanged K E T.toGrp))
    (hM : IsSplitTorus (baseChanged K M T.toGrp)) :
    localTorusFiltrationAtSplitting F E T = localTorusFiltrationAtSplitting F M T := by
  funext r
  simp only [localTorusFiltrationAtSplitting,
    torusNormIwahori_eq_of_splitting_fields F E M T hE hM]

/-- Norm-image naturality passes to different finite Galois splitting fields
by comparing both choices with their compositum. -/
theorem map_localTorusNormIwahori_le
    (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    {U : CommGroupScheme (Spec (CommRingCat.of K))} [IsAffine U.X.left]
    (hE : IsSplitTorus (baseChanged K E T.toGrp))
    (hM : IsSplitTorus (baseChanged K M U.toGrp)) (f : T ⟶ U) :
    (torusNormIwahori K E (intermediateValuation F E) T).map
      (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
        torusNormIwahori K M (intermediateValuation F M) U := by
  let N := E ⊔ M
  have : FiniteDimensional K N := IntermediateField.finiteDimensional_sup E M
  have : IsGalois K N := inferInstance
  have hEN := torusNormIwahori_eq_of_le F E N T le_sup_left hE
  have hMN := torusNormIwahori_eq_of_le F M N U le_sup_right hM
  calc
    (torusNormIwahori K E (intermediateValuation F E) T).map
        (rationalPoints.map (CommGroupScheme.groupHom f)) =
      (torusNormIwahori K N (intermediateValuation F N) T).map
        (rationalPoints.map (CommGroupScheme.groupHom f)) :=
      congrArg (fun H : Subgroup (rationalPoints T.toGrp) =>
        H.map (rationalPoints.map (CommGroupScheme.groupHom f))) hEN.symm
    _ ≤ torusNormIwahori K N (intermediateValuation F N) U :=
      map_torusNormIwahori_le K N (intermediateValuation F N) f
    _ = torusNormIwahori K M (intermediateValuation F M) U := hMN

set_option maxHeartbeats 800000 in
/-- Actual morphisms preserve the family even when its source and target
are presented with different splitting fields. -/
theorem map_localTorusFiltrationAtSplitting_le
    (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    {U : CommGroupScheme (Spec (CommRingCat.of K))} [IsAffine U.X.left]
    (hE : IsSplitTorus (baseChanged K E T.toGrp))
    (hM : IsSplitTorus (baseChanged K M U.toGrp)) (f : T ⟶ U) (r : ℝ≥0) :
    (localTorusFiltrationAtSplitting F E T r).map
      (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
        localTorusFiltrationAtSplitting F M U r := by
  have hnorm := map_localTorusNormIwahori_le F E T M hE hM f
  have hpos : (localGeometricCharacterCongruence F T r).map
      (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
        localGeometricCharacterCongruence F U r :=
    map_extendedCharacterCongruence_le K Ω
      (algebraicExtensionAddValuation F Ω) T.toGrp (H := U.toGrp)
      (CommGroupScheme.groupHom f) r
  by_cases hr : r = 0
  · subst r
    simpa only [localTorusFiltrationAtSplitting_zero] using hnorm
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    simp only [localTorusFiltrationAtSplitting, ite_eq_right hr, Subgroup.mem_inf] at ht ⊢
    constructor
    · apply hnorm
      exact Subgroup.mem_map_of_mem _ ht.1
    · apply hpos
      exact Subgroup.mem_map_of_mem _ ht.2

/-- For an induced torus the Iwahori intersection imposes no extra condition
at any positive depth. -/
theorem localTorusFiltrationAtSplitting_eq_geometric_of_induced
    (hE : IsSplitTorus (baseChanged K E T.toGrp)) (hT : IsInducedTorus T)
    {r : ℝ≥0} (hr : 0 < r) :
    localTorusFiltrationAtSplitting F E T r = localGeometricCharacterCongruence F T r := by
  rw [localTorusFiltrationAtSplitting, ite_eq_right (ne_of_gt hr),
    inducedTorusIwahori F T E hE hT]
  exact inf_eq_right.mpr
    (localGeometricCharacterCongruence_le_characterValuationKernel F T r)

/-- In positive depth the induced-torus family is exactly the geometric
character depth test, in the base field's additive normalization. -/
theorem mem_localTorusFiltrationAtSplitting_of_induced
    (hE : IsSplitTorus (baseChanged K E T.toGrp)) (hT : IsInducedTorus T)
    {r : ℝ≥0} (hr : 0 < r) (t : rationalPoints T.toGrp) :
    t ∈ localTorusFiltrationAtSplitting F E T r ↔
      ∀ χ : rationalCharacters (baseChanged K Ω T.toGrp),
        ((r : ℝ) : WithTop ℝ) ≤ algebraicExtensionAddValuation F Ω
          ((rationalCharacterEval χ (rationalExtend K Ω T.toGrp t) : Ω) - 1) := by
  rw [localTorusFiltrationAtSplitting_eq_geometric_of_induced F E T hE hT hr]
  simp only [localGeometricCharacterCongruence, mem_extendedCharacterCongruence,
    mem_characterCongruence, mem_addValuationUnitFiltration_of_pos _ hr]

/-- A finite Galois splitting field inside the fixed common separable closure. -/
structure LocalTorusSplittingData
    (T : CommGroupScheme (Spec (CommRingCat.of K))) where
  L : IntermediateField K Ω
  [finiteDimensional : FiniteDimensional K L]
  [isGalois : IsGalois K L]
  splits : IsSplitTorus (baseChanged K L T.toGrp)

attribute [instance] LocalTorusSplittingData.finiteDimensional
  LocalTorusSplittingData.isGalois

/-- Choose actual embedded splitting data for every torus over the unramified field. -/
def localTorusSplittingData
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (hT : IsTorus T.toGrp) :
    LocalTorusSplittingData F T := by
  classical
  let h :=
    exists_finiteGaloisSplittingField_inside Ω T.toGrp hT
  exact {
    L := h.choose
    finiteDimensional := h.choose_spec.1
    isGalois := h.choose_spec.2.1
    splits := h.choose_spec.2.2 }

/-- A common family for every actual torus over the maximal unramified field.
Its positive character test and its zero norm subgroup do not depend on
any caller-supplied splitting choice. -/
def localTorusFiltration
    (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) (r : ℝ≥0) : Subgroup (rationalPoints T.toGrp) :=
  let S := localTorusSplittingData F T hT
  localTorusFiltrationAtSplitting F S.L T r

/-- The chosen common family agrees with its construction from every splitting field. -/
theorem localTorusFiltration_eq_of_splitting
    (hT : IsTorus T.toGrp) (hE : IsSplitTorus (baseChanged K E T.toGrp)) :
    localTorusFiltration F T hT = localTorusFiltrationAtSplitting F E T := by
  let S := localTorusSplittingData F T hT
  change localTorusFiltrationAtSplitting F S.L T = _
  exact localTorusFiltrationAtSplitting_eq F S.L T E S.splits hE

/-- The zero term is exactly the actual torus Iwahori of any splitting field. -/
theorem localTorusFiltration_zero
    (hT : IsTorus T.toGrp) (hE : IsSplitTorus (baseChanged K E T.toGrp)) :
    localTorusFiltration F T hT 0 = torusNormIwahori K E (intermediateValuation F E) T := by
  rw [localTorusFiltration_eq_of_splitting F E T hT hE,
    localTorusFiltrationAtSplitting_zero]

/-- The common family decreases with nonnegative real depth. -/
theorem localTorusFiltration_antitone (hT : IsTorus T.toGrp) :
    Antitone (localTorusFiltration F T hT) := by
  let S := localTorusSplittingData F T hT
  exact localTorusFiltrationAtSplitting_antitone F S.L T

set_option maxHeartbeats 800000 in
/-- Every member lies in the actual base character-valuation kernel. -/
theorem localTorusFiltration_le_characterValuationKernel
    (hT : IsTorus T.toGrp) (r : ℝ≥0) :
    localTorusFiltration F T hT r ≤
      characterValuationKernel (fixedFieldValuation F) T.toGrp := by
  let S := localTorusSplittingData F T hT
  have hnorm := torusNormIwahori_le_characterValuationKernel
    (fixedFieldValuation F) (intermediateValuation F S.L)
    (intermediateValuation_conjugate F S.L) T
  change localTorusFiltrationAtSplitting F S.L T r ≤ _
  by_cases hr : r = 0
  · simpa only [hr, localTorusFiltrationAtSplitting_zero] using hnorm
  · simp only [localTorusFiltrationAtSplitting, ite_eq_right hr]
    intro t ht
    exact hnorm ht.1

/-- The common family is separated for every actual torus. -/
theorem iInf_localTorusFiltration_eq_bot (hT : IsTorus T.toGrp) :
    ⨅ r : ℝ≥0, localTorusFiltration F T hT r = ⊥ := by
  let S := localTorusSplittingData F T hT
  exact iInf_localTorusFiltrationAtSplitting_eq_bot F S.L T S.splits

/-- The common families are functorial for all actual torus morphisms. -/
theorem map_localTorusFiltration_le
    {U : CommGroupScheme (Spec (CommRingCat.of K))} [IsAffine U.X.left]
    (hT : IsTorus T.toGrp) (hU : IsTorus U.toGrp) (f : T ⟶ U) (r : ℝ≥0) :
    (localTorusFiltration F T hT r).map
      (rationalPoints.map (CommGroupScheme.groupHom f)) ≤ localTorusFiltration F U hU r := by
  let S := localTorusSplittingData F T hT
  let Q := localTorusSplittingData F U hU
  exact map_localTorusFiltrationAtSplitting_le F S.L T Q.L S.splits Q.splits f r

/-- For an induced torus, positive membership is exactly the normalized
geometric-character congruence formula, without a supplied splitting field. -/
theorem mem_localTorusFiltration_of_induced
    (hT : IsTorus T.toGrp) (hind : IsInducedTorus T)
    {r : ℝ≥0} (hr : 0 < r) (t : rationalPoints T.toGrp) :
    t ∈ localTorusFiltration F T hT r ↔
      ∀ χ : rationalCharacters (baseChanged K Ω T.toGrp),
        ((r : ℝ) : WithTop ℝ) ≤ algebraicExtensionAddValuation F Ω
          ((rationalCharacterEval χ (rationalExtend K Ω T.toGrp t) : Ω) - 1) := by
  let S := localTorusSplittingData F T hT
  exact mem_localTorusFiltrationAtSplitting_of_induced F S.L T S.splits hind hr t

end Local

end Langlands.Geometry.Building
