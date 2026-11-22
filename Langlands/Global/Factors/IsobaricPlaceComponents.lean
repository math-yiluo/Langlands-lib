import Langlands.Automorphic.ArchimedeanStandardAdmissibleProof
import Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex
import Langlands.Global.Factors.IsobaricAutomorphicRepresentation
import Langlands.Representation.Archimedean.ComplexStandardLanglandsQuotientProof
import Langlands.Representation.Archimedean.GKModuleQuotient
import Langlands.Representation.Archimedean.OrderedStandardPermutation
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-! # Archimedean local components from isobaric witnesses -/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Archimedean Langlands.LocalFactor.Archimedean PlaceComponent

section Range

variable {K L X V V' : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']
  {σ : Representation ℂ K X} {τ : L →ₗ⁅ℂ⁆ Module.End ℂ X}
  {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ρ' : Representation ℂ K V'} {π' : L →ₗ⁅ℂ⁆ Module.End ℂ V'}
  {A : X →ₗ[ℂ] V} {B : X →ₗ[ℂ] V'}

private theorem comp_surjective_preserves_range
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {σY : Representation ℂ K Y} {τY : L →ₗ⁅ℂ⁆ Module.End ℂ Y}
    {T : Y →ₗ[ℂ] X} (hT : T ∈ gkHoms σY τY σ τ) (hs : Function.Surjective T)
    (hA : A ∈ gkHoms σ τ ρ π) (hAr : PlaceComponent.IsIrreducible ρ π (LinearMap.range A)) :
    A.comp T ∈ gkHoms σY τY ρ π ∧
      PlaceComponent.IsIrreducible ρ π (LinearMap.range (A.comp T)) := by
  refine ⟨⟨fun k y => (congrArg A (hT.1 k y)).trans (hA.1 k (T y)),
    fun X y => (congrArg A (hT.2 X y)).trans (hA.2 X (T y))⟩, ?_⟩
  rw [LinearMap.range_comp_of_range_eq_top A (LinearMap.range_eq_top.mpr hs)]
  exact hAr

private theorem isStable_range (hA : A ∈ gkHoms σ τ ρ π) :
    IsStable ρ π (LinearMap.range A) := by
  constructor
  · rintro k _ ⟨x, rfl⟩
    exact ⟨σ k x, hA.1 k x⟩
  · rintro Y _ ⟨x, rfl⟩
    exact ⟨τ Y x, hA.2 Y x⟩

private theorem rangeRestrict_mem_gkHoms (hA : A ∈ gkHoms σ τ ρ π)
    (hW : IsStable ρ π (LinearMap.range A)) :
    A.rangeRestrict ∈ gkHoms σ τ (restrictCompact hW) (restrictLie hW) :=
  ⟨fun k x => Subtype.ext (hA.1 k x), fun Y x => Subtype.ext (hA.2 Y x)⟩

private theorem ker_eq_of_irreducible_ranges (hA : A ∈ gkHoms σ τ ρ π)
    (hB : B ∈ gkHoms σ τ ρ' π')
    (hAr : PlaceComponent.IsIrreducible ρ π (LinearMap.range A))
    (hBr : PlaceComponent.IsIrreducible ρ' π' (LinearMap.range B))
    {R : Submodule ℂ X} (hR : IsGKSubmodule σ τ R) (hRtop : R ≠ ⊤)
    (hRmax : ∀ W : Submodule ℂ X, IsGKSubmodule σ τ W → W ≠ ⊤ → W ≤ R) :
    LinearMap.ker A = LinearMap.ker B := by
  have hA' := rangeRestrict_mem_gkHoms hA hAr.2.1
  have hB' := rangeRestrict_mem_gkHoms hB hBr.2.1
  have hAr' : A.rangeRestrict ≠ 0 := by
    intro h
    exact hAr.1 (LinearMap.range_eq_bot.mpr (by
      rw [← LinearMap.subtype_comp_rangeRestrict A, h, LinearMap.comp_zero]))
  have hBr' : B.rangeRestrict ≠ 0 := by
    intro h
    exact hBr.1 (LinearMap.range_eq_bot.mpr (by
      rw [← LinearMap.subtype_comp_rangeRestrict B, h, LinearMap.comp_zero]))
  have hRA := eq_ker_of_largest_proper hA'.1 hA'.2
    (isIrreducibleGKModule_restrict hAr) hAr' hR hRtop hRmax
  have hRB := eq_ker_of_largest_proper hB'.1 hB'.2
    (isIrreducibleGKModule_restrict hBr) hBr' hR hRtop hRmax
  simpa only [LinearMap.ker_rangeRestrict] using hRA.symm.trans hRB

private theorem isGKIsotypic_range_of_ker_eq (hA : A ∈ gkHoms σ τ ρ π)
    (hB : B ∈ gkHoms σ τ ρ' π')
    (hAr : IsStable ρ π (LinearMap.range A)) (hBr : IsStable ρ' π' (LinearMap.range B))
    (hker : LinearMap.ker A = LinearMap.ker B)
    (hisotypic : IsGKIsotypic (restrictCompact hBr) (restrictLie hBr) ρ' π') :
    IsGKIsotypic (restrictCompact hAr) (restrictLie hAr) ρ' π' := by
  have hker' : LinearMap.ker A ≤ LinearMap.ker B.rangeRestrict := by
    rw [LinearMap.ker_rangeRestrict]
    exact hker.le
  let D : LinearMap.range A →ₗ[ℂ] LinearMap.range B :=
    ((LinearMap.ker A).liftQ B.rangeRestrict hker').comp
      A.quotKerEquivRange.symm.toLinearMap
  have hD (x : X) : D (A.rangeRestrict x) = B.rangeRestrict x := by
    change (LinearMap.ker A).liftQ B.rangeRestrict hker'
      (A.quotKerEquivRange.symm ⟨A x, LinearMap.mem_range_self A x⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ x
  have hAD := rangeRestrict_mem_gkHoms hA hAr
  have hBD := rangeRestrict_mem_gkHoms hB hBr
  change gkSpan (restrictCompact hAr) (restrictLie hAr) ρ' π' = ⊤
  apply top_unique
  rw [← hisotypic]
  refine iSup_le fun C => iSup_le fun hC => ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := B.surjective_rangeRestrict y
  have hCD : C ∘ₗ D ∈ gkHoms (restrictCompact hAr) (restrictLie hAr) ρ' π' := by
    constructor
    · intro k y
      obtain ⟨z, rfl⟩ := A.surjective_rangeRestrict y
      simp only [LinearMap.comp_apply, ← hAD.1, hD, hBD.1, hC.1]
    · intro Y y
      obtain ⟨z, rfl⟩ := A.surjective_rangeRestrict y
      simp only [LinearMap.comp_apply, ← hAD.2, hD, hBD.2, hC.2]
  simpa only [LinearMap.comp_apply, hD] using apply_mem_gkSpan hCD (A.rangeRestrict x)

end Range

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance isobaricPlaceRationalGroup (j : ℕ) : AddCommGroup (RationalInvariantFunctions F j) :=
  Submodule.addCommGroup _
local instance isobaricPlaceContinuousGroup (j : ℕ) : AddCommGroup (ContinuousRationalFunctions F j) :=
  Submodule.addCommGroup _
local instance isobaricPlaceSmoothGroup (j : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F j) :=
  Submodule.addCommGroup _
local instance isobaricPlaceFormGroup (j : ℕ) : AddCommGroup (AutomorphicForms F j) :=
  Submodule.addCommGroup _
local instance isobaricPlaceStableGroup (j : ℕ) : AddCommGroup (StableAutomorphicFunctions F j) :=
  Submodule.addCommGroup _
local instance isobaricPlaceRealizationGroup {j : ℕ} (S : OperatorRealization F j) :
    AddCommGroup S.Space := Submodule.addCommGroup _

private theorem ordered_realStandard {ds : List RealBlock}
    (h : LocalFactor.Archimedean.IsRealLanglandsOrdered ds) :
    Archimedean.IsRealLanglandsOrdered ds :=
  h.imp fun {a b} hab => by cases a <;> cases b <;> exact hab

namespace OperatorSubquotient

variable {Q : OperatorSubquotient F n}

/-- A real standard-module witness supplies an irreducible range for the full place action. -/
theorem HasRealPlaceLanglandsQuotient.exists_irreducibleRange {v : RP} {ds : List RealBlock}
    (h : Q.HasRealPlaceLanglandsQuotient v ds) :
    ∃ A : realStandardKFinite n ds →ₗ[ℂ] Q.Space,
      A ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds)
        (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) ∧
      PlaceComponent.IsIrreducible (Q.realPlaceCompactRepresentation v)
        (Q.realPlaceLieAction v) (LinearMap.range A) := by
  obtain ⟨_, _, A, hK, hL, hA0, hAmin⟩ := h
  have hA : IsRealStandardIntertwiner n (Q.realPlaceCompactRepresentation v)
      (Q.realPlaceLieAction v) ds A := ⟨hK, hL⟩
  have hg : A ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds)
      (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) :=
    ⟨hA.map_realStandardRep, hA.map_realStandardLie⟩
  exact ⟨A, hg, hA0, isStable_range hg, fun W hWle hW =>
    hAmin W hWle hW.1 (fun X x hx => hW.2 (1 ⊗ₜ X) x hx)⟩

/-- A complex standard-module witness supplies an irreducible range for the full place action. -/
theorem HasComplexPlaceLanglandsQuotient.exists_irreducibleRange
    {v : CP} {ds : List ComplexCharacterData} (h : Q.HasComplexPlaceLanglandsQuotient v ds) :
    ∃ A : complexStandardKFinite n ds →ₗ[ℂ] Q.Space,
      A ∈ gkHoms (complexStandardRep n ds) (complexStandardLie n ds)
        (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v) ∧
      PlaceComponent.IsIrreducible (Q.complexPlaceCompactRepresentation v)
        (Q.complexPlaceLieAction v) (LinearMap.range A) := by
  obtain ⟨_, _, A, hK, hL, hA0, hAmin⟩ := h
  have hA : IsComplexStandardIntertwining n (Q.complexPlaceCompactRepresentation v)
      (Q.complexPlaceLieAction v) ds A := ⟨hK, hL⟩
  have hg : A ∈ gkHoms (complexStandardRep n ds) (complexStandardLie n ds)
      (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v) :=
    ⟨hA.map_rep, hA.map_lie⟩
  exact ⟨A, hg, hA0, isStable_range hg, fun W hWle hW =>
    hAmin W hWle hW.1 (fun X x hx => hW.2 (1 ⊗ₜ X) x hx)⟩

/-- The range of a real standard-module map carries an admissible `(𝔤, K)`-structure. -/
theorem realStandardRange_isRealGKModule_and_admissible {v : RP} {ds : List RealBlock}
    {A : realStandardKFinite n ds →ₗ[ℂ] Q.Space}
    (hA : A ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds)
      (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v))
    (hW : IsStable (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v)
      (LinearMap.range A)) :
    IsRealGKModule n (restrictCompact hW) (restrictLie hW) ∧
      IsAdmissibleGKModule (restrictCompact hW) := by
  have h := isRealGKModule_realStandardModule n ds
  have hAr := rangeRestrict_mem_gkHoms hA hW
  let a := A.rangeRestrict.intertwiningMap_of_isIntertwiningMap _ _ hAr.1
  exact ⟨h.of_surjective a A.surjective_rangeRestrict hAr.2,
    (realStandardAdmissible n ds).of_surjective h.1 h.2.1 a A.surjective_rangeRestrict⟩

/-- The range of a complex standard-module map carries an admissible `(𝔤, K)`-structure. -/
theorem complexStandardRange_isComplexGKModule_and_admissible {v : CP}
    {ds : List ComplexCharacterData} {A : complexStandardKFinite n ds →ₗ[ℂ] Q.Space}
    (hA : A ∈ gkHoms (complexStandardRep n ds) (complexStandardLie n ds)
      (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v))
    (hW : IsStable (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v)
      (LinearMap.range A)) :
    IsComplexGKModule n (restrictCompact hW) (restrictLie hW) ∧
      IsAdmissibleGKModule (restrictCompact hW) := by
  have h := isComplexGKModule_complexStandardModule n ds
  have hAr := rangeRestrict_mem_gkHoms hA hW
  let a := A.rangeRestrict.intertwiningMap_of_isIntertwiningMap _ _ hAr.1
  exact ⟨h.of_surjective a A.surjective_rangeRestrict hAr.2,
    (complexStandardAdmissible n ds).of_surjective h.1 h.2.1 a A.surjective_rangeRestrict⟩

end OperatorSubquotient

namespace IrreducibleOperatorSubquotient

variable {r : ℕ} {Q Q' : IrreducibleOperatorSubquotient F r}

/-- A surjective map between real standard modules gives a common irreducible admissible type
for their isobaric quotient witnesses, assuming the real Langlands quotient statement. -/
theorem common_realPlaceIsotypic_of_surjective_standard
    (hL : RealStandardLanglandsQuotientStatement) (v : RP) {ds es : List RealBlock}
    (h : Q.subquotient.HasRealPlaceLanglandsQuotient v ds)
    (h' : Q'.subquotient.HasRealPlaceLanglandsQuotient v es)
    {T : realStandardKFinite (r + 1) ds →ₗ[ℂ] realStandardKFinite (r + 1) es}
    (hs : Function.Surjective T)
    (hT : T ∈ gkHoms (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds)
      (realStandardRep (r + 1) es) (realStandardLie (r + 1) es)) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsRealGKModule (r + 1) ρ π ∧ IsAdmissibleGKModule ρ ∧
        IsIrreducibleGKModule ρ π ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsRealPlaceIsotypic v ρ π := by
  obtain ⟨R, hR, hRtop, hRmax⟩ := hL (r + 1) ds h.1 (ordered_realStandard h.2.1)
  obtain ⟨A, hA, hAr⟩ := h.exists_irreducibleRange
  obtain ⟨B, hB, hBr⟩ := h'.exists_irreducibleRange
  obtain ⟨hgk, hadm⟩ := OperatorSubquotient.realStandardRange_isRealGKModule_and_admissible
    hA hAr.2.1
  obtain ⟨hBT, hBTr⟩ :=
    comp_surjective_preserves_range (V := Q'.subquotient.Space) (A := B) hT hs hB hBr
  have hker := ker_eq_of_irreducible_ranges hA hBT hAr hBTr hR hRtop hRmax
  exact ⟨ModuleCat.of ℂ (LinearMap.range A), restrictCompact hAr.2.1, restrictLie hAr.2.1,
    hgk, hadm, isIrreducibleGKModule_restrict hAr,
    Q.subquotient.isRealPlaceIsotypic_restrict Q.irreducible v hAr,
    isGKIsotypic_range_of_ker_eq hA hBT hAr.2.1 hBTr.2.1 hker
      (Q'.subquotient.isRealPlaceIsotypic_restrict Q'.irreducible v hBTr)⟩

/-- A surjective map between complex standard modules gives a common irreducible admissible type
for their isobaric quotient witnesses. -/
theorem common_complexPlaceIsotypic_of_surjective_standard
    (v : CP) {ds es : List ComplexCharacterData}
    (h : Q.subquotient.HasComplexPlaceLanglandsQuotient v ds)
    (h' : Q'.subquotient.HasComplexPlaceLanglandsQuotient v es)
    {T : complexStandardKFinite (r + 1) ds →ₗ[ℂ] complexStandardKFinite (r + 1) es}
    (hs : Function.Surjective T)
    (hT : T ∈ gkHoms (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds)
      (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es)) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsComplexGKModule (r + 1) ρ π ∧ IsAdmissibleGKModule ρ ∧
        IsIrreducibleGKModule ρ π ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsComplexPlaceIsotypic v ρ π := by
  obtain ⟨R, hR, hRtop, hRmax⟩ := complexStandardLanglandsQuotient (r + 1) ds h.1 h.2.1
  obtain ⟨A, hA, hAr⟩ := h.exists_irreducibleRange
  obtain ⟨B, hB, hBr⟩ := h'.exists_irreducibleRange
  obtain ⟨hgk, hadm⟩ := OperatorSubquotient.complexStandardRange_isComplexGKModule_and_admissible
    hA hAr.2.1
  obtain ⟨hBT, hBTr⟩ :=
    comp_surjective_preserves_range (V := Q'.subquotient.Space) (A := B) hT hs hB hBr
  have hker := ker_eq_of_irreducible_ranges hA hBT hAr hBTr hR hRtop hRmax
  exact ⟨ModuleCat.of ℂ (LinearMap.range A), restrictCompact hAr.2.1, restrictLie hAr.2.1,
    hgk, hadm, isIrreducibleGKModule_restrict hAr,
    Q.subquotient.isComplexPlaceIsotypic_restrict Q.irreducible v hAr,
    isGKIsotypic_range_of_ker_eq hA hBT hAr.2.1 hBTr.2.1 hker
      (Q'.subquotient.isComplexPlaceIsotypic_restrict Q'.irreducible v hBTr)⟩

/-- Real quotient witnesses with permuted lists give the same irreducible admissible type,
assuming the real Langlands quotient statement. -/
theorem common_realPlaceIsotypic_of_perm
    (hL : RealStandardLanglandsQuotientStatement) (v : RP) {ds es : List RealBlock}
    (h : Q.subquotient.HasRealPlaceLanglandsQuotient v ds)
    (h' : Q'.subquotient.HasRealPlaceLanglandsQuotient v es) (hp : ds.Perm es) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsRealGKModule (r + 1) ρ π ∧ IsAdmissibleGKModule ρ ∧
        IsIrreducibleGKModule ρ π ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsRealPlaceIsotypic v ρ π := by
  obtain ⟨T, hTs, hTi⟩ := realStandardEquiv_of_ordered_perm hp h.1
    (ordered_realStandard h.2.1) (ordered_realStandard h'.2.1)
  exact common_realPlaceIsotypic_of_surjective_standard hL v h h' hTs.2
    ⟨hTi.map_realStandardRep, hTi.map_realStandardLie⟩

/-- Real quotient witnesses with permuted Mœglin data give the same irreducible admissible type,
assuming the real Langlands quotient statement. -/
theorem common_realPlaceIsotypic_of_moeglin_perm
    (hL : RealStandardLanglandsQuotientStatement) (v : RP) {ds es : List RealBlock}
    (h : Q.subquotient.HasRealPlaceLanglandsQuotient v ds)
    (h' : Q'.subquotient.HasRealPlaceLanglandsQuotient v es)
    (hp : (realMoeglinData ds).Perm (realMoeglinData es)) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsRealGKModule (r + 1) ρ π ∧ IsAdmissibleGKModule ρ ∧
        IsIrreducibleGKModule ρ π ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsRealPlaceIsotypic v ρ π := by
  obtain ⟨T, hTs, hTi⟩ := realStandardSurjection_of_moeglin_perm hp h.1
    (ordered_realStandard h.2.1) (ordered_realStandard h'.2.1)
  exact common_realPlaceIsotypic_of_surjective_standard hL v h h' hTs
    ⟨hTi.map_realStandardRep, hTi.map_realStandardLie⟩

/-- Complex quotient witnesses with permuted lists give the same irreducible admissible type. -/
theorem common_complexPlaceIsotypic_of_perm
    (v : CP) {ds es : List ComplexCharacterData}
    (h : Q.subquotient.HasComplexPlaceLanglandsQuotient v ds)
    (h' : Q'.subquotient.HasComplexPlaceLanglandsQuotient v es) (hp : ds.Perm es) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsComplexGKModule (r + 1) ρ π ∧ IsAdmissibleGKModule ρ ∧
        IsIrreducibleGKModule ρ π ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsComplexPlaceIsotypic v ρ π := by
  obtain ⟨T, hTs, hTi⟩ := complexStandardEquiv_of_ordered_perm hp h.1 h.2.1 h'.2.1
  exact common_complexPlaceIsotypic_of_surjective_standard v h h' hTs.2
    ⟨hTi.map_rep, hTi.map_lie⟩

/-- Two real place restrictions with the same standard-module witness are isotypic for a common
irreducible admissible factor if the standard module has a largest proper stable subspace. -/
theorem common_realPlaceIsotypic_of_same_standard
    (hL : RealStandardLanglandsQuotientStatement) (v : RP) {ds : List RealBlock}
    (h : Q.subquotient.HasRealPlaceLanglandsQuotient v ds)
    (h' : Q'.subquotient.HasRealPlaceLanglandsQuotient v ds) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsRealGKModule (r + 1) ρ π ∧ IsAdmissibleGKModule ρ ∧
        IsIrreducibleGKModule ρ π ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsRealPlaceIsotypic v ρ π :=
  common_realPlaceIsotypic_of_perm hL v h h' (List.Perm.refl ds)

/-- Two complex place restrictions with the same standard-module witness
are isotypic for a common irreducible admissible factor. -/
theorem common_complexPlaceIsotypic_of_same_standard
    (v : CP) {ds : List ComplexCharacterData}
    (h : Q.subquotient.HasComplexPlaceLanglandsQuotient v ds)
    (h' : Q'.subquotient.HasComplexPlaceLanglandsQuotient v ds) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsComplexGKModule (r + 1) ρ π ∧ IsAdmissibleGKModule ρ ∧
        IsIrreducibleGKModule ρ π ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsComplexPlaceIsotypic v ρ π :=
  common_complexPlaceIsotypic_of_perm v h h' (List.Perm.refl ds)

end IrreducibleOperatorSubquotient

end Langlands.Automorphic
