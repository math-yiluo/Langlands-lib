import Langlands.LocalFactor.DeligneHenniartUpperUnits
import Langlands.LocalFactor.DeligneHenniartWitnessGroups
import Langlands.LocalFactor.Ramification.WeilBreakStatement
import Langlands.LocalFactor.RankOneStabilityCoset
import Langlands.LocalFactor.NonabelianRankOneScaling
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.VirtualRepresentation.ExactDeterminantInduction

/-! # The exact Deligne--Henniart witness coset -/

noncomputable section

universe uF uV uW

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local
open LocalWeil.Ramification Ramification.Padic LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-! ## Determinants of low-break virtual representations -/

/-- The determinant of an irreducible class with label below `t` is trivial
on the upper group of index `t`, once triviality thresholds are nonempty. -/
theorem determinantCharacter_generator_eq_one
    (hthr : WeilTrivialityThresholdsNonempty.{uF, uW} F)
    (b : LocalWeil.Basis.{uF, uW} F) {t : ℝ} (hb : breakLabel F b < t)
    {g : localWeilGroup F} (hg : g ∈ upperGroup F t) :
    ExactGrothendieckGroup.determinantCharacter _
      (LocalWeil.realizeExact F (generator b)) g = 1 := by
  rw [LocalWeil.realizeExact_generator, ExactGrothendieckGroup.determinantCharacter_ofClass,
    Weil.forgetProperty_basisContinuousClass]
  obtain ⟨n, c, hc⟩ := b
  induction c using Quotient.inductionOn with
  | h A =>
    have hlt : lastBreak F A.val < t := hb
    obtain ⟨r, hr, hrt⟩ := exists_lt_of_csInf_lt (hthr A.val A.property.1) hlt
    have htriv := isTrivialAt_mono F A.val hrt.le hr.2 g hg
    apply Units.ext
    change LinearMap.det (A.val.representation g) = 1
    rw [htriv]
    exact map_one LinearMap.det

/-- A virtual Weil representation all of whose constituents have label below
`t` has determinant trivial on the upper group of index `t`. -/
theorem determinantCharacter_realizeExact_eq_one
    (hthr : WeilTrivialityThresholdsNonempty.{uF, uW} F)
    (w : LocalWeil.Lattice.{uF, uW} F) {t : ℝ} (hw : AllBreaksBelow F w t)
    {g : localWeilGroup F} (hg : g ∈ upperGroup F t) :
    ExactGrothendieckGroup.determinantCharacter _ (LocalWeil.realizeExact F w) g = 1 := by
  induction w using Finsupp.induction with
  | zero => simp
  | single_add b n f hb hn ih =>
    have hb' : breakLabel F b < t := by
      apply hw b
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hb,
        add_zero]
      exact hn
    have hf : AllBreaksBelow F f t := by
      intro c hc
      have hcb : c ≠ b := fun h => hb (h ▸ Finsupp.mem_support_iff.mpr hc)
      apply hw c
      rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hcb, zero_add]
    have hsingle : Finsupp.single b n = n • generator b := by
      simp [generator]
    rw [map_add, ExactGrothendieckGroup.determinantCharacter_add_apply, ih hf, mul_one,
      hsingle, map_zsmul, ExactGrothendieckGroup.determinantCharacter_zsmul_apply,
      determinantCharacter_generator_eq_one F hthr b hb' hg, one_zpow]

/-- On the bottom Weil subgroup, the determinant of the literal base-component
realization is the determinant of the exact realization. -/
theorem determinantCharacter_realizeAtBase
    (w : LocalWeil.Lattice.{uF, max uF uV} F) (g : weilSubgroup F (baseExtension F)) :
    ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F (baseExtension F))
      (realizeAtBase F w) g =
      ExactGrothendieckGroup.determinantCharacter _ (LocalWeil.realizeExact F w)
        (g : localWeilGroup F) := by
  unfold realizeAtBase ExactGrothendieckGroup.continuousRestrict
  rw [LinearMap.comp_apply, ExactGrothendieckGroup.determinantCharacter_restrict]
  rfl

/-- The same vanishing for the literal base-component realization. -/
theorem determinantCharacter_realizeAtBase_eq_one
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (w : LocalWeil.Lattice.{uF, max uF uV} F) {t : ℝ} (hw : AllBreaksBelow F w t)
    (g : weilSubgroup F (baseExtension F)) (hg : g ∈ baseUpperGroup F t) :
    ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F (baseExtension F))
      (realizeAtBase F w) g = 1 := by
  rw [determinantCharacter_realizeAtBase]
  exact determinantCharacter_realizeExact_eq_one F hthr w hw hg

/-- Field form: the descended determinant of a virtual representation with all
labels below `t ≥ 0` is trivial on the principal units of level `⌈t⌉`. -/
theorem fieldDeterminant_eq_one_of_mem_principalUnits
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    (w : LocalWeil.Lattice.{uF, max uF uV} F) {t : ℝ} (ht : 0 ≤ t)
    (hw : AllBreaksBelow F w t) (δ : (baseExtension F).fieldˣ)
    (hδ : δ ∈ (fieldData F (baseExtension F)).principalUnits ⌈t⌉₊) :
    fieldDeterminant.{uF, uV} F eC _ (realizeAtBase F w) δ = 1 := by
  let := (fieldData F (baseExtension F)).topology
  have hmap := baseUpperGroup_map_reciprocityUnits F hreal hinert hcmp eC he ht
  rw [← hmap] at hδ
  obtain ⟨g, hg, rfl⟩ := hδ
  change fieldDeterminant F eC _ (realizeAtBase F w) (reciprocityUnits F eC _ g) = 1
  rw [fieldDeterminant_reciprocityUnits]
  exact determinantCharacter_realizeAtBase_eq_one F hthr w hw g hg

/-! ## Rank-one test representations -/

/-- Every local Weil element lies in the bottom Weil subgroup. -/
theorem mem_baseWeil (w : localWeilGroup F) : w ∈ weilSubgroup F (baseExtension F) := by
  rw [baseWeil_eq_top]
  trivial

/-- The literal inverse of the bottom inclusion: every local Weil element lies
in the bottom Weil subgroup, since that subgroup is the whole group. -/
def baseWeilSection : localWeilGroup F →ₜ* weilSubgroup F (baseExtension F) where
  toFun w := ⟨w, mem_baseWeil F w⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id.subtype_mk (mem_baseWeil F)

@[simp]
theorem baseWeilSection_val (g : weilSubgroup F (baseExtension F)) :
    baseWeilSection F (g : localWeilGroup F) = g :=
  rfl

@[simp]
theorem coe_baseWeilSection (w : localWeilGroup F) :
    (baseWeilSection F w : localWeilGroup F) = w :=
  rfl

/-- A bottom-field quasicharacter read on the local Weil group through the
base component of a common-closure family. -/
def baseWeilCharacter (eC : ReciprocityFamily F) (η : FieldCharacter F (baseExtension F)) :
    localWeilGroup F →ₜ* ℂˣ :=
  (weilCharacter F eC (baseExtension F) η).comp (baseWeilSection F)

theorem baseWeilCharacter_apply (eC : ReciprocityFamily F)
    (η : FieldCharacter F (baseExtension F)) (g : weilSubgroup F (baseExtension F)) :
    baseWeilCharacter F eC η (g : localWeilGroup F) = η (reciprocityUnits F eC _ g) :=
  rfl

variable {F}

/-- The irreducible class of the character line of a continuous character. -/
def lineBasis (χ : localWeilGroup F →ₜ* ℂˣ) : LocalWeil.Basis.{uF, uW} F :=
  LocalWeil.basisClass (FiniteRepresentation.characterLine.{uF, uW} χ.toMonoidHom)
    (FiniteRepresentation.characterLine_isContinuous χ)
    (FiniteRepresentation.characterLine_isIrreducible χ.toMonoidHom) 1 (by simp)

theorem realizeExact_generator_lineBasis (χ : localWeilGroup F →ₜ* ℂˣ) :
    LocalWeil.realizeExact F (generator (lineBasis.{uF, uW} χ)) =
      ExactGrothendieckGroup.characterClass.{uF, uW} χ :=
  LocalWeil.realizeExact_ofRepresentation _ _ _ _ _

theorem degree_generator_lineBasis (χ : localWeilGroup F →ₜ* ℂˣ) :
    LocalWeil.degree F (generator (lineBasis.{uF, uW} χ)) = 1 := by
  rw [← LocalWeil.degree_realizeExact, realizeExact_generator_lineBasis,
    ExactGrothendieckGroup.degree_characterClass]

theorem determinantCharacter_generator_lineBasis (χ : localWeilGroup F →ₜ* ℂˣ) :
    ExactGrothendieckGroup.determinantCharacter _
      (LocalWeil.realizeExact F (generator (lineBasis.{uF, uW} χ))) = χ.toMonoidHom := by
  rw [realizeExact_generator_lineBasis, ExactGrothendieckGroup.determinantCharacter_characterClass]

/-- A character trivial on the upper group of index `r ≥ 0` has line label at
most `r`. -/
theorem breakLabel_lineBasis_le (χ : localWeilGroup F →ₜ* ℂˣ) {r : ℝ} (hr : 0 ≤ r)
    (hχ : ∀ w ∈ upperGroup F r, χ w = 1) :
    breakLabel F (lineBasis.{uF, uW} χ) ≤ r := by
  apply lastBreak_le_of_mem
  refine ⟨hr, fun w hw => ?_⟩
  apply LinearMap.ext
  intro v
  change ((χ w : ℂˣ) : ℂ) • v = v
  rw [hχ w hw, Units.val_one, one_smul]

/-- The degree-zero test combination `[χ] - [1]`. -/
def lineDifference (χ : localWeilGroup F →ₜ* ℂˣ) : LocalWeil.Lattice.{uF, uW} F :=
  generator (lineBasis.{uF, uW} χ) - generator (lineBasis.{uF, uW} (1 : localWeilGroup F →ₜ* ℂˣ))

theorem degree_lineDifference (χ : localWeilGroup F →ₜ* ℂˣ) :
    LocalWeil.degree F (lineDifference.{uF, uW} χ) = 0 := by
  rw [lineDifference, map_sub, degree_generator_lineBasis, degree_generator_lineBasis, sub_self]

theorem determinantCharacter_lineDifference (χ : localWeilGroup F →ₜ* ℂˣ)
    (g : localWeilGroup F) :
    ExactGrothendieckGroup.determinantCharacter _
      (LocalWeil.realizeExact F (lineDifference.{uF, uW} χ)) g = χ g := by
  rw [lineDifference, map_sub, ExactGrothendieckGroup.determinantCharacter_sub_apply,
    determinantCharacter_generator_lineBasis, determinantCharacter_generator_lineBasis]
  simp

/-- If the character is trivial on the upper group of index `r` with
`0 ≤ r < b`, every constituent of `[χ] - [1]` has label below `b`. -/
theorem allBreaksBelow_lineDifference (χ : localWeilGroup F →ₜ* ℂˣ) {r b : ℝ}
    (hr : 0 ≤ r) (hrb : r < b) (hχ : ∀ w ∈ upperGroup F r, χ w = 1) :
    AllBreaksBelow F (lineDifference.{uF, uW} χ) b := by
  intro c hc
  by_cases h1 : c = lineBasis.{uF, uW} χ
  · rw [h1]
    exact (breakLabel_lineBasis_le χ hr hχ).trans_lt hrb
  by_cases h0 : c = lineBasis.{uF, uW} (1 : localWeilGroup F →ₜ* ℂˣ)
  · rw [h0]
    refine (breakLabel_lineBasis_le (1 : localWeilGroup F →ₜ* ℂˣ) le_rfl ?_).trans_lt
      (hr.trans_lt hrb)
    intro w _
    rfl
  exfalso
  apply hc
  rw [lineDifference, Finsupp.sub_apply]
  simp only [generator]
  rw [Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h0, sub_zero]

variable (F)

/-! ## The zero-input annihilator -/

/-- Separation: an element on which every degree-zero test of labels below
`a / 2` has trivial determinant lies in the principal units of level `⌈a / 2⌉`.
The tests used are differences `[η ∘ rec] - [1]` of character lines. -/
theorem mem_principalUnits_of_fieldDeterminant_eq_one
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {a : ℝ} (ha : 0 < a) (δ : (baseExtension F).fieldˣ)
    (h : ∀ w : LocalWeil.Lattice.{uF, max uF uV} F, LocalWeil.degree F w = 0 →
      AllBreaksBelow F w (a / 2) →
      fieldDeterminant.{uF, uV} F eC _ (realizeAtBase F w) δ = 1) :
    δ ∈ (fieldData F (baseExtension F)).principalUnits ⌈a / 2⌉₊ := by
  let := (fieldData F (baseExtension F)).topology
  apply (PadicAbelian.mem_principalUnits_iff_bounded_characters
    (fieldData F (baseExtension F)) _ δ).mpr
  intro η hη
  set m := ⌈a / 2⌉₊ with hm
  have ha2 : 0 < a / 2 := by linarith
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ha2).ne'
  have hmlt : (m : ℝ) - 1 < a / 2 := by
    have := Nat.ceil_lt_add_one ha2.le
    rw [← hm] at this
    linarith
  set r : ℝ := ((m : ℝ) - 1 + a / 2) / 2 with hr
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hra : r < a / 2 := by rw [hr]; linarith
  have hmr : m ≤ ⌈r⌉₊ := by
    have hlt : m - 1 < ⌈r⌉₊ := by
      apply Nat.lt_ceil.mpr
      rw [Nat.cast_sub hm1, Nat.cast_one, hr]
      linarith
    omega
  have hmap := baseUpperGroup_map_reciprocityUnits F hreal hinert hcmp eC he hr0
  have hχ : ∀ w ∈ upperGroup F r, baseWeilCharacter F eC η w = 1 := by
    intro w hw
    have hmem : reciprocityUnits F eC _ (baseWeilSection F w) ∈
        (fieldData F (baseExtension F)).principalUnits ⌈r⌉₊ := by
      rw [← hmap]
      exact ⟨baseWeilSection F w, hw, rfl⟩
    exact ((fieldData F (baseExtension F)).multiplicativeTrivialAt_iff_conductor_le η m).mpr
      hη _ ((fieldData F (baseExtension F)).principalUnits_antitone hmr hmem)
  have hw := h (lineDifference.{uF, max uF uV} (baseWeilCharacter F eC η))
    (degree_lineDifference _) (allBreaksBelow_lineDifference _ hr0 hra hχ)
  obtain ⟨g, rfl⟩ := reciprocityUnits_surjective F eC (baseExtension F) δ
  rw [fieldDeterminant_reciprocityUnits, determinantCharacter_realizeAtBase,
    determinantCharacter_lineDifference, baseWeilCharacter_apply] at hw
  exact hw

private theorem haarMeasure_nonempty (E : Extension F) :
    Nonempty (HaarMeasure F E) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  let := (fieldData F E).fieldT2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts E.field) := inferInstance
  exact ⟨HarmonicAnalysis.normalizedAdditiveHaar E.field K⟩

/-- DH81 4.6 coset at zero input: the zero-input exact witnesses are exactly
the principal units of level `⌈a / 2⌉`, for `a > 0`. -/
theorem exactWitness_zero_iff
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    {a : ℝ} (ha : 0 < a) (ψ : AdditiveCharacter F (baseExtension F))
    (δ : (baseExtension F).fieldˣ) :
    ExactWitness F eC ε 0 a ψ δ ↔
      δ ∈ (fieldData F (baseExtension F)).principalUnits ⌈a / 2⌉₊ := by
  rw [exactWitness_iff]
  simp only [map_zero, value_zero hε]
  constructor
  · intro h
    obtain ⟨μ⟩ := haarMeasure_nonempty F (baseExtension F)
    exact mem_principalUnits_of_fieldDeterminant_eq_one F hreal hinert hcmp eC he ha δ
      (fun w hw0 hwb => (h w hw0 hwb μ).symm)
  · intro hδ w _ hwb _
    exact (fieldDeterminant_eq_one_of_mem_principalUnits F hthr hreal hinert hcmp eC he w
      (by linarith) hwb δ hδ).symm

/-- The coset clause of DH81 4.6: relative to one exact witness, the exact
witnesses form precisely its coset of the principal units of level `⌈a / 2⌉`. -/
theorem exactWitness_iff_mem_coset
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    {v : LocalWeil.Lattice.{uF, max uF uV} F} {a : ℝ} (ha : 0 < a)
    {ψ : AdditiveCharacter F (baseExtension F)} {γ : (baseExtension F).fieldˣ}
    (hγ : ExactWitness F eC ε v a ψ γ) (γ' : (baseExtension F).fieldˣ) :
    ExactWitness F eC ε v a ψ γ' ↔
      γ' * γ⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits ⌈a / 2⌉₊ :=
  (exactWitness_coset hε hγ).trans
    (exactWitness_zero_iff F hthr hreal hinert hcmp eC he hε ha ψ _)

/-- The coset clause at the index of the target: for a system and an input
with positive constituent labels, at `a = minimumBreak F v hv`. -/
theorem exactWitness_iff_mem_coset_of_isSystem
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (hgeo : CommonClosureGeometricStatement.{uF, uF})
    {eC : ReciprocityFamily F} {ε : Assignment.{uF, uV} F} (hsys : IsSystem F eC ε)
    {ψ : AdditiveCharacter F (baseExtension F)}
    {v : LocalWeil.Lattice.{uF, max uF uV} F} (hv : (breakSupport F v).Nonempty)
    (hpos : PositiveBreakSupport F v) {γ : (baseExtension F).fieldˣ}
    (hγ : ExactWitness F eC ε v (minimumBreak F v hv) ψ γ)
    (γ' : (baseExtension F).fieldˣ) :
    ExactWitness F eC ε v (minimumBreak F v hv) ψ γ' ↔
      γ' * γ⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits ⌈minimumBreak F v hv / 2⌉₊ :=
  exactWitness_iff_mem_coset F hthr hreal hinert hcmp eC
    (geometric_baseReciprocityCandidate F hgeo eC hsys.1) hsys.2.1
    ((positiveBreakSupport_iff_minimumBreak_pos F v hv).mp hpos) hγ γ'

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
