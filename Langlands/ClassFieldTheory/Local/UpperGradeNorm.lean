import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityProof
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof
import Langlands.LocalFactor.DeligneHenniartIntermediateGeometricProof
import Langlands.LocalFactor.DeligneHenniartInductionStep
import Langlands.LocalFactor.Ramification.Herbrand.ConvexityProof

/-! # Norms of the successive unit subgroups above the relative breaks -/

noncomputable section

namespace Langlands.LocalClassField.UpperGradeNorm

open Correspondence LocalFactor LocalFactor.CommonClosure Weil.Local
open VirtualRepresentation.LocalWeil.Ramification Ramification.HerbrandBridge
open LocalFactor.NonabelianSystem.DeligneHenniart

universe u
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p) (E : Extension K)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : TopologicalSpace (Correspondence.baseExtension K).field :=
  (fieldData K (Correspondence.baseExtension K)).topology
local instance : TopologicalSpace E.field := (fieldData K E).topology

private theorem baseExtension_le : (Correspondence.baseExtension K).field ≤ E.field := by
  change ⊥ ≤ E.field
  exact bot_le

/-- The field norm from an actual finite intermediate field to the base field,
read through the unit identification of the bottom field. -/
def normToBaseUnits : E.fieldˣ →* K.Carrierˣ :=
  (baseFieldUnitsEquiv K).toMonoidHom.comp
    ((Correspondence.baseExtension K).unitsNorm E (baseExtension_le K E))

/-- The norm square on actual Weil elements at the base. -/
theorem normToBaseUnits_reciprocityUnits (eC : ReciprocityFamily K) (heC : NormalizedReciprocity K eC)
    (w : weilSubgroup K E) :
    normToBaseUnits K E (reciprocityUnits K eC E w) =
      RankOne.reciprocityUnits K (baseReciprocityCandidate K eC) w.val := by
  let B := Correspondence.baseExtension K
  let wB := weilInclusion K B E (baseExtension_le K E) w
  have h := reciprocityUnits_weilInclusion K heC B E (baseExtension_le K E) w
  exact (congrArg (baseFieldUnitsEquiv K) h.symm).trans
    (baseFieldUnitsEquiv_reciprocityUnits K eC wB)

/-- The carried upper group is precisely the restriction to the fixing Weil
subgroup of the base upper group with corresponding index. -/
theorem mem_intermediateUpperGroup_relativeHerbrandPsi_iff {s : ℝ} (hs : -1 ≤ s)
    (w : weilSubgroup K E) :
    w ∈ intermediateUpperGroup K E (relativeHerbrandPsi E s) ↔ w.val ∈ upperGroup K s := by
  rw [mem_intermediateUpperGroup, ← intermediateWeilEquiv_mem_upperGroup_iff E hs,
    ContinuousMulEquiv.apply_symm_apply]

/-- If the base upper group already fixes `E`, the norm maps the unit level
of the corresponding relative index onto the base unit level. -/
theorem normToBaseUnits_map_unitFiltration (eC : ReciprocityFamily K) (heC : NormalizedReciprocity K eC)
    {s : ℝ} (hs : 0 ≤ s) (hfix : upperGroup K s ≤ weilSubgroup K E) :
    ((fieldData K E).unitFiltration ⌈relativeHerbrandPsi E s⌉₊).map (normToBaseUnits K E) =
      K.canonicalTopologicalData.unitFiltration ⌈s⌉₊ := by
  let e := baseReciprocityCandidate K eC
  have he := geometric_baseReciprocityCandidate K commonClosureGeometricProof eC heC
  have hK := upperGroup_map_reciprocityUnits K absoluteUpperReciprocityTheorems.2.2.1
    (absoluteUpperInertia K _) e he hs
  have hE := intermediateUpperGroup_map_reciprocityUnits K absoluteUpperReciprocityTheorems.2.2.1
    unitFiltrationComparison eC E (absoluteUpperInertia _ _)
    (intermediateGeometricProof p K eC heC E) (relativeHerbrandPsi_nonneg E hs)
  rw [← (fieldData K E).unitFiltration_eq_principalUnits] at hE
  rw [← hE, Subgroup.map_map, ← hK]
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.val, (mem_intermediateUpperGroup_relativeHerbrandPsi_iff K E (by linarith) w).mp hw,
      (normToBaseUnits_reciprocityUnits K E eC heC w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    let v : weilSubgroup K E := ⟨w, hfix hw⟩
    exact ⟨v, (mem_intermediateUpperGroup_relativeHerbrandPsi_iff K E (by linarith) v).mpr hw,
      normToBaseUnits_reciprocityUnits K E eC heC v⟩

private theorem unitFiltration_ne_succ {l : ℕ} (hl : 0 < l) :
    K.canonicalTopologicalData.unitFiltration l ≠ K.canonicalTopologicalData.unitFiltration (l + 1) := by
  let T := K.canonicalTopologicalData
  let e := T.gradedUnitsPositiveEquiv T.uniformizer T.ord_uniformizer l hl
  obtain ⟨x, hx⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (Multiplicative.ofAdd (1 : T.ResidueField))
  intro heq
  have h : T.gradedUnitProjection l x = 1 := (QuotientGroup.eq_one_iff x).mpr (heq.le x.property)
  change e (T.gradedUnitProjection l x) = Multiplicative.ofAdd (1 : T.ResidueField) at hx
  rw [h, map_one] at hx
  exact one_ne_zero (congrArg Multiplicative.toAdd hx).symm

/-- Once the upper group at a positive integral level is in the fixing
subgroup, moving slightly to the right advances both ceiling levels by one. -/
theorem exists_next_ceiling_levels (eC : ReciprocityFamily K) (heC : NormalizedReciprocity K eC)
    {l : ℕ} (hl : 0 < l) (hfix : upperGroup K l ≤ weilSubgroup K E) :
    ∃ b : ℝ, (l : ℝ) < b ∧ ⌈b⌉₊ = l + 1 ∧
      ⌈relativeHerbrandPsi E b⌉₊ = ⌈relativeHerbrandPsi E l⌉₊ + 1 := by
  let m := ⌈relativeHerbrandPsi E (l : ℝ)⌉₊
  have hmargin : relativeHerbrandPsi E l < ((m + 1 : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_succ_self m)
  have hev : ∀ᶠ b in nhds (l : ℝ), relativeHerbrandPsi E b < ((m + 1 : ℕ) : ℝ) :=
    ((relativeHerbrandPsi_continuous E).tendsto _).eventually (gt_mem_nhds hmargin)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let b := (l : ℝ) + ε
  have hb : (l : ℝ) < b := lt_add_of_pos_right _ hε
  have hbceil : ⌈b⌉₊ = l + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero l)).mpr
    rw [Nat.succ_sub_one]
    exact ⟨hb, by push_cast; dsimp [b]; linarith⟩
  have hbψ : relativeHerbrandPsi E b < ((m + 1 : ℕ) : ℝ) := by
    apply hball
    rw [Real.dist_eq, show b - (l : ℝ) = ε by dsimp [b]; ring, abs_of_pos hε]
    exact hεδ
  have hlo : m ≤ ⌈relativeHerbrandPsi E b⌉₊ :=
    Nat.ceil_mono ((relativeHerbrandPsi_strictMono E).monotone hb.le)
  have hhi : ⌈relativeHerbrandPsi E b⌉₊ ≤ m + 1 := Nat.ceil_le.mpr hbψ.le
  refine ⟨b, hb, hbceil, ?_⟩
  by_contra hne
  have heq : ⌈relativeHerbrandPsi E b⌉₊ = m := by omega
  have h0 := normToBaseUnits_map_unitFiltration K E eC heC (Nat.cast_nonneg l) hfix
  have h1 := normToBaseUnits_map_unitFiltration K E eC heC ((Nat.cast_nonneg l).trans hb.le)
    ((upperGroup_antitone K hb.le).trans hfix)
  rw [Nat.ceil_natCast] at h0
  rw [heq, hbceil] at h1
  exact unitFiltration_ne_succ K hl (h0.symm.trans h1)

section Graded

variable {l m : ℕ}
variable (h0 : ((fieldData K E).unitFiltration m).map (normToBaseUnits K E) =
  K.canonicalTopologicalData.unitFiltration l)
variable (h1 : ((fieldData K E).unitFiltration (m + 1)).map (normToBaseUnits K E) =
  K.canonicalTopologicalData.unitFiltration (l + 1))

/-- Restriction of the norm to the specified unit levels. -/
def normUnitLevel : (fieldData K E).unitFiltration m →* K.canonicalTopologicalData.unitFiltration l :=
  ((normToBaseUnits K E).comp ((fieldData K E).unitFiltration m).subtype).codRestrict _
    (fun x => h0.le (Subgroup.mem_map_of_mem _ x.property))

theorem normUnitLevel_surjective : Function.Surjective (normUnitLevel K E h0) := by
  intro y
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.mp (h0.ge y.property)
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- A norm mapping the two specified adjacent subgroups onto their counterparts
induces a homomorphism on the actual successive unit quotients. -/
def normUnitGrade : (fieldData K E).GradedUnits m →* K.canonicalTopologicalData.GradedUnits l :=
  QuotientGroup.lift _ ((K.canonicalTopologicalData.gradedUnitProjection l).comp
    (normUnitLevel K E h0)) (by
      intro x hx
      apply (QuotientGroup.eq_one_iff (normUnitLevel K E h0 x)).mpr
      exact h1.le (Subgroup.mem_map_of_mem _ hx))

@[simp] theorem normUnitGrade_projection (x : (fieldData K E).unitFiltration m) :
    normUnitGrade K E h0 h1 ((fieldData K E).gradedUnitProjection m x) =
      K.canonicalTopologicalData.gradedUnitProjection l (normUnitLevel K E h0 x) := rfl

theorem normUnitGrade_surjective : Function.Surjective (normUnitGrade K E h0 h1) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.canonicalTopologicalData.gradedUnitKernel l) y
  obtain ⟨x, hx⟩ := normUnitLevel_surjective K E h0 y
  exact ⟨(fieldData K E).gradedUnitProjection m x,
    congrArg (K.canonicalTopologicalData.gradedUnitProjection l) hx⟩

end Graded

end Langlands.LocalClassField.UpperGradeNorm
