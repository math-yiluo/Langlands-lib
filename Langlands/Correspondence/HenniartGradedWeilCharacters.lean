import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Langlands.ClassFieldTheory.Local.OpenFiniteIndexSeparationProof
import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityProof
import Langlands.LocalFactor.DeligneHenniartUpperUnits
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof
import Langlands.Topology.ComplexCharacterExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Lifting graded unit characters to the actual Weil group -/

noncomputable section

namespace Langlands.Henniart.Numerical

open LocalClassField LocalFactor Ramification.HerbrandBridge Weil.Local
open VirtualRepresentation.LocalWeil.Ramification
open NonabelianSystem.DeligneHenniart (upperGroup_map_reciprocityUnits)

universe uK
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : IsTopologicalGroup K.Carrierˣ := by
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  infer_instance

/-- The characters of the actual successive unit quotient at level `l`. -/
abbrev GradedUnitCharacters (l : ℕ) := K.canonicalTopologicalData.GradedUnits l →* ℂˣ

/-- The dual of a positive unit grade has cardinality equal to that of the
residue field. -/
theorem card_gradedUnitCharacters {l : ℕ} (hl : 0 < l) :
    ENat.card (GradedUnitCharacters K l) = K.canonicalTopologicalData.residueCardinality := by
  let T := K.canonicalTopologicalData
  let e := T.gradedUnitsPositiveEquiv T.uniformizer T.ord_uniformizer l hl
  let : Finite T.ResidueField := T.finite_residueField
  let : Finite (T.GradedUnits l) := Finite.of_injective e e.injective
  let : NeZero (Monoid.exponent (T.GradedUnits l) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := T.GradedUnits l)⟩
  let : Finite (GradedUnitCharacters K l) := Finite.of_equiv (T.GradedUnits l)
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (T.GradedUnits l) ℂ).some.symm.toEquiv
  rw [ENat.card_eq_coe_natCard,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (T.GradedUnits l) ℂ,
    Nat.card_congr e.toEquiv]
  rfl

/-- Upper-numbering reciprocity onto the actual unit subgroup of the ceiling
level. -/
def upperUnitReciprocity (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e)
    {s : ℝ} (hs : 0 ≤ s) : upperGroup K s →* K.canonicalTopologicalData.unitFiltration ⌈s⌉₊ :=
  ((RankOne.reciprocityUnits K e).toMonoidHom.comp (upperGroup K s).subtype).codRestrict _
    fun w => upperGroup_map_reciprocityUnits K absoluteUpperReciprocityTheorems.2.2.1
      (absoluteUpperInertia K _) e he hs ▸ Subgroup.mem_map_of_mem _ w.property

theorem upperUnitReciprocity_surjective (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e)
    {s : ℝ} (hs : 0 ≤ s) : Function.Surjective (upperUnitReciprocity K e he hs) := by
  intro u
  have h : u.val ∈ (upperGroup K s).map (RankOne.reciprocityUnits K e).toMonoidHom :=
    (upperGroup_map_reciprocityUnits K absoluteUpperReciprocityTheorems.2.2.1
      (absoluteUpperInertia K _) e he hs).ge u.property
  obtain ⟨w, hw, huw⟩ := Subgroup.mem_map.mp h
  exact ⟨⟨w, hw⟩, Subtype.ext huw⟩

/-- At a natural upper index, reciprocity onto the corresponding unit level. -/
def integralUpperUnitReciprocity (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e) (l : ℕ) :
    upperGroup K l →* K.canonicalTopologicalData.unitFiltration l :=
  ((RankOne.reciprocityUnits K e).toMonoidHom.comp (upperGroup K l).subtype).codRestrict _
    fun w => by
      change RankOne.reciprocityUnits K e w.val ∈ K.canonicalTopologicalData.unitFiltration l
      have h : RankOne.reciprocityUnits K e w.val ∈ K.canonicalTopologicalData.unitFiltration
          ⌈(l : ℝ)⌉₊ := (upperUnitReciprocity K e he (s := l) (Nat.cast_nonneg l) w).property
      simpa only [Nat.ceil_natCast] using h

theorem integralUpperUnitReciprocity_surjective (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e) (l : ℕ) :
    Function.Surjective (integralUpperUnitReciprocity K e he l) := by
  intro u
  have heq : (upperGroup K l).map (RankOne.reciprocityUnits K e).toMonoidHom =
      K.canonicalTopologicalData.unitFiltration l := by
    simpa only [Nat.ceil_natCast] using upperGroup_map_reciprocityUnits K
      absoluteUpperReciprocityTheorems.2.2.1 (absoluteUpperInertia K _) e he
      (s := l) (Nat.cast_nonneg l)
  have h : u.val ∈ (upperGroup K l).map (RankOne.reciprocityUnits K e).toMonoidHom :=
    heq.ge u.property
  obtain ⟨w, hw, huw⟩ := Subgroup.mem_map.mp h
  exact ⟨⟨w, hw⟩, Subtype.ext huw⟩

/-- The reciprocity map to the actual successive quotient at an integral index. -/
def upperGradedReciprocity (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e) (l : ℕ) :
    upperGroup K l →* K.canonicalTopologicalData.GradedUnits l :=
  (K.canonicalTopologicalData.gradedUnitProjection l).comp (integralUpperUnitReciprocity K e he l)

theorem upperGradedReciprocity_surjective (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e) (l : ℕ) :
    Function.Surjective (upperGradedReciprocity K e he l) :=
  (QuotientGroup.mk'_surjective _).comp (integralUpperUnitReciprocity_surjective K e he l)

/-- Extend any graded unit character to a continuous character on the whole
multiplicative group, retaining its specified values on the level subgroup. -/
theorem exists_gradedFieldCharacter {l : ℕ} (η : GradedUnitCharacters K l) :
    ∃ χ : K.Carrierˣ →ₜ* ℂˣ, ∀ x : K.canonicalTopologicalData.unitFiltration l,
      χ x = η (K.canonicalTopologicalData.gradedUnitProjection l x) := by
  let T := K.canonicalTopologicalData
  let U := T.unitFiltration l
  let S := T.unitFiltration (l + 1)
  obtain ⟨χ, hχ⟩ := Topology.exists_complex_character_extension U.subtype Subtype.val_injective
    (η.comp (T.gradedUnitProjection l))
  have hx (x : U) : χ x = η (T.gradedUnitProjection l x) := DFunLike.congr_fun hχ x
  have h1 : χ.comp S.subtype = 1 := by
    apply MonoidHom.ext
    intro s
    let x : U := ⟨s.val, T.unitFiltration_antitone (Nat.le_succ _) s.property⟩
    have hs : T.gradedUnitProjection l x = 1 := (QuotientGroup.eq_one_iff x).mpr s.property
    change χ x = 1
    rw [hx x, hs, map_one]
  have hc := Topology.continuous_monoidHom_of_open_subgroup S (T.isOpen_unitFiltration (l + 1)) χ
    (by rw [h1]; exact continuous_const)
  exact ⟨⟨χ, hc⟩, hx⟩

/-- A chosen continuous extension of a graded unit character. No
multiplicativity in the parameter `η` is asserted. -/
def liftGradedCharacterToField {l : ℕ} (η : GradedUnitCharacters K l) :
    K.Carrierˣ →ₜ* ℂˣ := (exists_gradedFieldCharacter K η).choose

theorem liftGradedCharacterToField_apply {l : ℕ} (η : GradedUnitCharacters K l)
    (x : K.canonicalTopologicalData.unitFiltration l) :
    liftGradedCharacterToField K η x = η (K.canonicalTopologicalData.gradedUnitProjection l x) :=
  (exists_gradedFieldCharacter K η).choose_spec x

theorem liftGradedCharacterToField_next {l : ℕ} (η : GradedUnitCharacters K l)
    (u : K.Carrierˣ) (hu : u ∈ K.canonicalTopologicalData.unitFiltration (l + 1)) :
    liftGradedCharacterToField K η u = 1 := by
  let T := K.canonicalTopologicalData
  let x : T.unitFiltration l := ⟨u, T.unitFiltration_antitone (Nat.le_succ _) hu⟩
  have h : T.gradedUnitProjection l x = 1 := (QuotientGroup.eq_one_iff x).mpr hu
  change liftGradedCharacterToField K η x = 1
  rw [liftGradedCharacterToField_apply K, h, map_one]

/-- The chosen extension, transported to the Weil group by reciprocity. -/
def liftGradedCharacterToWeil (e : RankOne.ReciprocityCandidate K)
    {l : ℕ} (η : GradedUnitCharacters K l) : localWeilGroup K →ₜ* ℂˣ :=
  RankOne.weilCharacter K e (liftGradedCharacterToField K η)

theorem liftGradedCharacterToWeil_apply (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e)
    {l : ℕ} (η : GradedUnitCharacters K l) (w : upperGroup K l) :
    liftGradedCharacterToWeil K e η w = η (upperGradedReciprocity K e he l w) :=
  liftGradedCharacterToField_apply K η (integralUpperUnitReciprocity K e he l w)

/-- The chosen lift is trivial on every strictly deeper upper group. -/
theorem liftGradedCharacterToWeil_deeper (e : RankOne.ReciprocityCandidate K)
    (he : GeometricWeilReciprocityRelation K K.canonicalTopologicalData e)
    {l : ℕ} (η : GradedUnitCharacters K l) {s : ℝ} (hs : (l : ℝ) < s)
    (w : localWeilGroup K) (hw : w ∈ upperGroup K s) :
    liftGradedCharacterToWeil K e η w = 1 := by
  have h := (upperUnitReciprocity K e he (s := s) ((Nat.cast_nonneg l).trans hs.le) ⟨w, hw⟩).property
  exact liftGradedCharacterToField_next K η _
    (K.canonicalTopologicalData.unitFiltration_antitone (Nat.lt_ceil.mpr hs) h)

end Langlands.Henniart.Numerical
