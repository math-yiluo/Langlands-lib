import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure
import Langlands.Group.HaarModulus
import Langlands.BruhatTits.SpecialCompact.ContractionPredicates

/-! # The finite index of a contracted compact open subgroup -/

noncomputable section

universe u

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace Langlands.HarishChandraSchwartz

variable {U : Type u} [Group U] [TopologicalSpace U] [IsTopologicalGroup U]
  [LocallyCompactSpace U]

local instance : MeasurableSpace U := borel U
local instance : BorelSpace U := ⟨rfl⟩

/-- The index of a compact open subgroup's contracted image is the inverse
of the actual Haar modulus of the automorphism. -/
theorem contractedOpenSubgroup_relIndex (Y : OpenSubgroup U)
    (hY : IsCompact (Y : Set U)) (φ : U ≃ₜ* U)
    (hφ : Y.toSubgroup.map φ.toMonoidHom ≤ Y.toSubgroup) :
    (Y.toSubgroup.map φ.toMonoidHom).relIndex Y.toSubgroup ≠ 0 ∧
      ((Y.toSubgroup.map φ.toMonoidHom).relIndex Y.toSubgroup : ℝ) =
        (mulEquivHaarChar φ : ℝ)⁻¹ := by
  let Z := Y.toSubgroup.map φ.toMonoidHom
  have hZ : IsOpen (Z : Set U) := φ.toHomeomorph.isOpenMap _ Y.isOpen
  have hfin : Z.relIndex Y.toSubgroup ≠ 0 := by
    let : CompactSpace Y := isCompact_iff_compactSpace.mp hY
    have := Subgroup.quotient_finite_of_isOpen (Z.subgroupOf Y.toSubgroup)
      (Subgroup.subgroupOf_isOpen Y.toSubgroup Z hZ)
    let : (Z.subgroupOf Y.toSubgroup).FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    exact Subgroup.FiniteIndex.index_ne_zero
  refine ⟨hfin, ?_⟩
  let C : TopologicalSpace.PositiveCompacts U :=
    ⟨⟨(Y : Set U), hY⟩, by simpa only [Y.isOpen.interior_eq] using
      (show (Y : Set U).Nonempty from ⟨1, Y.one_mem⟩)⟩
  let μ := Measure.haarMeasure C
  have hμY : μ (Y : Set U) = 1 := Measure.haarMeasure_self
  have hpre : φ ⁻¹' (Z : Set U) = Y := by
    change φ ⁻¹' (φ '' (Y : Set U)) = Y
    exact Set.preimage_image_eq _ φ.injective
  have hscale := mulEquivHaarChar_smul_preimage μ (X := (Z : Set U)) φ
  rw [hpre, hμY] at hscale
  simp only [ENNReal.smul_def, smul_eq_mul, mul_one] at hscale
  have hmeasure := measure_eq_relIndex_mul μ hφ hZ.measurableSet hfin
  change μ (Y : Set U) = (Z.relIndex Y.toSubgroup : ℝ≥0∞) * μ (Z : Set U) at hmeasure
  have hprod : (Z.relIndex Y.toSubgroup : ℝ≥0∞) * (mulEquivHaarChar φ : ℝ≥0∞) = 1 := by
    rw [hscale, ← hmeasure, hμY]
  have hprodR := congrArg ENNReal.toReal hprod
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal,
    ENNReal.toReal_one] at hprodR
  exact (mul_eq_one_iff_eq_inv₀ (by exact_mod_cast (mulEquivHaarChar_pos φ).ne')).mp hprodR

section Ambient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- The intrinsic contracted index equals the relative index of the literal
ambient intersection and its actual conjugate. -/
theorem contractedIntersection_relIndex (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (U : Subgroup G) (hU : IsClosed (U : Set G))
    (g : Subgroup.normalizer (U : Set G))
    (hc : BruhatTits.SpecialCompact.ambientConjugate (g : G)
      ((K.toSubgroup ⊓ U : Subgroup G) : Set G) ⊆
        ((K.toSubgroup ⊓ U : Subgroup G) : Set G)) :
    (conjSubgroup (g : G) (K.toSubgroup ⊓ U)).relIndex (K.toSubgroup ⊓ U) ≠ 0 ∧
      ((conjSubgroup (g : G) (K.toSubgroup ⊓ U)).relIndex (K.toSubgroup ⊓ U) : ℝ) =
        ((HaarModulus.closedNormalizerCharacter U hU g : ℝ≥0) : ℝ)⁻¹ := by
  let := hU.locallyCompactSpace
  let Y : OpenSubgroup U := K.comap U.subtype continuous_subtype_val
  let φ := HaarModulus.normalizerConj U g
  have hY : IsCompact (Y : Set U) :=
    hU.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hK
  have hφ : Y.toSubgroup.map φ.toMonoidHom ≤ Y.toSubgroup := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hc ⟨u, ⟨hu, u.property⟩, rfl⟩).1
  have hYm : Y.toSubgroup.map U.subtype = K.toSubgroup ⊓ U := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.property⟩
    · rintro ⟨hxK, hxU⟩
      exact ⟨⟨x, hxU⟩, hxK, rfl⟩
  have hZm : (Y.toSubgroup.map φ.toMonoidHom).map U.subtype =
      conjSubgroup (g : G) (K.toSubgroup ⊓ U) := by
    ext x
    constructor
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      apply mem_conjSubgroup.mpr
      change (g : G)⁻¹ * ((g : G) * (u : G) * (g : G)⁻¹) * g ∈ K.toSubgroup ⊓ U
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
        (show (u : G) ∈ K.toSubgroup ⊓ U from ⟨hu, u.property⟩)
    · intro hx
      have hx' := mem_conjSubgroup.mp hx
      refine ⟨φ ⟨(g : G)⁻¹ * x * g, hx'.2⟩,
        ⟨⟨(g : G)⁻¹ * x * g, hx'.2⟩, hx'.1, rfl⟩, ?_⟩
      simp [φ, HaarModulus.normalizerConj_apply, mul_assoc]
  have heq := Subgroup.relIndex_map_map_of_injective
    (Y.toSubgroup.map φ.toMonoidHom) Y.toSubgroup U.subtype_injective
  rw [hYm, hZm] at heq
  rw [heq]
  exact contractedOpenSubgroup_relIndex Y hY φ hφ

end Ambient

end Langlands.HarishChandraSchwartz
