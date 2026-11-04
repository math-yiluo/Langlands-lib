import Langlands.Representation.Aubert.General.RationalPositiveCartanCoverStatement
import Langlands.Representation.Aubert.General.RationalIwasawaCartan
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation

/-! # The same-subgroup finite Cartan covering adapter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.Cartan Langlands.Plancherel.RenardCartan

namespace Langlands.Aubert.General.RationalPointFamily

/-- The actual positive-product cover supplies the finite covering used by
cuspidal compactness, without changing the geometric compact subgroup. -/
theorem rationalPositiveCartanCover : RationalPositiveCartanCoverStatement.{u} := by
  intro F _ _ _ _ G _ S i _ ν D x Z j s h hrep hsj hcomp
  classical
  let emb : rationalPoints Z → centralizerPoints i := fun z =>
    ⟨rationalPoints.map j z, by
      rw [← torusCentralizer_carrier_base]
      exact (hrep.pointsEquiv (Over.mk (𝟙 _)) z).property⟩
  obtain ⟨Fcover, hFcover⟩ := hcomp.2.2.2.2.2.2.1
  refine ⟨hFcover.1.toFinset.image emb, fun g => ?_⟩
  obtain ⟨z, hz⟩ := hcomp.1.1 g
  obtain ⟨t, ht, htz⟩ := hFcover.2.2.2
    (show (Langlands.Plancherel.rationalCharacterValuation Z).rangeRestrict z.val ∈
      (Langlands.Plancherel.rationalCharacterValuation Z).rangeRestrict ''
        dominantCentralizer i ν s h from ⟨z.val, z.property, rfl⟩)
  have htdom := hFcover.2.2.1 ht
  have hrel := (specialCompactSetoid_iff_characterValue_eq D x ν j s h hcomp.1.2
    ⟨t, htdom⟩ z).mpr (congrArg Subtype.val htz)
  obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := DoubleCoset.eq.mp (hrel.trans hz)
  obtain ⟨c, hc, f, hf, rfl⟩ := ht
  obtain ⟨cchar, hcchar, rfl⟩ := (mem_C0Plus S s (positiveRelativeRoots i ν) c).mp hc
  let a := uniformizerSection S (Multiplicative.ofAdd cchar)
  have ha : a ∈ CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν) := by
    refine ⟨⟨Multiplicative.ofAdd cchar, rfl⟩, fun α hα => ?_⟩
    change CocharacterUniformizer.characterNorm F S α
      (CocharacterUniformizer.latticeSection F S (Multiplicative.ofAdd cchar)) ≤ 1
    rw [CocharacterUniformizer.characterNorm_latticeSection]
    have hq : (1 : ℝ) < LocalField.residueCardinality F := by
      exact_mod_cast LocalField.residueCardinality_gt_one F
    exact (zpow_le_one_iff_right₀ hq).mpr
      (neg_nonpos.mpr (hcchar α (simpleRelativeRoots_subset_positive i ν hα)))
  have hcomm : Commute (rationalPoints.map j f) (rationalPoints.map i a) := by
    have hfcentral := (hrep.pointsEquiv (Over.mk (𝟙 _)) f).property
    have hc := hfcentral (Over.mk (𝟙 _)) (𝟙 _) a
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe, Category.id_comp,
      rationalPoints.map_apply] using hc
  refine ⟨k₁, k₂, emb f, a, hk₁, hk₂,
    Finset.mem_image.mpr ⟨f, hFcover.1.mem_toFinset.mpr hf, rfl⟩, ha, ?_⟩
  have hmap : rationalPoints.map j (rationalPoints.map s a) = rationalPoints.map i a := by
    rw [← rationalPoints_map_comp_apply, hsj]
  change g = k₁ * rationalPoints.map j f * rationalPoints.map i a * k₂
  calc
    g = k₁ * (rationalPoints.map j (rationalPoints.map s a) *
        rationalPoints.map j f) * k₂ := by simpa only [map_mul] using hg
    _ = k₁ * (rationalPoints.map i a * rationalPoints.map j f) * k₂ := by rw [hmap]
    _ = k₁ * rationalPoints.map j f * rationalPoints.map i a * k₂ := by
      rw [← hcomm.eq]
      simp only [mul_assoc]

end Langlands.Aubert.General.RationalPointFamily
