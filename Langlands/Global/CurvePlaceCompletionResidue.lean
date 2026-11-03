import Langlands.Global.CurvePlaceAdeleDiagonal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Actual curve-place residue fields and completion -/

noncomputable section

universe u

open IsDedekindDomain
open scoped Topology Valued

namespace Langlands.Global

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
  (v : AlgebraicCurve.Place k F)

/-- The actual valuation ring maps to the valuation ring of its completion. -/
abbrev curvePlaceIntegersMap :
    v.toValuationSubring →+* curvePlaceCompletionIntegers v :=
  algebraMap _ _

@[simp]
theorem curvePlaceIntegersMap_coe (a : v.toValuationSubring) :
    (curvePlaceIntegersMap v a : curvePlaceCompletion v) =
      algebraMap F (curvePlaceCompletion v) (a : F) := rfl

theorem curvePlaceCompletion_mem_maximalIdeal_iff (x : curvePlaceCompletionIntegers v) :
    x ∈ IsLocalRing.maximalIdeal (curvePlaceCompletionIntegers v) ↔
      Valued.v (x : curvePlaceCompletion v) < 1 :=
  Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (curvePlaceCompletion v) (WithZero (Multiplicative ℤ))))

/-- Reduction of the original valuation ring in the completed residue field. -/
def curvePlaceCompletionResidueMap :
    v.toValuationSubring →+* IsLocalRing.ResidueField (curvePlaceCompletionIntegers v) :=
  (IsLocalRing.residue _).comp (curvePlaceIntegersMap v)

@[simp]
theorem curvePlaceCompletionResidueMap_eq_zero_iff (a : v.toValuationSubring) :
    curvePlaceCompletionResidueMap v a = 0 ↔
      a ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [curvePlaceCompletionResidueMap, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff,
    curvePlaceCompletion_mem_maximalIdeal_iff]
  change Valued.v (algebraMap F (curvePlaceCompletion v) (a : F)) < 1 ↔ _
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.heightOneSpectrum.valuation_lt_one_iff_mem a

theorem curvePlaceCompletionResidueMap_ker :
    RingHom.ker (curvePlaceCompletionResidueMap v) =
      IsLocalRing.maximalIdeal v.toValuationSubring := by
  ext a
  exact curvePlaceCompletionResidueMap_eq_zero_iff v a

/-- Every completed integer is congruent to an actual integer modulo the
completed maximal ideal. -/
theorem curvePlace_exists_integer_sub_lt_one (x : curvePlaceCompletionIntegers v) :
    ∃ a : v.toValuationSubring,
      Valued.v (algebraMap F (curvePlaceCompletion v) (a : F) -
        (x : curvePlaceCompletion v)) < 1 := by
  have hball : {y : curvePlaceCompletion v |
      Valued.v (y - (x : curvePlaceCompletion v)) < 1} ∈
        𝓝 (x : curvePlaceCompletion v) := by
    apply Valued.mem_nhds.mpr
    refine ⟨1, ?_⟩
    intro y hy
    simpa only [Units.val_one, Valuation.restrict_lt_one_iff] using hy
  obtain ⟨b, hb⟩ := (v.heightOneSpectrum.denseRange_algebraMap F).mem_nhds hball
  have hbx : Valued.v (algebraMap F (curvePlaceCompletion v) b) ≤ 1 := by
    have h := Valued.v.map_add
      (algebraMap F (curvePlaceCompletion v) b - (x : curvePlaceCompletion v))
      (x : curvePlaceCompletion v)
    rw [sub_add_cancel] at h
    exact h.trans (max_le hb.le x.property)
  have hbO : b ∈ v.toValuationSubring :=
    (curvePlaceCompletion_mem_integers_iff v b).mp hbx
  exact ⟨⟨b, hbO⟩, hb⟩

/-- The reduction map onto the completed residue field is surjective. -/
theorem curvePlaceCompletionResidueMap_surjective :
    Function.Surjective (curvePlaceCompletionResidueMap v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := curvePlace_exists_integer_sub_lt_one v x
  refine ⟨a, ?_⟩
  change IsLocalRing.residue (curvePlaceCompletionIntegers v) (curvePlaceIntegersMap v a) =
    IsLocalRing.residue (curvePlaceCompletionIntegers v) x
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff,
    curvePlaceCompletion_mem_maximalIdeal_iff]
  exact ha

/-- The canonical residue-field equivalence induced by completion. -/
def curvePlaceCompletionResidueEquiv :
    v.ResidueField ≃+* IsLocalRing.ResidueField (curvePlaceCompletionIntegers v) :=
  (Ideal.quotEquivOfEq (curvePlaceCompletionResidueMap_ker v).symm).trans
    ((curvePlaceCompletionResidueMap v).quotientKerEquivOfSurjective
      (curvePlaceCompletionResidueMap_surjective v))

@[simp]
theorem curvePlaceCompletionResidueEquiv_residue (a : v.toValuationSubring) :
    curvePlaceCompletionResidueEquiv v (IsLocalRing.residue v.toValuationSubring a) =
      IsLocalRing.residue (curvePlaceCompletionIntegers v) (curvePlaceIntegersMap v a) := rfl

end Langlands.Global
