import Langlands.GroupScheme.Rational.MaximalLeviParabolicCountStatement
import Langlands.GroupScheme.Rational.MaximalLeviConeComplementProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.Representation.Exponents.MaximalLeviFixedDirectionNormalizer

/-! # Counting the parabolics with a specified maximal Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace MaximalLeviConeComplementLine

/-- The upper bound for actual parabolics with a common embedded maximal Levi,
from the two possible signs on its central-annihilator line. -/
theorem maximalLeviParabolicCount_core : MaximalLeviParabolicCountStatement.{u} := by
  classical
  intro k _ G hG P M p l hp hl hproper hmax n Q q lQ hq hlQ hcomp hinj
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨R⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  obtain ⟨x, hx⟩ := R.restrictedRoots_nonempty hG
    (range_comp_ne_top_of_not_isIso hp.isClosedSubgroup hproper l)
  have hxpos := R.splitComponentEvaluation_pos_of_mem_restrictedRoots hx
  have hx0 : x ≠ 0 := by
    intro he
    rw [he, map_zero] at hxpos
    exact lt_irrefl 0 hxpos
  have hxcent : ∀ ν : cocharacterLattice A,
      IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
      pair A x ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0 := by
    intro ν hν
    obtain ⟨α, hα, _, rfl⟩ := R.mem_restrictedRoots.mp hx
    rw [pair_one_tmul_one_tmul,
      latticePairing_restrict_eq_zero_of_isCentral R.data.i R.data.f
        R.isCompatible.factor_comp
        (positiveRelativeRoots_subset_relativeRoots _ _
          (simpleRelativeRoots_subset_positive _ _ hα)) hν,
      Int.cast_zero]
  let S (i : Fin n) : ParabolicRootPresentation (q i) (lQ i) a :=
    Classical.choice (parabolicRootPresentationExistence k G hG (Q i) M A
      (q i) (lQ i) a (hq i) (hlQ i) ha)
  have hsame (i j : Fin n) (y : Vstar A) (hy : y ≠ 0)
      (hycent : ∀ ν : cocharacterLattice A,
        IsCentral (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) →
        pair A y ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0)
      (hi : y ∉ (S i).positiveCone) (hj : y ∉ (S j).positiveCone) : i = j := by
    obtain ⟨U₁, r₁, hr₁, _⟩ := (hlQ i).exists_unipotentRadical
    obtain ⟨U₂, r₂, hr₂, _⟩ := (hlQ j).exists_unipotentRadical
    exact hinj (maximalLeviConeComplement k G hG P M A p l a hp hl hproper hmax ha
      y hy hycent (Q i) U₁ (Q j) U₂ (q i) (lQ i) r₁ (q j) (lQ j) r₂ hr₁ hr₂
      (hcomp i) (hcomp j) (S i) (S j) hi hj).1
  let sign : Fin n → Bool := fun i => decide (x ∈ (S i).positiveCone)
  have hsign : Function.Injective sign := by
    intro i j he
    by_cases hi : x ∈ (S i).positiveCone
    · have hj : x ∈ (S j).positiveCone := by
        have he' : decide (x ∈ (S i).positiveCone) = decide (x ∈ (S j).positiveCone) := he
        simpa [hi] using he'.symm
      apply hsame i j (-x) (neg_ne_zero.mpr hx0)
      · intro ν hν
        rw [map_neg, LinearMap.neg_apply, hxcent ν hν, neg_zero]
      · exact ((S i).notMem_positiveCone_or_neg_notMem hx0).resolve_left (not_not.mpr hi)
      · exact ((S j).notMem_positiveCone_or_neg_notMem hx0).resolve_left (not_not.mpr hj)
    · have hj : x ∉ (S j).positiveCone := by
        have he' : decide (x ∈ (S i).positiveCone) = decide (x ∈ (S j).positiveCone) := he
        simpa [hi] using he'.symm
      exact hsame i j x hx0 hxcent hi hj
  simpa only [Fintype.card_fin, Fintype.card_bool] using Fintype.card_le_of_injective sign hsign

end Langlands.GroupScheme
