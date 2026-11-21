import Langlands.Global.RankinSelberg.ComplexBruhatSectionLocality
import Langlands.Global.RankinSelberg.ComplexBruhatCellVanishing
import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Mathlib.Order.Preorder.Finite

/-! # Injectivity of restriction to the open complex Bruhat cell -/

noncomputable section

open Set TopologicalSpace
open scoped Classical Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatRestriction

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.GeneralLinear (upperUnipotent upperBruhatCell upperBruhatCellNeighborhood
  isOpen_upperBruhatCellNeighborhood exists_mem_upperBruhatCell mul_mem_upperBruhatCell
  permutationInversionCount permutationInversionCount_eq_card)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (chartDomain chartCoordinates chartSection cellCoordinates
  continuous_chartSection complexBruhatGaussChart)
open ComplexBruhatTestExtension (ChartTest chartSaturation mem_chartSaturation extendTest tsupport_extendTest_subset)
open ComplexBruhatSectionLocality (IsBorelSaturated IsVanishingOnSections chartSaturation_preimage_section
  complexBruhatSectionLocality)
open ComplexBruhatChartDerivative (complexBruhatChartDerivative)
open ComplexBruhatCellVanishing (complexBruhatCellVanishing)
open ComplexWhittakerSmoothExtension (SmoothStandard compactProfile)
open ComplexWhittakerTranslateExtension (smoothTranslate)
open ComplexCompactSmoothDifferences (CompactProfileDifferenceBound)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ

private theorem eq_revPerm_of_strictAnti {n : ℕ} (w : Equiv.Perm (Fin n)) (hw : StrictAnti w) :
    w = Fin.revPerm := by
  have hm : StrictMono (fun i : Fin n => (w i).rev) := fun _ _ hij => Fin.rev_strictAnti (hw hij)
  apply Equiv.ext
  intro i
  have h : (w i).rev = i := congrFun hm.eq_id i
  simpa only [Fin.rev_rev, Fin.revPerm_apply] using congrArg Fin.rev h

private theorem isBorelSaturated_cellNeighborhood {n : ℕ} (w : Equiv.Perm (Fin n)) :
    IsBorelSaturated (upperBruhatCellNeighborhood n ℂ w) := by
  intro b g hg
  rcases hg with hg | ⟨v, hv, hg⟩
  · exact Or.inl (mul_mem_upperBruhatCell n ℂ w b hg)
  · exact Or.inr ⟨v, hv, mul_mem_upperBruhatCell n ℂ v b hg⟩

/-- An exact smooth Whittaker functional with a finite compact difference bound
is zero if its restriction to the open Bruhat chart is zero. -/
def ComplexBruhatRestrictionStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (L : SmoothStandard (r + 1) ds →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ), 0 ≤ C →
    (∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R) →
    (∀ F (u : G (r + 1)), u ∈ N (r + 1) → L (smoothTranslate u F) = complexWhittakerCharacter a u * L F) →
    (∀ φ : ChartTest (r + 1), L (extendTest Fin.revPerm ds φ) = 0) → L = 0

set_option maxHeartbeats 1300000 in
theorem complexBruhatRestriction : ComplexBruhatRestrictionStatement := by
  intro r ds a L J C hC hL hCov hLong
  let n := r + 1
  let region (k : ℕ) : Set (G n) :=
    {g | ∃ w : Equiv.Perm (Fin n), k ≤ permutationInversionCount n w ∧ g ∈ upperBruhatCell n ℂ w}
  have hStep (k : ℕ) (ih : IsVanishingOnSections L (region (k + 1))) :
      IsVanishingOnSections L (region k) := by
    apply complexBruhatSectionLocality n ds L (region k)
    intro g hg
    obtain ⟨w, hwk, hgw⟩ := hg
    let V := upperBruhatCellNeighborhood n ℂ w
    let O : Opens (Coordinates n) := ⟨chartSection w ⁻¹' V,
      (isOpen_upperBruhatCellNeighborhood (K := ℂ) w).preimage (continuous_chartSection w)⟩
    have hSat : chartSaturation w (O : Set (Coordinates n)) = chartDomain w ∩ V :=
      chartSaturation_preimage_section w (isBorelSaturated_cellNeighborhood w)
    refine ⟨w, O, O.isOpen, ?_, ?_⟩
    · rw [hSat]
      exact ⟨((complexBruhatGaussChart n w).2.2 g).mp hgw |>.1, Or.inl hgw⟩
    · intro φ hφ
      by_cases hw : StrictAnti w
      · simpa only [eq_revPerm_of_strictAnti w hw] using hLong φ
      · obtain ⟨T, hT, hD⟩ := complexBruhatChartDerivative r ds a w L J C hC hL hCov
        have hOff : Distribution.IsVanishingOn (⇑T) ((O : Set (Coordinates n)) \ cellCoordinates w) := by
          intro ψ hψ
          rw [hT]
          apply ih
          intro x hx
          have hxS := tsupport_extendTest_subset w ds ψ hx
          obtain ⟨hxD, hxz⟩ := (mem_chartSaturation w (tsupport ψ) x).mp hxS
          have hxO := hψ hxz
          have hxV : x ∈ V := by
            have hxSat := (mem_chartSaturation w (O : Set (Coordinates n)) x).mpr ⟨hxD, hxO.1⟩
            rw [hSat] at hxSat
            exact hxSat.2
          rcases hxV with hxCell | ⟨v, hv, hxCell⟩
          · exact False.elim (hxO.2 (((complexBruhatGaussChart n w).2.2 x).mp hxCell).2)
          · exact ⟨v, Nat.succ_le_of_lt (lt_of_le_of_lt hwk hv), hxCell⟩
        calc
          L (extendTest w ds φ) = T φ := (hT φ).symm
          _ = 0 := complexBruhatCellVanishing r ds a w hw T hD O hOff φ hφ
  let M := (Finset.univ : Finset (Fin n × Fin n)).card
  have hBound (w : Equiv.Perm (Fin n)) : permutationInversionCount n w ≤ M := by
    rw [permutationInversionCount_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hBase : IsVanishingOnSections L (region (M + 1)) := by
    intro F hF
    have hZero : F = 0 := by
      apply Subtype.ext
      funext g
      change F.val g = 0
      by_contra h
      obtain ⟨w, hw, _⟩ := hF (subset_tsupport _ h)
      exact Nat.not_succ_le_self M (hw.trans (hBound w))
    rw [hZero, map_zero]
  have hAll (k : ℕ) (hk : k ≤ M + 1) : IsVanishingOnSections L (region k) := by
    exact Nat.decreasingInduction (motive := fun j _ => IsVanishingOnSections L (region j))
      (fun j _ ih => hStep j ih) hBase hk
  ext F
  change L F = 0
  apply hAll 0 (Nat.zero_le _)
  intro g _
  obtain ⟨w, hw⟩ := exists_mem_upperBruhatCell g
  exact ⟨w, Nat.zero_le _, hw⟩

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatRestriction
