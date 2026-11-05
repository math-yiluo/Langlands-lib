import Langlands.Representation.Aubert.General.RationalTorusModularReductionStatement
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.Representation.Aubert.General.SemidirectModularCharacter
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # The ambient modular character on actual torus points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

private theorem mulEquivHaarChar_borel {H : Type*} [Group H] [TopologicalSpace H]
    [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    (β : H ≃ₜ* H) :
    (letI : MeasurableSpace H := borel H
     letI : BorelSpace H := ⟨rfl⟩
     mulEquivHaarChar β) = mulEquivHaarChar β := by
  borelize H
  rfl

set_option maxHeartbeats 800000 in
/-- The explicit structural inputs suffice to trivialize the ambient modular
character on the literal rational-point torus image. -/
theorem rationalTorusModularReduction : RationalTorusModularReductionStatement.{u} := by
  intro hProduct hReciprocity hCentralizer k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard K0 hBasis t ht
  let : MeasurableSpace (RationalPoint k G.X) := borel _
  let : BorelSpace (RationalPoint k G.X) := ⟨rfl⟩
  have hζ : IsStandardCocharacter i ν (rootSet i ν ∅) ν := by
    simpa only [rootSet_empty] using isStandardCocharacter_empty_self i ν
  have hOpp :
      standardOppositeUnipotentPoints i ν ∅ = oppositeUnipotent i ν := by
    change (standardUnipotent i (-ν) (Neg.neg '' ∅)).carrier _ = _
    rw [Set.image_empty]
    have hU := ((hStandard k G hG T i hi (-ν) (hν.neg i ν)
      ∅ (Set.empty_subset _)).2 (-ν) (isStandardCocharacter_empty_self i (-ν))).2.2
    rw [groupHom_neg_comp_eq_oppositeCocharacter] at hU
    rw [hU]
    rfl
  have hLevi : levi i ν ∅ = centralizerPoints i := by
    change (standardLevi i ν (rootSet i ν ∅)).carrier _ = _
    rw [rootSet_empty, standardLevi_empty_of_genericCentralizer i ν
      (hCentralizer k G hG T i hi ν hν), torusCentralizer_carrier_base]
  have hM := isClosed_levi_of_isNonarchimedeanLocalField i ν ∅
  have hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν ∅
  have hV := isClosed_oppositeUnipotent_localField i ν
  have hd := isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν ∅
  have hdOpp := opposite_isSemidirectDecomposition i ν hStandard hG hi hν ∅ ν hζ
  have hDisjoint : Disjoint (oppositeUnipotent i ν) (parabolic i ν ∅) := by
    apply Subgroup.disjoint_def.mpr
    intro x hxV hxP
    apply Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
      (CommGroupScheme.groupHom ν ≫ i) hxV
    exact standardParabolic_empty_le i ν _ (by simpa only [parabolic, rootSet_empty] using hxP)
  obtain ⟨B, hB, hFaces⟩ := hBasis
  obtain ⟨_, A, q, _, hFactors⟩ := hFaces ∅ (Set.empty_subset _)
  have hFactorization : ∀ K ∈ B, HasIwahoriIntersectionDecomposition K
      (levi i ν ∅) (unipotent i ν ∅) (oppositeUnipotent i ν) := by
    intro K hK
    have h := (hFactors K hK).1
    simpa only [levi, unipotent, rootSet_empty, hOpp] using h
  let m : levi i ν ∅ := ⟨t, torusPoints_le_levi i ν ∅ ht⟩
  let α := innerConjugation t
  let αM := ContinuousMulEquiv.refl (levi i ν ∅)
  let αU := HaarModulus.normalizerConj (unipotent i ν ∅)
    ⟨t, hd.levi_le_normalizer m.property⟩
  let αV := HaarModulus.normalizerConj (oppositeUnipotent i ν)
    ⟨t, hdOpp.levi_le_normalizer m.property⟩
  have hMcompat : ∀ x : levi i ν ∅, α (x : RationalPoint k G.X) = (αM x : _) := by
    intro x
    have hx : (x : RationalPoint k G.X) ∈ centralizerPoints i := hLevi ▸ x.property
    have hc := centralizerPoints_le_pointCentralizer i hx t ht
    change t * (x : RationalPoint k G.X) * t⁻¹ = (x : RationalPoint k G.X)
    rw [hc]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hUcompat : ∀ x : unipotent i ν ∅,
      α (x : RationalPoint k G.X) = (αU x : _) := fun _ => rfl
  have hVcompat : ∀ x : oppositeUnipotent i ν,
      α (x : RationalPoint k G.X) = (αV x : _) := fun _ => rfl
  have hprod := hProduct (RationalPoint k G.X)
    (levi i ν ∅) (unipotent i ν ∅) (oppositeUnipotent i ν)
    (parabolic i ν ∅) K0 B α αM αU αV hM hU hV
    hB hFactorization hd.levi_le hd.unipotent_le hDisjoint hMcompat hUcompat hVcompat
  let : LocallyCompactSpace (unipotent i ν ∅) := hU.locallyCompactSpace
  let : LocallyCompactSpace (oppositeUnipotent i ν) := hV.locallyCompactSpace
  let : LocallyCompactSpace (levi i ν ∅) := hM.locallyCompactSpace
  have hrec := congrArg (fun a : ℝ≥0ˣ => (a : ℝ≥0))
    (hReciprocity k G hG T i hi ν hν hStandard ∅ hU ν hζ m)
  simp only [Units.val_mul, Units.val_one, HaarModulus.closedRestrictCharacter_eq,
    HaarModulus.restrictCharacter_apply, HaarModulus.normalizerCharacter_apply] at hrec
  have hrec' : mulEquivHaarChar αU * mulEquivHaarChar αV = 1 := by
    rw [← mulEquivHaarChar_borel αU, ← mulEquivHaarChar_borel αV]
    exact hrec
  rw [modularCharacter_eq_innerConjugation]
  change mulEquivHaarChar α = 1
  rw [hprod]
  simpa only [αM, mulEquivHaarChar_refl, mul_one, one_mul, mul_comm] using hrec'

end Langlands.Aubert.General.RationalPointFamily
