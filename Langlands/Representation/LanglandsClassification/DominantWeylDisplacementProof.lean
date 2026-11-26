import Langlands.Representation.LanglandsClassification.DominantWeylDisplacementStatement
import Langlands.Representation.LanglandsClassification.StandardParabolicRootPresentation
import Langlands.Representation.Exponents.MaximalLeviExponentTransport
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization

/-! # Dominant Weyl displacement via the minimal standard parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace
open Langlands.Aubert.General.RepresentedParabolic

/-- The projected displacement theorem at the minimal standard parabolic
gives the bound in the full real character space. -/
theorem dominantWeylDisplacement : DominantWeylDisplacementStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro hν D x hx w
  have hrep : (torusCentralizer i).IsRepresentedBy (Standard.leviHom i ν ∅) := by
    rw [← (standardParabolicEndpoints k G hG T i hi ν hν).2.1]
    exact Standard.isRepresentedBy_leviHom i ν ∅
  have hclosed := Standard.isClosedSubgroup_leviHom i ν ∅
  let a := torusCentralizerFactor i hrep
  have hmax : IsMaximalSplitTorus a :=
    hi.isMaximalSplitTorus_torusCentralizerFactor hrep hclosed
  have ha : IsSplitComponent a :=
    ⟨hi.isSplitSubtorus.isCentralSplitTorus_torusCentralizerFactor hrep hclosed,
      fun A iA hiA f hf => hmax.2 A iA hiA.isSplitSubtorus f hf⟩
  have hfactor : 𝟙 T.toGrp ≫ i = a ≫ Standard.leviHom i ν ∅ := by
    rw [Category.id_comp, torusCentralizerFactor_comp]
  let pres := ParabolicDatum.standardRootPresentation i ν hG hi hν ∅
    (Set.empty_subset _) a ha (𝟙 T.toGrp) hfactor
  have h := pres.restrict_displacement_mem_nonnegCone hG D x
    (fun α => hx ⟨α.val, α.property.1.1⟩ α.property) w⁻¹
  change rationalCharacterRestrictReal (𝟙 T.toGrp)
    (relativeWeylDisplacement w⁻¹ x) ∈ pres.nonnegCone at h
  have hcone : pres.nonnegCone = (PointedCone.hull ℝ pres.restrictedRoots : Set (Vstar T)) :=
    congrArg (fun C : PointedCone ℝ (Vstar T) => (C : Set (Vstar T)))
      (RootCombination.nonnegCone_eq_hull pres.finite_restrictedRoots)
  have hroots : pres.restrictedRoots =
      (fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' simpleRelativeRoots i ν := by
    change restrictedSimpleRoots i ν ∅ (𝟙 T) = _
    rw [restrictedSimpleRoots, Set.sdiff_empty]
    exact Set.image_congr fun α _ => by simp only [restrictedRootVector_eq_tmul, Category.id_comp]
  rwa [rationalCharacterRestrictReal_id_apply, relativeWeylDisplacement_apply, hcone, hroots] at h

end Langlands.GroupScheme
