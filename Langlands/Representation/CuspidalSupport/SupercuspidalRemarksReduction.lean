import Langlands.Representation.CuspidalSupport.SupercuspidalRemarksStatements
import Langlands.Representation.CuspidalSupport.SupercuspidalRemarksGeneric
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.Representation.Exponents.RepresentedCuspidalProjection
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Renard VI.2.1, remarks, from the joint special compact basis statement

The three remarks of `SupercuspidalRemarksStatements` follow from the represented
VI.2.1 equivalence (a) ⇔ (c) and from generic topological-group lemmas. Only the
forward implication (a) ⇒ (c) still has a theorem-valued premise:
`JointSpecialCompactBasisExistenceStatement`. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.BruhatTits.SpecialCompact Langlands.SupercuspidalRemarks

/-- Renard VI.2.1, remarks, reduced to the joint special compact basis statement: the
joint special compact basis statement implies `SupercuspidalRemarksStatements`. -/
def SupercuspidalRemarksReductionStatement : Prop :=
  JointSpecialCompactBasisExistenceStatement.{u} → SupercuspidalRemarksStatements.{u, v}

/-- Renard VI.2.1, remarks, from `JointSpecialCompactBasisExistenceStatement`. The
backward implications of the second and third remarks and the first remark use no
theorem-valued premise; the forward implications use the joint statement through
`compactRestriction_of_isSupercuspidal`. -/
theorem supercuspidalRemarksReduction : SupercuspidalRemarksReductionStatement.{u, v} := by
  intro hJoint k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := Plancherel.rationalCommonNormOpenSubgroup G
  have : H.toSubgroup.Normal := Plancherel.rationalCommonNormKernel_normal G
  have : (H.toSubgroup ⊔ Subgroup.center (rationalPoints G)).FiniteIndex :=
    CuspidalSupport.rationalCommonNormKernel_sup_center_finiteIndex k G hG
  have hHZ : IsCompact ((H.toSubgroup ⊓ Subgroup.center (rationalPoints G) :
      Subgroup (rationalPoints G)) : Set (rationalPoints G)) :=
    Plancherel.isCompact_rationalCommonNormKernel_inf_center G hG
  obtain ⟨K₀, hK₀⟩ : ∃ K : OpenSubgroup (rationalPoints G),
      IsCompact (K : Set (rationalPoints G)) :=
    Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup k G
  have hsc : ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G),
      HasCompactSmoothDualCoefficients (A.representation.comp H.toSubgroup.subtype) →
        IsSupercuspidal A := fun A hA =>
    isSupercuspidal_of_compactRestriction parabolicDynamic smoothMaximalSplitTorusConjugacy
      standardCocharacter relativeRootSystem hG A hA
  have hcr : ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G), IsSupercuspidal A →
      HasCompactSmoothDualCoefficients (A.representation.comp H.toSubgroup.subtype) :=
    fun A hA => compactRestriction_of_isSupercuspidal parabolicDynamic standardCocharacter
      relativeRootSystem hJoint hG A hA
  refine ⟨fun A B hBA hA => IsSupercuspidal.of_isSubquotient hBA hA,
    fun hZ A => ⟨fun hA => ?_, fun hA => ?_⟩, fun A => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · exact hasCompactSmoothDualCoefficients_of_support_of_isCompact_center A.representation hZ
      K₀ hK₀ (support_subset_mul_center_of_comp A.representation A.isSmooth H (hcr A hA))
  · exact hsc A (hasCompactSmoothDualCoefficients_comp_openSubgroup A.representation H hA)
  · exact support_subset_mul_center_of_comp A.representation A.isSmooth H (hcr A hA)
  · exact hsc A (hasCompactSmoothDualCoefficients_comp_of_support A.representation H hHZ
      K₀ hK₀ hA)

end Langlands.Aubert.General.RepresentedParabolic
