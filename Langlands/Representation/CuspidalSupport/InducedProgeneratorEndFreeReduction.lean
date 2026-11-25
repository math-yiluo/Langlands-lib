import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndBasis
import Langlands.Representation.CuspidalSupport.LeviInductionEndEmbedding
import Langlands.Representation.CuspidalSupport.NormKernelSummandCenterBasis
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorReduction
import Langlands.Representation.CuspidalSupport.RationalSummandInductionSupercuspidal
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # The endomorphism ring of the induced progenerator from the joint special-compact basis

Renard VI.10.4, Lemma (`InducedProgeneratorEndFreeStatement`), reduced to the single open
structural statement `JointSpecialCompactBasisExistenceStatement`, which is used only to make
`Π_D` projective.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Reduction

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inducedProgeneratorReductionAmbientTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}

/-- Given the joint special-compact basis existence, `Π_D = ind_{⁰M(F)}^{M(F)} ρ₀` is
projective among smooth representations of `M(F)`, for the Levi `M` of an actual rational
parabolic, a supercuspidal `π` and any subrepresentation `ρ₀` of `π|_{⁰M(F)}`. -/
theorem projective_rationalNormKernelSummandInduction_of_jointSpecialCompact
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), IsSupercuspidal π →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M),
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      Projective (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ ρ₀ j hj
  have h0 : HasCompactNormKernelRestriction π :=
    compactRestriction_of_isSupercuspidal parabolicDynamic standardCocharacter
      relativeRootSystem hJoint hl.isConnectedReductive π hπ
  have hc : HasCompactSmoothDualCoefficients
      (π.representation.comp (Plancherel.rationalCommonNormKernel M).subtype) := h0
  exact CuspidalSupport.rationalNormKernelSummandInduction_projective M π ρ₀ j hc hj

/-- **A basis of `End(i_P Π_D)` over `End(Π_D)ᵐᵒᵖ` indexed by `W(D)`, from the joint
special-compact basis existence.** This is `inducedProgeneratorEndBasis` with its two
hypotheses discharged: `Π_D` is projective by
`projective_rationalNormKernelSummandInduction_of_jointSpecialCompact` and supercuspidal by
`isSupercuspidal_rationalNormKernelSummandInduction`. -/
def inducedProgeneratorEndBasisOfJointSpecialCompact
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u}) (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible → IsSupercuspidal π →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M), ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      letI := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
      letI := RepFunctorFiltration.endPrecompModule
        (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul)
        (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
          (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))
      Module.Basis (twistStabilizerDoubleCosets p l hp hl π)
        (End (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))ᵐᵒᵖ
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ⟶
          (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)) :=
  haveI := hl.isConnectedReductive.isAffineHom
  haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  haveI := hl.isConnectedReductive.smooth
  letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  fun π hπ hsc ρ₀ hρ₀ j hj =>
    inducedProgeneratorEndBasis hG p l r hp hr hl hmul π hπ ρ₀ hρ₀ j hj
      (projective_rationalNormKernelSummandInduction_of_jointSpecialCompact.{u, v}
        hJoint p l hp hl π hsc ρ₀ j hj)
      (isSupercuspidal_rationalNormKernelSummandInduction π hsc ρ₀ j hj)

end Reduction

/-- **Renard VI.10.4, Lemma, from the joint special-compact basis existence.** The joint
special-compact basis existence implies `InducedProgeneratorEndFreeStatement`. The first
conjunct is `leviInductionEndEmbedding`, the second and third are
`inducedProgeneratorEnd_expansion` with `Π_D` projective and supercuspidal, and the fourth is
`leviInducedEndCenterExpansion_of_endExpansion` applied to the third. -/
theorem inducedProgeneratorEndFree_of_jointSpecialCompact
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u}) :
    InducedProgeneratorEndFreeStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  intro _ _ P M N p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ hsc ρ₀ hρ₀ j hj W piD I
  have hproj := projective_rationalNormKernelSummandInduction_of_jointSpecialCompact.{u, v}
    hJoint p l hp hl π hsc ρ₀ j hj
  have hsc' := isSupercuspidal_rationalNormKernelSummandInduction π hsc ρ₀ j hj
  obtain ⟨hfin, b, hb⟩ := inducedProgeneratorEnd_expansion hG p l r hp hr hl hmul
    π hπ ρ₀ hρ₀ j hj hproj hsc'
  have hb' : ∀ x : End (I.obj piD), ∃! a : Fin _ → End piD,
      x = ∑ i, End.of (I.map (a i).asHom ≫ (End.of (b i)).asHom) := by
    intro x
    obtain ⟨a, ha, hau⟩ := hb x.asHom
    refine ⟨fun i => End.of (a i), End.ext ?_, fun a' ha' => ?_⟩
    · rw [End.sum_asHom]
      exact ha
    · have h := congrArg End.asHom ha'
      rw [End.sum_asHom] at h
      have h' := hau (fun i => (a' i).asHom) h
      funext i
      exact End.ext (congrFun h' i)
  obtain ⟨s, c, hc⟩ := leviInducedEndCenterExpansion_of_endExpansion p l r hp hr hl hmul
    π hπ ρ₀ hρ₀ j hj _ (fun i => End.of (b i)) hb'
  refine ⟨fun a a' h => congrArg End.asHom ((leviInductionEndEmbedding.{u, max u v} p l r hp hr
      hl hmul (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)).injective
      (a₁ := End.of a) (a₂ := End.of a') (End.ext h)), hfin, ⟨b, hb⟩,
    s, fun i => (c i).asHom, fun x => ?_⟩
  obtain ⟨z, hz, hzu⟩ := hc (End.of x)
  refine ⟨z, ?_, fun z' hz' => hzu z' (End.ext ?_)⟩
  · have h := congrArg End.asHom hz
    rw [End.sum_asHom] at h
    exact h
  · rw [End.sum_asHom]
    exact hz'

end Langlands.Aubert.General.RepresentedParabolic
