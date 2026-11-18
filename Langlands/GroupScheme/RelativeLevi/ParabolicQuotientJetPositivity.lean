import Langlands.AlgebraicGeometry.Modules.StabilizedTensorKernel
import Langlands.AlgebraicGeometry.Modules.TildeFiniteProjectiveFrames
import Langlands.AlgebraicGeometry.Picard.GrassmannianAffineOpenComparison
import Langlands.GroupScheme.IdentityJetAmbientGlobalGenerators
import Langlands.GroupScheme.IdentityJetGrassmannianAmple
import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantComponents
import Langlands.GroupScheme.RelativeLevi.ParabolicIdentityJetCoordinates
import Langlands.GroupScheme.RelativeLevi.PositiveParabolicQuotientJetEmbedding

/-! # Parabolic determinant-dual ampleness from the actual quotient jet kernels -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open HomogeneousQuotientFromEmbedding SelfNormalizingAmbient
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant
open Langlands.Scheme.Modules

section Quotient

variable {R : CommRingCat.{u}} {G P : GroupScheme (Spec R)}
  [IsAffine G.X.left] (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
  (Q : HomogeneousQuotient i) (D : ProperQuotientJetData i Q)

/-- The actual stabilized jet tensor kernel is the Grassmannian's classified kernel
on each affine open of the actual parabolic quotient. -/
def HasStabilizedJetKernelComparison : Prop :=
  let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
  letI : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  let p := Q.scheme.hom
  let C := ModuleCat.of R D.embeddingData.complement
  let M := IdentityJet.module r.group D.order
  let q := IdentityJet.ambientGlobalGenerator G p r.hom D.order
  let E := D.embeddingData.grassmannian
  let f := D.embeddingData.embedding.left
  ∀ U : Q.scheme.left.affineOpens,
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    (stabilizedTensorMap p M q C U).ker =
      (affineOpenPoint E f p (Over.w D.embeddingData.embedding) U).toSubmodule

/-- The actual positive-order kernel comparison gives ampleness of the chosen
actual Lie determinant dual of the quotient family. -/
theorem homogeneousQuotientLieDeterminantDual_isAmple_of_jetKernels
    [IsProper Q.scheme.hom] (hn : 0 < D.order)
    (hK : HasStabilizedJetKernelComparison hG i hi Q D) :
    (parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)).lieDeterminant.dual.IsAmple := by
  let r := parabolicRepresentative (homogeneousQuotientParabolic hG i hi Q)
  let : IsAffineHom r.group.X.hom := r.parabolic.isAffineHom
  let : Smooth r.group.X.hom := r.parabolic.smooth
  let p := Q.scheme.hom
  let : CompactSpace Q.scheme.left := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace Q.scheme.left := quasiSeparatedSpace_of_quasiSeparated p
  let C := ModuleCat.of R D.embeddingData.complement
  let : Module.Finite R C := D.embeddingData.finite_complement
  let : Module.Projective R C := D.embeddingData.projective_complement
  let M := IdentityJet.module r.group D.order
  let q := IdentityJet.ambientGlobalGenerator G p r.hom D.order
  let E := D.embeddingData.grassmannian
  let f := D.embeddingData.embedding.left
  let : IsClosedImmersion f := D.embeddingData.closed
  let N := IdentityJet.stabilizedModule r.group D.order p (tilde C)
  have hc : HasAffinePointComparison E f N
      (fun z => stabilizedGlobalGenerator p M q C z) := by
    apply hasAffinePointComparison_of_affineOpenTensorKernels E f p (Over.w D.embeddingData.embedding)
    intro U
    let := Scheme.TwoAffineOpenCover.algebraOfHom p U
    refine ⟨stabilizedTensorMap p M q C U, ?_, hK U, ?_⟩
    · apply stabilizedTensorMap_surjective
      rw [IdentityJet.globalFamilyTensorMap_ambientGlobalGenerator]
      exact r.identityJetTensorCoordinates_surjective hG D.order U
    · intro m
      exact (stabilizedTensorMap_tmul p M q C U (1 : Γ(Q.scheme.left, U)) m).trans
        (one_smul _ _)
  exact IdentityJet.lieDeterminantDual_isAmple_of_stabilizedGrassmannian
    r.group D.order hn p (tilde_hasFiniteLocalBasis_of_finite_projective C) E f _ hc

end Quotient

/-- The classified jet kernels on the prescribed quotient components give the
unchanged finite-family determinant-dual ampleness target. -/
theorem finiteAffineParabolicDeterminantDualAmple_of_jetKernels
    (hK : ∀ (R : Type u) [CommRing R]
      (G P : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
      (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      HasStabilizedJetKernelComparison hG i hi (affineParabolicQuotient hG i hi).quotient
        (affineParabolicQuotientJetDataAtLeast hG i hi 1).val) :
    FiniteAffineParabolicDeterminantDualAmpleStatement.{u} := by
  apply finiteAffineParabolicDeterminantDualAmple_of_components
  intro R _ G P hG i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let Q := affineParabolicQuotient hG i hi
  let : IsProper Q.quotient.scheme.hom := Q.proper
  let D := affineParabolicQuotientJetDataAtLeast hG i hi 1
  exact homogeneousQuotientLieDeterminantDual_isAmple_of_jetKernels hG i hi Q.quotient
    D.val D.property (hK R G P hG i hi)

end Langlands.GroupScheme.ParabolicSubgroupModuli
