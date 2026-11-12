import Langlands.Representation.CuspidalSupport.BernsteinLeviInertiaCofan
import Langlands.Representation.CuspidalSupport.BernsteinCarrierDescent
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingStatement

/-! # Assembly of the actual finite cuspidal embedding target -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinFiniteTargetTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinFiniteTargetFieldT2 : T2Space F :=
  Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinFiniteTargetAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinFiniteTargetIndexDecidableEq :
    DecidableEq (Finset (SimpleRoot i ν)) := Classical.decEq _

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Flatten the actual induced inertia cofans inside the original finite
induced-cuspidal direct-sum target. -/
def bernsteinFiniteInducedCofan
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (τ : ∀ I : Finset (SimpleRoot i ν), SmoothRep.{0, uF, max uF uV} ℂ (levi i ν I))
    (hτ : ∀ I, Langlands.Aubert.General.IsLeviCuspidal
      (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I) (τ I)) :
    BernsteinLabelledCofanPresentation i ν family
      (SmoothRep.directSum.{uF, uF, max uF uV} (fun I =>
        (normalizedInductionFunctor (family.decomposition I)
          (family.closedUnipotent I)).obj (τ I))) := by
  classical
  let A := fun I => (normalizedInductionFunctor (family.decomposition I)
    (family.closedUnipotent I)).obj (τ I)
  let p := fun I => bernsteinInducedCuspidalCofan i ν family hdecomp hGeom I (τ I) (hτ I)
  let t := fun I => Cofan.mk (A I) (p I).leg
  let s := SmoothRep.directSumCofan A
  refine ⟨(Σ I, (p I).index), (fun k => (p k.1).summand k.2),
    (fun k => (p k.1).leg k.2 ≫ SmoothRep.directSumι A k.1), ?_,
    (fun k => (p k.1).label k.2), (fun k => (p k.1).block k.2)⟩
  exact Langlands.Cofan.sigmaCofanIsColimit
    (fun I => (p I).summand) t s (fun I => (p I).isColimit)
    (SmoothRep.directSumIsColimit A)

/-- Actual support uniqueness regroups a supplied Bernstein-labelled cofan
into the original class-indexed coproduct predicate. -/
theorem isBernsteinCoproductOfComponents_of_labelledPresentation
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (p : BernsteinLabelledCofanPresentation i ν family W) :
    Renard.IsCoproductOfComponents
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, max uF uV} i ν family c) W := by
  apply isBernsteinCoproductOfComponents_of_labelledCofan.{uF, max uF uV}
    i ν family hunique p.summand (Cofan.mk W p.leg) p.isColimit p.label
  intro k
  exact (bernsteinBlockProperty_iff_saturated _ _).mpr (p.block k)

/-- The literal finite cuspidal embedding, actual Levi inertia decomposition,
actual support uniqueness and induced-inertia exclusion imply objectwise
Bernstein decomposition in the original independent carrier universe. -/
theorem bernsteinCoproductOfComponents_of_finiteEmbedding
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (hEmbed : FiniteCuspidalInducedEmbeddingTarget.{uF, uF, uV}
      (parabolic i ν) (levi i ν) (unipotent i ν) family.decomposition
      family.closedUnipotent family.closedLevi family.leviDecomposition)
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    Renard.IsCoproductOfComponents
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family c) V := by
  classical
  obtain ⟨τ, hτ, f, hf⟩ := hEmbed V
  exact isBernsteinCoproductOfComponents_of_injectiveIntertwiner i ν family hunique f hf
    (isBernsteinCoproductOfComponents_of_labelledPresentation i ν family hunique _
      (bernsteinFiniteInducedCofan i ν family hdecomp hGeom τ hτ))

/-- The global actual finite-embedding input supplies the literal finite
embedding needed for this family; all structural comparison inputs are proved.
Together with the other three retained inputs it yields the exact original
category-decomposition predicate for this family. -/
theorem bernsteinCategoryDecomposition_of_representationInputs
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (hdecomp : RationalCuspidalInertiaProductDecompositionStatement.{uF, max uF uV})
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (hEmbed : RationalCuspidalInducedEmbeddingStatement.{uF, uV}) :
    Renard.IsCategoryDecomposition
      (fun c : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family c) := by
  let := family.finiteSimpleRoots
  let := Fintype.ofFinite (SimpleRoot i ν)
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hactual : FiniteCuspidalInducedEmbeddingTarget.{uF, uF, uV}
      (parabolic i ν) (levi i ν) (unipotent i ν) family.decomposition
      family.closedUnipotent family.closedLevi family.leviDecomposition :=
    hEmbed F G family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter standardCocharacter standardLeviIntersection
      (relativeRootSystem F G family.connectedReductive T i family.maximalSplitTorus)
      family.closedUnipotent family.closedLevi
  exact ⟨bernsteinCoproductOfComponents_of_finiteEmbedding i ν family
    hunique hdecomp hGeom hactual,
    bernsteinBlock_offDiagonalHomsZero_of_supportUniqueness i ν family hunique⟩

end Langlands.CuspidalSupport
