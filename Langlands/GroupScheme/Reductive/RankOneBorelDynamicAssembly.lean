import Langlands.GroupScheme.Reductive.RankOnePrescribedBorelCurve
import Langlands.GroupScheme.Dynamic.HomogeneousCurveParabolicComparison

/-! # Conditional assembly of the two dynamic Borels in rank one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Choose the original cocharacter or its negative whose actual dynamic
parabolic is represented by the prescribed Borel, retaining four structural
inputs explicitly. -/
def prescribedBorelSignedParabolic
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hConj : SolvableMaximalTorusConjugacyStatement.{u})
    (hCent : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : haveI := hG.isAffineHom
      α ∈ roots i) (ν : cocharacterLattice T)
    (hν : latticePairing T α ν ≠ 0)
    (b : B ⟶ G) (hB : IsBorelSubgroup b)
    (t : T.toGrp ⟶ B) (ht : t ≫ b = i) :
    {eta : cocharacterLattice T // (eta = ν ∨ eta = -ν) ∧
      (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy b} := by
  let D := prescribedBorelDynamicCurveData
    hFix hProj hConj hCent hG i hi hT hdep hα ν hν b hB t ht
  let : IsProper D.quotient.hom := D.proper
  let : Smooth D.projection.left := D.smooth
  let : Surjective D.projection.left := D.surjective
  let : QuasiCompact D.projection.left := D.quasiCompact
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t ≫ b) ≤
      SubgroupFunctor.range b := by
    simpa only [ht] using D.centralizer_le
  let E := HomogeneousQuotient.signedParabolicRepresentativeOfCurve
    b D.projection D.fibers hG.isPseudoReductive hB.isClosedSubgroup
    hB.isSolvableGroupScheme hB.connectedSpace hT t ν
    D.dimension_le_one D.inclusion_not_isIso hZ
  refine ⟨E.val, E.property.1, ?_⟩
  simpa only [ht] using E.property.2

/-- Four explicit structural theorems imply the public rank-one Borel
statement. This conditional theorem does not discharge those inputs. -/
theorem rankOneBorelDynamic_of_projectiveBorelInputs
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hConj : SolvableMaximalTorusConjugacyStatement.{u})
    (hCent : AlgClosedMaximalTorusCentralizerStatement.{u}) :
    RankOneBorelDynamicStatement.{u} := by
  intro k _ _ G hG T i hT hi hdep α hα ν hν B b t hB ht
  obtain ⟨eta, hsigned, hrep⟩ := prescribedBorelSignedParabolic
    hFix hProj hConj hCent hG i hi hT hdep hα ν hν b hB t ht
  rcases hsigned with rfl | rfl
  · exact Or.inl hrep
  · exact Or.inr hrep

end Langlands.GroupScheme
