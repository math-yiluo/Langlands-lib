import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.Rational.CoordinateSemigroupProof
import Langlands.GroupScheme.Rational.SemigroupFunctorialityReduction
import Langlands.GroupScheme.Rational.SemigroupRetraction
import Langlands.GroupScheme.Adjoint.NormalEquivariantRetractionStatement
import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.SubgroupFunctor.FppfImage

/-! # Actual semigroup functoriality and normal adjoint comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Every equivariant homomorphism of smooth affine groups preserves the actual
semigroup subgroup, without a separability assumption on the homomorphism. -/
theorem semigroupFunctoriality : SemigroupFunctorialityStatement.{u} :=
  semigroupFunctoriality_of_imageGeneration_and_containment
    ImageGeneration.pointedImageGeneration.{u}
    CoordinateWeights.coordinateSemigroupComparison.{u}.2

section Retraction

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An equivariant retract has exactly the semigroup intersection induced from
its ambient group, for every additive semigroup. -/
theorem semigroup_comap_eq_of_retraction
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G) (r : G ⟶ H) (hr : b.IsEquivariantRetraction c j r)
    (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A :=
  semigroup_comap_eq_of_equivariantRetraction semigroupFunctoriality hS b c j r hr A

/-- The retraction maps onto the semigroup subgroup on every original test. -/
theorem semigroup_map_eq_of_retraction
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G) (r : G ⟶ H) (hr : b.IsEquivariantRetraction c j r)
    (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup b A).map r = semigroupSubgroup c A :=
  semigroup_map_eq_of_equivariantRetraction semigroupFunctoriality hS b c j r hr A

end Retraction

section Adjoint

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The structural normal-adjoint retraction proposition suffices for semigroup
intersection in the normal adjoint case over an algebraically closed field. -/
theorem semigroup_comap_eq_of_normalAdjoint
    (hRetraction : NormalAdjointEquivariantRetractionStatement.{u})
    (hG : IsAdjoint G) (hH : IsAdjoint H)
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G) (hj : IsClosedSubgroup j) (hn : (SubgroupFunctor.range j).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom))
    (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let : Smooth H.X.hom := hH.isSemisimple.isConnectedReductive.smooth
  obtain ⟨r, hr, heqr⟩ := hRetraction k G H hG hH j hj hn S hS b c heq
  exact semigroup_comap_eq_of_retraction hS b c j r ⟨hr, heq, heqr⟩ A

end Adjoint

section AdjointSquare

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H G' H' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [IsAffineHom G'.X.hom] [IsAffineHom H'.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The normal-adjoint comparison lifts through actual adjoint quotient squares
when both semigroup fppf images and both full-centre containments are supplied.
The centre quotients and their restrictions need not be smooth. -/
theorem semigroup_comap_eq_of_normalAdjoint_quotient_square
    (hRetraction : NormalAdjointEquivariantRetractionStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (b' : AutomorphicAction S.toGrp G') (c' : AutomorphicAction S.toGrp H')
    (j : H ⟶ G) (q : G ⟶ G') (p : H ⟶ H') (j' : H' ⟶ G')
    (hq : IsAdjointQuotient q) (hp : IsAdjointQuotient p)
    (hsq : j ≫ q = p ≫ j')
    (hj' : IsClosedSubgroup j') (hn' : (SubgroupFunctor.range j').IsNormal)
    (heq' : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H'.X),
      c'.act s h ≫ j'.hom.hom = b'.act s (h ≫ j'.hom.hom))
    (A : AddSubsemigroup (characterLattice S))
    (hImageG : SubgroupFunctor.IsFppfImage
      (semigroupSubgroup b A) (semigroupSubgroup b' A) q)
    (hImageH : SubgroupFunctor.IsFppfImage
      (semigroupSubgroup c A) (semigroupSubgroup c' A) p)
    (hCenterG : center G ≤ semigroupSubgroup b A)
    (hCenterH : center H ≤ semigroupSubgroup c A) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  apply SubgroupFunctor.comap_eq_of_fppfImage_quotient_square j q p j' hsq
    hImageG hImageH
  · rwa [hq.kernel_range_eq_center]
  · rwa [hp.kernel_range_eq_center]
  · exact semigroup_comap_eq_of_normalAdjoint hRetraction hq.isAdjoint hp.isAdjoint
      hS b' c' j' hj' hn' heq' A

end AdjointSquare

end Langlands.GroupScheme.RelativeRoot
