import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.MatrixRepresentation.UnipotentQuotient
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.Rational.Characters
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport

/-! # Bounded adjoint images from full-center kernel representations -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsAdjointQuotient

variable {k : Type u} [Field k]
  {G A P : GroupScheme (Spec (CommRingCat.of k))}
  {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-- A homomorphism killing the full center descends to a closed embedding when
its full scheme kernel is contained in that center. -/
theorem isClosedSubgroup_desc_of_kernel_le
    [IsAffineHom P.X.hom] [LocallyOfFiniteType P.X.hom]
    (f : G ⟶ P) (hf : KillsCenter f)
    (hk : SubgroupFunctor.range (kernelι f) ≤ center G) :
    IsClosedSubgroup (hq.desc f hf) := by
  let : IsAffineHom G.X.hom := hq.isConnectedReductive.isAffineHom
  let hA := hq.isAdjoint.isSemisimple.isConnectedReductive
  let : IsAffineHom A.X.hom := hA.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : Smooth A.X.hom := hA.smooth
  let : ConnectedSpace A.X.left := hA.connectedSpace
  let : Flat q.hom.hom.left := hq.flat
  let : Surjective q.hom.hom.left := hq.surjective
  let : QuasiCompact q.hom.hom.left := inferInstance
  let : Mono (hq.desc f hf).hom.hom :=
    FpqcHomDescent.mono_of_kernel_range_le q f (hq.desc f hf)
      (hq.comp_desc f hf) (by rw [hq.kernel_range_eq_center]; exact hk)
  exact HomImage.isClosedSubgroup_of_mono _

end Langlands.GroupScheme.IsAdjointQuotient

namespace Langlands.BruhatTits.RationalPoints

set_option linter.defProp false in
/-- Bounded image under an actual full-center kernel homomorphism implies
bounded image in any supplied actual adjoint quotient. -/
def isAlgebraicallyBounded_adjoint_image_of_kernel_eq_center
    {F : Type u} [Field F] [ValuativeRel F]
    {G A P : GroupScheme (Spec (CommRingCat.of F))}
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    [IsAffine A.X.left] [IsAffineHom P.X.hom] [IsAffine P.X.left]
    [LocallyOfFiniteType P.X.hom]
    (f : G ⟶ P) (hk : SubgroupFunctor.range (kernelι f) = center G)
    (S : Set (rationalPoints G))
    (hS : IsAlgebraicallyBounded F P.X (rationalPoints.map f '' S)) :
    IsAlgebraicallyBounded F A.X (rationalPoints.map q '' S) := by
  have hf : KillsCenter f := by
    intro T x hx
    apply (mem_range_kernelι_iff f x).mp
    rw [hk]
    exact hx
  let : IsClosedImmersion (hq.desc f hf).hom.hom.left :=
    hq.isClosedSubgroup_desc_of_kernel_le f hf (by rw [hk])
  apply isAlgebraicallyBounded_of_closedImmersion F (hq.desc f hf).hom.hom
  have heq : ((fun p : rationalPoints A => p ≫ (hq.desc f hf).hom.hom) ''
      (rationalPoints.map q '' S)) = rationalPoints.map f '' S := by
    rw [Set.image_image]
    congr 1
    funext x
    change (x ≫ q.hom.hom) ≫ (hq.desc f hf).hom.hom = x ≫ f.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hq.comp_desc]
  rw [heq]
  exact hS

end Langlands.BruhatTits.RationalPoints
