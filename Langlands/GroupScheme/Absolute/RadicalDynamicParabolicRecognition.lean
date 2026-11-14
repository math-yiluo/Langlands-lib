import Langlands.GroupScheme.Dynamic.ParabolicQuotient
import Langlands.GroupScheme.Absolute.UnipotentQuotientParabolics
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Rational.StandardParabolicIntersections
import Langlands.GroupScheme.Rational.SmoothAffineGenericCentralizer
import Langlands.GroupScheme.SubgroupFunctor.FppfImageContainment
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive

/-! # Parabolic recognition with a full unipotent radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))} [IsAffine Q.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (q : G ⟶ Q)

/-- The actual full inverse image of the quotient's dynamic parabolic. -/
def quotientParabolicPreimage : GroupScheme (Spec (CommRingCat.of k)) :=
  SubgroupPreimage.groupScheme q (Affine.parabolicHom (χ ≫ q))

/-- Its canonical inclusion in the original group. -/
def quotientParabolicPreimageInclusion : quotientParabolicPreimage χ q ⟶ G :=
  SubgroupPreimage.inclusion q (Affine.parabolicHom (χ ≫ q))

/-- The full inverse image is identified on every scheme test. -/
theorem range_quotientParabolicPreimageInclusion :
    SubgroupFunctor.range (quotientParabolicPreimageInclusion χ q) =
      (parabolic (χ ≫ q)).comap q := by
  change SubgroupFunctor.range
    (SubgroupPreimage.inclusion q (Affine.parabolicHom (χ ≫ q))) = _
  rw [SubgroupPreimage.range_inclusion, (Affine.isRepresentedBy_parabolicHom (χ ≫ q)).2]

end Dynamic

variable {k : Type u} [Field k]
    {G H Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [Smooth H.X.hom]

/-- A smooth closed subgroup containing a dynamic parabolic and the full
kernel of a reductive unipotent quotient is geometrically parabolic. -/
theorem isParabolicSubgroup_of_dynamic_le_of_unipotentQuotient_kernel_le
    (q : G ⟶ Q) (hQ : IsConnectedReductive Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : Dynamic.parabolic χ ≤ SubgroupFunctor.range i)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i) :
    IsParabolicSubgroup i := by
  have : Smooth Q.X.hom := hQ.smooth
  have : ConnectedSpace Q.X.left := hQ.connectedSpace
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : Mono i.hom.hom := hi.mono_overHom
  let j := Dynamic.Affine.parabolicHom (χ ≫ q)
  have hj : IsParabolicSubgroup j :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hQ j
      (Dynamic.Affine.isClosedSubgroup_parabolicHom (χ ≫ q)) _
      (Dynamic.Affine.isRepresentedBy_parabolicHom (χ ≫ q)).2
  have hp : IsParabolicSubgroup (Dynamic.quotientParabolicPreimageInclusion χ q) :=
    UnipotentQuotientParabolics.isParabolicSubgroup_preimage q hq j hj
  apply hp.of_smooth_overgroup hi
  rw [Dynamic.range_quotientParabolicPreimageInclusion]
  exact (Dynamic.parabolic_isFppfImage χ q hq.smooth inferInstance).comap_le_range
    i hP hker

/-- Over an algebraically closed field, containment of one dynamic parabolic
and the full represented unipotent radical suffices for parabolicity. -/
theorem isParabolicSubgroup_of_dynamic_le_of_radical_le [IsAlgClosed k]
    {U : GroupScheme (Spec (CommRingCat.of k))}
    (r : U ⟶ G) (hr : IsUnipotentRadical r)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : Dynamic.parabolic χ ≤ SubgroupFunctor.range i)
    (hrad : SubgroupFunctor.range r ≤ SubgroupFunctor.range i) :
    IsParabolicSubgroup i := by
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U r hr
  have : Smooth U.X.hom := hr.smooth
  have : ConnectedSpace U.X.left := hr.connectedSpace
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  apply isParabolicSubgroup_of_dynamic_le_of_unipotentQuotient_kernel_le q
    hQ.isConnectedReductive_of_isAlgClosed
    (HasSmoothConnectedUnipotentKernel.of_representative r hr.isClosedSubgroup
      hr.isUnipotent hq) i hi χ hP
  rwa [hq.2.2.2]

/-- Torus-centralizer, positive dynamic and full radical containment recognize
geometric parabolicity without assuming reductivity of the ambient group. -/
theorem isParabolicSubgroup_of_generic_torus_dynamic_radical_le [IsAlgClosed k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter j ν)
    (r : U ⟶ G) (hr : IsUnipotentRadical r)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hZ : torusCentralizer j ≤ SubgroupFunctor.range i)
    (hU : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ j) ≤ SubgroupFunctor.range i)
    (hrad : SubgroupFunctor.range r ≤ SubgroupFunctor.range i) :
    IsParabolicSubgroup i :=
  isParabolicSubgroup_of_dynamic_le_of_radical_le r hr i hi _
    (parabolic_le_of_torusCentralizer_le_of_unipotent_le hT j ν hν _ hZ hU) hrad

end Langlands.GroupScheme
