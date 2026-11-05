import Langlands.GroupScheme.Absolute.BorelNormalizerProof
import Langlands.GroupScheme.Rational.PositiveRootStabilizerReduction
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof

/-! # Positive-root stabilizers for a supplied generic dynamic Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

include hG hi

/-- A supplied Borel representing a generic cocharacter's dynamic parabolic
has trivial positive-root stabilizer in the actual rational normalizer quotient.
No global Borel-existence or parabolic-classification theorem is assumed. -/
theorem hasTrivialPositiveRootStabilizer_of_dynamicBorel
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    (hb : IsBorelSubgroup b)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy b) :
    HasTrivialPositiveRootStabilizer i ν := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  intro w hw
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hn := mem_normalizer_parabolic_of_positive_roots i relativeRootSignInclusions
    hG hi hν n hw
  rw [← hP.2] at hn
  have hpoint := SubgroupFunctor.normalizer_carrier_base_le (SubgroupFunctor.range b) hn
  rw [borelNormalizer k G B b hb] at hpoint
  have hp : n.val ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rwa [← hP.2]
  have hz := hi.isSplitSubtorus.mem_centralizer_of_mem_parabolic ν n.property hp
  rw [genericCentralizer k G hG T i hi ν hν, torusCentralizer_carrier_base] at hz
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hz

/-- The actual relative Weyl quotient is identified with its faithful action
on the rational root span, using only a supplied generic dynamic Borel. -/
def relativeWeylActionEquivOfDynamicBorel
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    (hb : IsBorelSubgroup b)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy b) :
    relativeWeylGroup i ≃* (relativeWeylAction i).range :=
  MonoidHom.ofInjective
    (hasTrivialPositiveRootStabilizer_of_dynamicBorel hG i hi ν hν hb hP
      |>.relativeWeylAction_injective)

theorem relativeWeylActionEquivOfDynamicBorel_apply
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    (hb : IsBorelSubgroup b)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy b)
    (w : relativeWeylGroup i) :
    (relativeWeylActionEquivOfDynamicBorel hG i hi ν hν hb hP w :
      relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i) = relativeWeylAction i w :=
  rfl

/-- Supplied actual integral reflection representatives, together with a
supplied generic dynamic Borel, give the full actual relative-root-system
comparison, including generation and faithfulness of the normalizer quotient. -/
theorem RelativeRootReflectionData.hasRelativeRootSystem_of_dynamicBorel
    (D : RelativeRootReflectionData i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    (hb : IsBorelSubgroup b)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy b) :
    HasRelativeRootSystem i := by
  let : Smooth G.X.hom := hG.smooth
  exact D.hasRelativeRootSystem_of_positive_stabilizer hi.isSplitSubtorus.1
    (hi.isSplitSubtorus.1.finite_relativeRoots i) hν
    (hasTrivialPositiveRootStabilizer_of_dynamicBorel hG i hi ν hν hb hP)

end Langlands.GroupScheme
