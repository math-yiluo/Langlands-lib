import Langlands.GroupScheme.Adjoint.ExistenceStatement
import Langlands.GroupScheme.Adjoint.SubgroupEmbedding
import Langlands.GroupScheme.Reductive.NormalCenterStatement
import Langlands.GroupScheme.Rational.SemigroupAdjointImageStatement
import Langlands.GroupScheme.Rational.SemigroupCenterContainment
import Langlands.GroupScheme.Rational.SemigroupFunctorialityProof

/-! # Normal reductive semigroup comparison through full-centre quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The independent structural propositions used by the normal reductive
intersection reduction. This bundle asserts none of its components. -/
def NormalReductiveSemigroupPrerequisites : Prop :=
  AdjointQuotientExistenceStatement.{u} ∧
    FixedCenterContainingTorusStatement.{u} ∧
    NormalReductiveCenterStatement.{u} ∧
    SemigroupAdjointImageStatement.{u} ∧
    NormalAdjointEquivariantRetractionStatement.{u}

section SuppliedQuotients

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H Q R : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- For supplied actual adjoint quotients, the structural centre, fixed-torus,
adjoint-image and adjoint-retraction propositions give normal reductive
semigroup intersection comparison. The centre quotients may be nonsmooth. -/
theorem semigroup_comap_eq_of_normalReductive_quotients
    (hFixed : FixedCenterContainingTorusStatement.{u})
    (hCenter : NormalReductiveCenterStatement.{u})
    (hImage : SemigroupAdjointImageStatement.{u})
    (hRetraction : NormalAdjointEquivariantRetractionStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (q : G ⟶ Q) (p : H ⟶ R)
    (hq : IsAdjointQuotient q) (hp : IsAdjointQuotient p)
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    (semigroupSubgroup b A).comap i = semigroupSubgroup c A := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom Q.X.hom := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffineHom R.X.hom := hp.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  have hcenters := hCenter k G H hq.isConnectedReductive hp.isConnectedReductive i hi hn
  let j := hq.subgroupHom hp i hcenters
  have hj : IsClosedSubgroup j := hq.subgroupHom_isClosedSubgroup hp i hcenters
  have hjn : (SubgroupFunctor.range j).IsNormal :=
    hq.subgroupHom_isNormal hp i hcenters hn
  have hjeq : (hp.action c).IsEquivariant (hq.action b) j :=
    hq.subgroupHom_isEquivariant hp b c i hcenters (fun s h => heq _ s h)
  apply semigroup_comap_eq_of_normalAdjoint_quotient_square hRetraction hS
    b c (hq.action b) (hp.action c) i q p j hq hp
    (hq.subgroupHom_square hp i hcenters) hj hjn (fun _ s h => hjeq s h) A
  · exact hImage k G Q inferInstance inferInstance S hS b (hq.action b) q hq
      (fun _ s g => hq.action_isEquivariant b s g) A hzero
  · exact hImage k H R inferInstance inferInstance S hS c (hp.action c) p hp
      (fun _ s h => hp.action_isEquivariant c s h) A hzero
  · exact center_le_semigroupSubgroup_of_fixedCenterContainingTorus
      hFixed hq.isConnectedReductive hS b A hzero
  · exact center_le_semigroupSubgroup_of_fixedCenterContainingTorus
      hFixed hp.isConnectedReductive hS c A hzero

end SuppliedQuotients

section Existence

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The five independent structural propositions imply semigroup intersection
comparison for normal connected reductive subgroups over algebraically closed
fields when zero belongs to the character semigroup. -/
theorem semigroup_comap_eq_of_normalReductive
    (hPrerequisites : NormalReductiveSemigroupPrerequisites.{u})
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    (semigroupSubgroup b A).comap i = semigroupSubgroup c A := by
  obtain ⟨hExist, hFixed, hCenter, hImage, hRetraction⟩ := hPrerequisites
  obtain ⟨Q, q, hq⟩ := hExist k G hG
  obtain ⟨R, p, hp⟩ := hExist k H hH
  exact semigroup_comap_eq_of_normalReductive_quotients hFixed hCenter hImage
    hRetraction hS b c i hi hn heq q p hq hp A hzero

end Existence

end Langlands.GroupScheme.RelativeRoot
