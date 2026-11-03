import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Absolute.BorelContaining
import Langlands.GroupScheme.Absolute.BorelPromotion
import Langlands.GroupScheme.Absolute.BorelStatement

/-! # Borel conjugacy through the identity component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {B P G : GroupScheme (Spec (CommRingCat.of k))}

section IdentityComponent

variable [Smooth P.X.hom] [IsAffineHom P.X.hom]

/-- A Borel embedding lifted to the actual identity component. -/
structure BorelIdentityComponentData (b : B ⟶ P) where
  factor : B ⟶ identityComponent P
  isBorelSubgroup : IsBorelSubgroup factor
  factor_comp : factor ≫ identityComponentι P = b

/-- A Borel lies in the identity component and is a Borel there. -/
def IsBorelSubgroup.identityComponentData {b : B ⟶ P} (hb : IsBorelSubgroup b) :
    BorelIdentityComponentData b := by
  have : ConnectedSpace B.X.left := hb.connectedSpace
  let b₀ := IdentityComponent.factor P b
  have hb₀ : b₀ ≫ identityComponentι P = b :=
    IdentityComponent.factor_identityComponentι P b
  refine ⟨b₀, ?_, hb₀⟩
  apply IsBorelSubgroup.of_comp (IdentityComponent.isClosedSubgroup_identityComponentι P)
  rwa [hb₀]

/-- Borel conjugacy in the identity component implies Borel conjugacy in the
whole smooth affine group, without a connectedness assumption on that group. -/
theorem BorelSubgroupsAreConjugate.of_identityComponent
    (h : BorelSubgroupsAreConjugate (identityComponent P)) :
    BorelSubgroupsAreConjugate P := by
  intro B B' b b' hb hb'
  let d := hb.identityComponentData
  let d' := hb'.identityComponentData
  have hc := (h B B' d.factor d'.factor d.isBorelSubgroup d'.isBorelSubgroup).postcomp
    (identityComponentι P)
  simpa only [d.factor_comp, d'.factor_comp] using hc

variable [IsAlgClosed k]

/-- The connected-group Borel conjugacy statement also gives conjugacy for
every smooth affine group over an algebraically closed field. -/
theorem borelSubgroupsAreConjugate_of_borelConjugacy
    (hB : BorelConjugacyStatement.{u}) : BorelSubgroupsAreConjugate P := by
  apply BorelSubgroupsAreConjugate.of_identityComponent
  exact (hB k (identityComponent P)).2

end IdentityComponent

section Overgroup

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An ambient Borel inside a specified closed overgroup, with the actual
factorization of the specified torus through that Borel retained. -/
structure BorelPairInOvergroupData (j : T.toGrp ⟶ G) (i : P ⟶ G)
    (f : T.toGrp ⟶ P) where
  subgroup : GroupScheme (Spec (CommRingCat.of k))
  inclusion : subgroup ⟶ P
  torusFactor : T.toGrp ⟶ subgroup
  isBorelSubgroup : IsBorelSubgroup (inclusion ≫ i)
  torusFactor_comp : torusFactor ≫ inclusion = f

/-- If a closed overgroup contains one ambient Borel and its Borels are
conjugate, it contains an ambient Borel through the prescribed split torus. -/
def BorelExistence.borelPairInOvergroupData
    (j : T.toGrp ⟶ G) (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    (hi : IsClosedSubgroup i) (hf : f ≫ i = j)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hP : BorelSubgroupsAreConjugate P)
    (hex : ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ P),
      IsBorelSubgroup (b ≫ i)) : BorelPairInOvergroupData j i f := by
  exact Classical.choice (by
    obtain ⟨B, b, t, hb, ht, _⟩ :=
      exists_isBorelSubgroup_containing_splitTorus_in_closedSubgroup
        j i f hT hj.2.1 hi hf
    exact ⟨⟨B, b, t, hP.isBorelSubgroup_comp i hi hb hex, ht⟩⟩)

/-- The chosen ambient Borel and original maximal torus form a Borel pair. -/
theorem BorelPairInOvergroupData.isBorelPair
    {j : T.toGrp ⟶ G} {i : P ⟶ G} {f : T.toGrp ⟶ P}
    (d : BorelPairInOvergroupData j i f) (hj : IsMaximalTorus j)
    (hf : f ≫ i = j) : IsBorelPair (d.inclusion ≫ i) j := by
  exact ⟨d.isBorelSubgroup, hj, d.torusFactor,
    by rw [← Category.assoc, d.torusFactor_comp, hf]⟩

end Overgroup

end Langlands.GroupScheme
