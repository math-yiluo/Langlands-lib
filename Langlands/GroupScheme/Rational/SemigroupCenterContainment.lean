import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusStatement
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.TrivialAction
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Full-centre containment from a fixed split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A fixed closed split torus is contained in every semigroup subgroup whose
semigroup contains zero. No smoothness of the ambient group is needed. -/
theorem range_le_semigroupSubgroup_of_fixed_splitTorus
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (b : AutomorphicAction S.toGrp G) (j : T.toGrp ⟶ G) (hj : IsClosedSubgroup j)
    (hfixed : ∀ (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ S.X) (t : U ⟶ T.X),
      b.act s (t ≫ j.hom.hom) = t ≫ j.hom.hom)
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    SubgroupFunctor.range j ≤ semigroupSubgroup b A := by
  let : IsAffineHom T.X.hom := hT.isAffineHom
  let c := AutomorphicAction.trivial S.toGrp T.toGrp
  have htriv : ∀ (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ S.X)
      (t : U ⟶ T.X), c.act s t = t :=
    fun _ s t => AutomorphicAction.trivial_act _ _ s t
  have heq : ∀ (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ S.X)
      (t : U ⟶ T.X), c.act s t ≫ j.hom.hom = b.act s (t ≫ j.hom.hom) := by
    intro U s t
    rw [htriv, hfixed]
  have h := semigroupSubgroup_map_le j hj c b heq A
  rw [semigroupSubgroup_eq_top_of_act_eq c htriv hS hT.smooth hT.connectedSpace A hzero,
    SubgroupFunctor.map_top] at h
  exact h

/-- The fixed centre-containing torus proposition supplies the full
scheme-theoretic centre containment required by the normal quotient reduction. -/
theorem center_le_semigroupSubgroup_of_fixedCenterContainingTorus
    [IsAlgClosed k] (hFixedTorus : FixedCenterContainingTorusStatement.{u})
    (hG : IsConnectedReductive G) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    center G ≤ semigroupSubgroup b A := by
  obtain ⟨T, j, hT, hj, hcenter, hfixed⟩ := hFixedTorus k G hG S hS b
  exact hcenter.trans
    (range_le_semigroupSubgroup_of_fixed_splitTorus hS hT b j hj hfixed A hzero)

end Langlands.GroupScheme.RelativeRoot
