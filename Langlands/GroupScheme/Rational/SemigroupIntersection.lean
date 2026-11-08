import Langlands.GroupScheme.Rational.SemigroupZeroExcludedIntersection
import Langlands.GroupScheme.Rational.CoordinateSemigroupProof
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.WeightSupportCongruence

/-! # Exact intersections of actual semigroup subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Intersecting actual semigroup subgroups agrees with intersecting the
semigroups whenever the first semigroup excludes zero. -/
theorem semigroupSubgroup_inf_eq (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (A B : AddSubsemigroup (characterLattice S)) (hA : 0 ∉ A) :
    semigroupSubgroup b A ⊓ semigroupSubgroup b B =
      semigroupSubgroup b (A ⊓ B) := by
  obtain ⟨⟨U, j, hj, hjc, hUs, hUc⟩, hstable, hLie, _⟩ :=
    semigroupRealization k G inferInstance inferInstance S hS b B
  let : IsAffineHom U.X.hom := hjc.isAffineHom
  let : Smooth U.X.hom := hUs
  let c := b.onRepresentedSubgroup j hj hstable
  have heq : ∀ (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ S.X)
      (x : V ⟶ U.X), c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp j hj hstable s x
  have htop : (⊤ : SubgroupFunctor U).map j = semigroupSubgroup b B := by
    rw [SubgroupFunctor.map_top, hj.2]
  have hsupport : actionWeightSupport c ⊤ ⊆ B := by
    rw [← actionWeightSupport_map j hj.1 c b heq, htop]
    exact fun χ hχ => ((HasLieImage.mem_actionWeightSupport_iff b hS B hLie χ).mp hχ).1
  have hcongr : semigroupSubgroup c A = semigroupSubgroup c (A ⊓ B) :=
    semigroupSubgroup_eq_of_weightSupport c
      (fun χ hχ => ⟨fun hχA => ⟨hχA, hsupport hχ⟩, And.left⟩)
  have hcomap : (semigroupSubgroup b A).comap j = semigroupSubgroup c A :=
    semigroup_comap_eq_of_zero_not_mem b c j heq semigroupRealization
      CoordinateWeights.coordinateSemigroupComparison.2 hS hjc A hA
  calc
    semigroupSubgroup b A ⊓ semigroupSubgroup b B =
        ((semigroupSubgroup b A).comap j).map j := by
      rw [SubgroupFunctor.map_comap, hj.2]
      exact SubgroupFunctor.ext (fun V => inf_comm _ _)
    _ = (semigroupSubgroup c (A ⊓ B)).map j := by rw [hcomap, hcongr]
    _ = semigroupSubgroup b (A ⊓ B) :=
      semigroupSubgroup_map_eq j hjc c b heq (A ⊓ B)
        (by rw [hj.2]; exact semigroupSubgroup_mono b inf_le_right)

/-- The exact point-group identification between the intersection of two
actual semigroup subgroups and the subgroup of the intersected semigroup. -/
def semigroupIntersectionPointsEquiv (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (A B : AddSubsemigroup (characterLattice S)) (hA : 0 ∉ A)
    (V : Over (Spec (CommRingCat.of k))) :
    ((semigroupSubgroup b A ⊓ semigroupSubgroup b B).carrier V) ≃*
      ((semigroupSubgroup b (A ⊓ B)).carrier V) :=
  MulEquiv.subgroupCongr
    (congrArg (fun F : SubgroupFunctor G => F.carrier V)
      (semigroupSubgroup_inf_eq hS b A B hA))

@[simp] theorem semigroupIntersectionPointsEquiv_val (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (A B : AddSubsemigroup (characterLattice S)) (hA : 0 ∉ A)
    (V : Over (Spec (CommRingCat.of k)))
    (x : ((semigroupSubgroup b A ⊓ semigroupSubgroup b B).carrier V)) :
    (semigroupIntersectionPointsEquiv hS b A B hA V x).val = x.val := rfl

end Langlands.GroupScheme.RelativeRoot
