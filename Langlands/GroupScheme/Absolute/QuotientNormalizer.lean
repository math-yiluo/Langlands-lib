import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting

/-! # Rational normalizers and exact subgroup preimages under quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A surjective group map locally of finite type lifts every rational point. -/
theorem exists_rationalPointLift (q : G ⟶ Q)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X) :
    ∃ a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      a ≫ q.hom.hom = x := by
  obtain ⟨a, ha⟩ :=
    Langlands.exists_point_lift_of_locallyOfFiniteType_surjective q.hom.hom.left x.left
  have haS : a ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Over.w q.hom.hom, ← Category.assoc, ha]
    exact Over.w x
  exact ⟨Over.homMk a haS, Over.OverMorphism.ext ha⟩

/-- A chosen actual rational-point lift through a surjective group map
locally of finite type over an algebraically closed field. -/
def rationalPointLift (q : G ⟶ Q)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  Classical.choose (exists_rationalPointLift q x)

@[simp]
theorem rationalPointLift_comp (q : G ⟶ Q)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X) :
    rationalPointLift q x ≫ q.hom.hom = x :=
  Classical.choose_spec (exists_rationalPointLift q x)

/-- The induced group homomorphism on algebraically closed base points
is surjective. -/
theorem rationalPoints_surjective (q : G ⟶ Q)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left] :
    Function.Surjective
      ((yonedaGrp.map q).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom :=
  fun x => ⟨rationalPointLift q x, rationalPointLift_comp q x⟩

namespace SubgroupFunctor

/-- The rational normalizer of an exact subgroup preimage is the preimage
of its rational normalizer under a surjective group map locally of finite type. -/
theorem normalizer_carrier_base_comap_eq (q : G ⟶ Q)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left]
    (F : SubgroupFunctor Q) :
    Subgroup.normalizer
        ((F.comap q).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (Subgroup.normalizer
        (F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X))).comap
        ((yonedaGrp.map q).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom :=
  (Subgroup.comap_normalizer_eq_of_surjective
    (F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (rationalPoints_surjective q)).symm

/-- Rational self-normalization descends along an exact all-test preimage
under a surjective group map locally of finite type. -/
theorem normalizer_carrier_base_eq_of_quotient (q : G ⟶ Q)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left]
    (F : SubgroupFunctor G) (FQ : SubgroupFunctor Q)
    (hpre : FQ.comap q = F)
    (hnorm : Subgroup.normalizer
      (FQ.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X)) =
        FQ.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    Subgroup.normalizer
      (F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
        F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← hpre, normalizer_carrier_base_comap_eq, hnorm]
  rfl

end SubgroupFunctor

end Langlands.GroupScheme
