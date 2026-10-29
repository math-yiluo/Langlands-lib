import Langlands.AbelianScheme.IsogenySpecialization
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Lifting algebraically closed field points through isogenies -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands

/-- A surjective morphism locally of finite type lifts points valued in an
algebraically closed field. -/
theorem exists_point_lift_of_locallyOfFiniteType_surjective
    {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    (x : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ a : Spec (CommRingCat.of K) ⟶ X, a ≫ f = x := by
  let p := pullback.snd f x
  have : JacobsonSpace ↥(pullback f x : Scheme.{u}) := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, _⟩ := p.surjective (IsLocalRing.closedPoint K)
  obtain ⟨c, _, hc⟩ := nonempty_inter_closedPoints
    (Z := Set.univ) (Set.nonempty_of_mem (Set.mem_univ z))
    isClosed_univ.isLocallyClosed
  refine ⟨pointOfClosedPoint p c hc ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    pointOfClosedPoint_comp p c hc, Category.id_comp]

namespace AbelianScheme

/-- Every algebraically closed field point lifts through an actual isogeny of
abelian schemes over that field. -/
def AlgClosedIsogenyPointLiftingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A B : AbelianScheme (Spec (CommRingCat.of K))) (f : A ⟶ B),
    IsIsogeny f →
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B.X,
        ∃ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
          a ≫ (groupHom f).hom.hom = x

/-- The actual point lift, as a morphism of schemes over the base field. -/
theorem exists_point_lift_of_isogeny
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B : AbelianScheme (Spec (CommRingCat.of K))}
    {f : A ⟶ B} (hf : IsIsogeny f)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B.X) :
    ∃ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
      a ≫ (groupHom f).hom.hom = x := by
  have : IsFinite (hom f) := hf.1
  have : Surjective (hom f) := hf.2.2
  obtain ⟨a, ha⟩ := exists_point_lift_of_locallyOfFiniteType_surjective (hom f) x.left
  have haS : a ≫ A.X.hom = 𝟙 (Spec (CommRingCat.of K)) := by
    rw [← Over.w (groupHom f).hom.hom, ← Category.assoc, ha]
    exact Over.w x
  refine ⟨Over.homMk a haS, ?_⟩
  exact Over.OverMorphism.ext ha

theorem algClosedIsogenyPointLifting : AlgClosedIsogenyPointLiftingStatement.{u} := by
  intro K _ _ A B f hf x
  exact exists_point_lift_of_isogeny hf x

end AbelianScheme
end Langlands
