import Langlands.GroupScheme.Rational.LeviFactorization
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Closed subgroup containment detected on algebraically closed field points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H K : GroupScheme (Spec (CommRingCat.of k))}
  {i : H ⟶ G} {j : K ⟶ G}

/-- For a reduced source locally of finite type over an algebraically closed field,
containment of its image in a closed subgroup is detected on rational points. -/
theorem range_le_of_algClosed_points [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hj : IsClosedSubgroup j)
    (h : (range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
      (range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    range i ≤ range j := by
  let f := i.hom.hom.left
  let g := j.hom.hom.left
  let p := pullback.fst f g
  have : IsClosedImmersion g := hj
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hpclosed : IsClosed (Set.range p) := p.isClosedEmbedding.isClosed_range
  have hppts : closedPoints H.X.left ⊆ Set.range p := by
    intro x hx
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X :=
      Over.homMk (pointOfClosedPoint H.X.hom x hx)
        (pointOfClosedPoint_comp H.X.hom x hx)
    obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
    change b ≫ j.hom.hom = a ≫ i.hom.hom at hb
    rw [Scheme.Pullback.range_fst]
    change ∃ y, g y = f x
    refine ⟨b.left (IsLocalRing.closedPoint k), ?_⟩
    have he := congrArg
      (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
        q.left (IsLocalRing.closedPoint k)) hb
    change g (b.left (IsLocalRing.closedPoint k)) =
      f (pointOfClosedPoint H.X.hom x hx (IsLocalRing.closedPoint k)) at he
    exact he.trans (congrArg f
      (pointOfClosedPoint_apply H.X.hom x hx (IsLocalRing.closedPoint k)))
  have hprange : Set.range p = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← closure_closedPoints (X := H.X.left)]
    exact closure_minimal hppts hpclosed
  have : Surjective p := ⟨Set.range_eq_univ.mp hprange⟩
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let a := inv p ≫ pullback.snd f g
  have ha : a ≫ g = f := by
    dsimp [a]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  let b : H.X ⟶ K.X := Over.homMk a (by
    rw [← Over.w j.hom.hom, ← Category.assoc, ha]
    exact Over.w i.hom.hom)
  have hb : b ≫ j.hom.hom = i.hom.hom := by
    apply Over.OverMorphism.ext
    exact ha
  rintro U x ⟨y, rfl⟩
  change U ⟶ H.X at y
  refine ⟨y ≫ b, ?_⟩
  change (y ≫ b) ≫ j.hom.hom = y ≫ i.hom.hom
  rw [Category.assoc, hb]

/-- Rational-point containment and all-test-scheme containment agree under the
reduced finite-type-source and closed-target hypotheses. -/
theorem range_le_iff_algClosed_points [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hj : IsClosedSubgroup j) :
    range i ≤ range j ↔
      (range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
        (range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  ⟨fun h => h _, range_le_of_algClosed_points hj⟩

/-- The group-scheme factorization through a closed subgroup obtained from
containment on algebraically closed field points. -/
def factorOfAlgClosedPoints [IsReduced H.X.left]
    [LocallyOfFiniteType H.X.hom] (hj : IsClosedSubgroup j)
    (h : (range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
      (range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    H ⟶ K := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have hr : (range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  exact hr.factorHom i (range_le_of_algClosed_points hj h)

/-- The rational-point factorization commutes with the inclusion. -/
theorem factorOfAlgClosedPoints_comp [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hj : IsClosedSubgroup j)
    (h : (range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
      (range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    factorOfAlgClosedPoints hj h ≫ j = i := by
  exact IsRepresentedBy.factorHom_comp _ _ _

/-- A rational-point containment in a closed subgroup gives an actual group-scheme
factorization, without a monicity assumption on the source homomorphism. -/
theorem exists_factor_of_algClosed_points [IsReduced H.X.left]
    [LocallyOfFiniteType H.X.hom] (hj : IsClosedSubgroup j)
    (h : (range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
      (range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ a : H ⟶ K, a ≫ j = i :=
  ⟨factorOfAlgClosedPoints hj h, factorOfAlgClosedPoints_comp hj h⟩

end Langlands.GroupScheme.SubgroupFunctor
