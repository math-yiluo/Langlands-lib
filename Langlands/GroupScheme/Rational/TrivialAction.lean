import Langlands.GroupScheme.Rational.SemigroupTriviality
import Langlands.GroupScheme.Rational.SemigroupSingleton
import Langlands.GroupScheme.Lie.TorusCentralizer

/-! # Trivial actual actions and their semigroup subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} (H G : GroupScheme B)

/-- The actual trivial action, given by the second projection. -/
def trivial : AutomorphicAction H G where
  hom := snd H.X G.X
  one_left g := lift_snd _ _
  mul_left h h' g := by simp only [lift_snd]
  mul_right h g g' := by simp only [lift_snd]

@[simp]
theorem trivial_act {T : Over B} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (trivial H G).act h g = g :=
  lift_snd h g

/-- An action fixing every point on every test is the actual trivial action. -/
theorem eq_trivial_of_act_eq (a : AutomorphicAction H G)
    (ha : ∀ (T : Over B) (h : T ⟶ H.X) (g : T ⟶ G.X), a.act h g = g) :
    a = trivial H G := by
  have hh : a.hom = snd H.X G.X := by
    have h := ha (H.X ⊗ G.X) (fst H.X G.X) (snd H.X G.X)
    simpa only [act, lift_fst_snd, Category.id_comp] using h
  cases a
  cases hh
  rfl

end AutomorphicAction

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (b : AutomorphicAction S.toGrp G)
    (htriv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (g : T ⟶ G.X), b.act s g = g)

include htriv

/-- A pointwise trivial actual action puts the whole Lie algebra in weight zero. -/
theorem actionWeightSpace_zero_eq_top_of_act_eq :
    actionWeightSpace b 0 = ⊤ := by
  apply top_unique
  intro X _
  rw [mem_actionWeightSpace_iff]
  intro A _ _ s
  rw [htriv, Lie.characterValue_zero, Units.val_one, lieKernelScale_one]

variable [LocallyOfFiniteType G.X.hom] (hS : IsSplitTorus S.toGrp)

include hS

/-- For a split acting torus, every nonzero-character weight space of a
trivial actual action vanishes. -/
theorem actionWeightSpace_eq_bot_of_act_eq {χ : characterLattice S} (hχ : χ ≠ 0) :
    actionWeightSpace b χ = ⊥ := by
  have hd := (iSupIndep_actionWeightSpace b hS).pairwiseDisjoint hχ
  change Disjoint (actionWeightSpace b χ) (actionWeightSpace b 0) at hd
  rw [actionWeightSpace_zero_eq_top_of_act_eq b htriv, disjoint_top] at hd
  exact hd

/-- A trivial actual action has no occurring weight other than possibly zero,
for any all-test subgroup functor. -/
theorem actionWeightSupport_subset_zero_of_act_eq (F : SubgroupFunctor G) :
    actionWeightSupport b F ⊆ {0} := by
  rintro χ ⟨X, hX, hXχ, _⟩
  apply Set.mem_singleton_iff.mpr
  by_contra hχ
  rw [actionWeightSpace_eq_bot_of_act_eq b htriv hS hχ] at hXχ
  exact hX hXχ

/-- A semigroup excluding zero selects no ambient weight of a trivial
actual action, so its generated functor is the identity on all tests. -/
theorem semigroupSubgroup_eq_bot_of_act_eq
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∉ A) :
    semigroupSubgroup b A = ⊥ := by
  apply semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization b hS A
  intro χ hχ hweight
  have heq : χ = 0 :=
    Set.mem_singleton_iff.mp (actionWeightSupport_subset_zero_of_act_eq b htriv hS ⊤ hweight)
  exact hzero (heq ▸ hχ)

omit [LocallyOfFiniteType G.X.hom] in
/-- A semigroup containing zero selects the whole smooth connected ambient
group for a trivial actual action. -/
theorem semigroupSubgroup_eq_top_of_act_eq
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    semigroupSubgroup b A = ⊤ := by
  let : Smooth G.X.hom := hG
  apply semigroupSubgroup_eq_top_of_support b hG hconn A
  intro χ hχ
  have heq : χ = 0 :=
    Set.mem_singleton_iff.mp (actionWeightSupport_subset_zero_of_act_eq b htriv hS ⊤ hχ)
  exact heq.symm ▸ hzero

omit [LocallyOfFiniteType G.X.hom] in
open Classical in
/-- The exact semigroup functor of a trivial actual action is determined
by whether the positive additive semigroup contains zero. -/
theorem semigroupSubgroup_of_act_eq
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (A : AddSubsemigroup (characterLattice S)) :
    semigroupSubgroup b A = if 0 ∈ A then ⊤ else ⊥ := by
  classical
  let : Smooth G.X.hom := hG
  split_ifs with hzero
  · exact semigroupSubgroup_eq_top_of_act_eq b htriv hS hG hconn A hzero
  · exact semigroupSubgroup_eq_bot_of_act_eq b htriv hS A hzero

end RelativeRoot

end Langlands.GroupScheme
