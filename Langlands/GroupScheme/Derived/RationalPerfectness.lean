import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Rational.Characters
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Perfect rational points and the scheme-theoretic derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MatrixGroups commutatorElement

namespace Langlands.GroupScheme

/-- The rational-point criterion for containment of a full scheme-theoretic image
in the derived subgroup, uniformly over algebraically closed fields. -/
def RationalPerfectnessCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom] (f : H ⟶ G),
    commutator (rationalPoints H) = ⊤ →
      SubgroupFunctor.range f ≤ derivedSubgroup G

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A reduced group locally of finite type with perfect rational points maps into
the scheme-theoretic derived subgroup of every target group scheme. -/
theorem range_le_derivedSubgroup_of_rationalPoints_perfect
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom] (f : H ⟶ G)
    (hH : commutator (rationalPoints H) = ⊤) :
    SubgroupFunctor.range f ≤ derivedSubgroup G := by
  intro T x hx K i hi hcomm
  apply SubgroupFunctor.range_le_of_algClosed_points hi ?_ T hx
  have hle : commutator (rationalPoints H) ≤
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 _))).comap (rationalPoints.map f) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change rationalPoints.map f ⁅a, b⁆ ∈
      (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _))
    rw [map_commutatorElement, commutatorElement_def]
    exact hcomm _ _ _
  rw [hH] at hle
  rintro y ⟨z, rfl⟩
  exact hle (Subgroup.mem_top z)

/-- The rational-point criterion holds on every test scheme. -/
theorem rationalPerfectnessCriterion : RationalPerfectnessCriterionStatement.{u} := by
  intro k _ _ G H _ _ f hH
  exact range_le_derivedSubgroup_of_rationalPoints_perfect f hH

/-- Over an algebraically closed field, perfectness of rational points implies
perfectness of the full derived subgroup functor for a reduced, locally finite-type group. -/
theorem derivedSubgroup_eq_top_of_rationalPoints_perfect
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : commutator (rationalPoints G) = ⊤) :
    derivedSubgroup G = ⊤ := by
  apply le_antisymm (fun _ _ _ => Subgroup.mem_top _)
  simpa only [SubgroupFunctor.range_id] using
    range_le_derivedSubgroup_of_rationalPoints_perfect (𝟙 G) hG

/-- The abstract special linear group of degree two over an algebraically closed field
is perfect, including in positive characteristic. -/
theorem commutator_sl2_eq_top_of_isAlgClosed :
    commutator SL(2, k) = ⊤ := by
  classical
  obtain ⟨a, ha⟩ := ({0, 1, -1} : Finset k).exists_notMem
  have ha' : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by simpa using ha
  exact Matrix.SL2.commutator_eq_top ha'.1 (sq_ne_one_iff.mpr ha'.2)

/-- A reduced locally finite-type group whose rational points are identified with
the actual matrix group `SL₂(k)` is scheme-theoretically perfect. -/
theorem derivedSubgroup_eq_top_of_sl2_rationalPoints
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    (e : SL(2, k) ≃* rationalPoints G) :
    derivedSubgroup G = ⊤ := by
  apply derivedSubgroup_eq_top_of_rationalPoints_perfect
  have he : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have h := map_commutator_eq SL(2, k) e.toMonoidHom
  rw [commutator_sl2_eq_top_of_isAlgClosed, Subgroup.map_top, he,
    ← commutator_def] at h
  exact h.symm

end Langlands.GroupScheme
