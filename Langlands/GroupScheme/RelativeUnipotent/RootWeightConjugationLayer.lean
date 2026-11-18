import Langlands.GroupScheme.RelativeUnipotent.RootWeightKernel
import Langlands.GroupScheme.RepresentedAction

/-! # Positive-term conjugation acts trivially on the next vector layer -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupTheory.HeightFiltration

variable {G : Type v} [Group G] {n : ℕ}
  (H : Fin n → Subgroup G) (w : Fin n → ℕ)
  (hc : ∀ i j, ⁅H i, H j⁆ ≤ level H w (w i + w j))

include hc

/-- The sum commutator bound extends to generated levels when the target level
is normal in the ambient group. -/
theorem commutator_mem_level_add (a b : ℕ) [(level H w (a + b)).Normal]
    {x y : G} (hx : x ∈ level H w a) (hy : y ∈ level H w b) :
    ⁅x, y⁆ ∈ level H w (a + b) := by
  let N := level H w (a + b)
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hcomm : ∀ x ∈ level H w a, ∀ y ∈ level H w b, Commute (f x) (f y) := by
    intro x hx
    refine Subgroup.iSup_induction (factor H w a)
      (C := fun x => ∀ y ∈ level H w b, Commute (f x) (f y)) hx
      (fun i x hxi => ?_) ?_ (fun x x' hxx hx' y hy => ?_)
    · intro y hy
      rcases lt_or_ge (w i) a with hi | hi
      · rw [factor_of_lt H w hi] at hxi
        rw [Subgroup.mem_bot.mp hxi, map_one]
        exact Commute.one_left _
      rw [factor_of_le H w hi] at hxi
      refine Subgroup.iSup_induction (factor H w b)
        (C := fun y => Commute (f x) (f y)) hy
        (fun j y hyj => ?_) ?_ (fun y y' hxy hxy' => ?_)
      · rcases lt_or_ge (w j) b with hj | hj
        · rw [factor_of_lt H w hj] at hyj
          rw [Subgroup.mem_bot.mp hyj, map_one]
          exact Commute.one_right _
        rw [factor_of_le H w hj] at hyj
        apply commutatorElement_eq_one_iff_commute.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).2
          (antitone_level H w (Nat.add_le_add hi hj)
            (hc i j (Subgroup.commutator_mem_commutator hxi hyj)))
      · rw [map_one]
        exact Commute.one_right _
      · rw [map_mul]
        exact hxy.mul_right hxy'
    · intro y _
      rw [map_one]
      exact Commute.one_left _
    · rw [map_mul]
      exact (hxx y hy).mul_left (hx' y hy)
  apply (QuotientGroup.eq_one_iff _).1
  change f ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (hcomm x hx y hy)

end Langlands.GroupTheory.HeightFiltration

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Langlands.GroupTheory

variable {R : Type u} [CommRing R]
  {U : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}
  (W : RootWeightData C)

/-- Conjugation by a point of the first positive term changes a point of term d
by an element of the next term, on every scheme test. -/
theorem commutator_mem_next (T : Over (Spec (CommRingCat.of R))) (d : ℕ)
    {z x : T ⟶ U.X} (hz : z ∈ (W.subgroup 0).carrier T)
    (hx : x ∈ (W.subgroup d).carrier T) :
    ⁅z, x⁆ ∈ (W.subgroup (d + 1)).carrier T := by
  let N := (W.subgroup (d + 1)).carrier T
  have : N.Normal := ⟨fun x hx z => W.isNormal_subgroup (d + 1) T z x
    (Subgroup.mem_top _) hx⟩
  have hn : (HeightFiltration.level
      (rootFactor C.roots ULift.up T) W.weight (d + 1 + 1)).Normal := this
  have : (HeightFiltration.level
      (rootFactor C.roots ULift.up T) W.weight (1 + (d + 1))).Normal := by
    simpa only [Nat.add_comm 1] using hn
  have h := HeightFiltration.commutator_mem_level_add
    (rootFactor C.roots ULift.up T) W.weight (W.commutator T) 1 (d + 1) hz hx
  change ⁅z, x⁆ ∈ HeightFiltration.level
    (rootFactor C.roots ULift.up T) W.weight (d + 1 + 1)
  simpa only [Nat.add_comm 1] using h

/-- Two represented term points related by positive-term conjugation have the
same actual vector-quotient image. -/
theorem quotientMap_eq_of_positive_conjugation
    (T : Over (Spec (CommRingCat.of R))) (d : ℕ)
    {z : T ⟶ U.X} (hz : z ∈ (W.subgroup 0).carrier T)
    (x y : T ⟶ (W.groupScheme d).X)
    (hy : y ≫ (W.inclusion d).hom.hom =
      z * (x ≫ (W.inclusion d).hom.hom) * z⁻¹) :
    y ≫ (W.quotientMap d).hom.hom = x ≫ (W.quotientMap d).hom.hom := by
  have hx : x ≫ (W.inclusion d).hom.hom ∈ (W.subgroup d).carrier T :=
    ((W.isRepresentedBy_inclusion d).pointsEquiv T x).property
  have hc := W.commutator_mem_next T d hz hx
  have he := (W.quotientMap_eq_one_iff d T (y * x⁻¹)).2 (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hy]
    simpa only [commutatorElement_def] using hc)
  rw [MonObj.mul_comp, GrpObj.inv_comp] at he
  exact mul_inv_eq_one.mp he

/-- The actual first positive term acts by conjugation on every represented term. -/
def positiveConjugationAction (d : ℕ) :
    AutomorphicAction (W.groupScheme 0) (W.groupScheme d) :=
  (AutomorphicAction.conjugation (W.inclusion 0)).onRepresentedSubgroup
    (W.inclusion d) (W.isRepresentedBy_inclusion d) (by
      intro T z x hx
      rw [AutomorphicAction.conjugation_act]
      exact W.isNormal_subgroup d T _ _ (Subgroup.mem_top _) hx)

theorem positiveConjugationAction_comp (d : ℕ)
    {T : Over (Spec (CommRingCat.of R))}
    (z : T ⟶ (W.groupScheme 0).X) (x : T ⟶ (W.groupScheme d).X) :
    (W.positiveConjugationAction d).act z x ≫ (W.inclusion d).hom.hom =
      (z ≫ (W.inclusion 0).hom.hom) * (x ≫ (W.inclusion d).hom.hom) *
        (z ≫ (W.inclusion 0).hom.hom)⁻¹ := by
  rw [positiveConjugationAction, AutomorphicAction.onRepresentedSubgroup_act_comp,
    AutomorphicAction.conjugation_act]

/-- The actual positive-term action is trivial on the actual exact-weight quotient. -/
theorem quotientMap_positiveConjugationAction (d : ℕ)
    {T : Over (Spec (CommRingCat.of R))}
    (z : T ⟶ (W.groupScheme 0).X) (x : T ⟶ (W.groupScheme d).X) :
    (W.positiveConjugationAction d).act z x ≫ (W.quotientMap d).hom.hom =
      x ≫ (W.quotientMap d).hom.hom :=
  W.quotientMap_eq_of_positive_conjugation T d
    (((W.isRepresentedBy_inclusion 0).pointsEquiv T z).property)
    x _ (W.positiveConjugationAction_comp d z x)

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
