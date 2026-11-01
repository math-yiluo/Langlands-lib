import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureSubgroupStatement

/-! # Actual sections in the two-power torsion closure -/

noncomputable section
open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u
variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

private lemma comp_mulRight (s t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    s ≫ (GrpObj.mulRight t).hom = s * t := by
  change s ≫ ((𝟙 A.X) * (toUnit A.X ≫ t)) = s * t
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  have h : s ≫ toUnit A.X = 𝟙 _ := toUnit_unique _ _
  rw [h, Category.id_comp]

private lemma mulRight_apply_section
    (s t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (GrpObj.mulRight t).hom.left (s.left (default : Spec (CommRingCat.of K))) =
      (s * t).left (default : Spec (CommRingCat.of K)) := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mulRight]

private lemma section_torsion_one :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left
      (default : Spec (CommRingCat.of K)) ∈ twoPowerTorsionLocus A := by
  exact ⟨0, 1, by simp, rfl⟩

private lemma torsion_pow_mul
    (s t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (n m : ℕ) (hs : s ^ (2 ^ n) = 1) (ht : t ^ (2 ^ m) = 1) :
    (s * t) ^ (2 ^ (n + m)) = 1 := by
  rw [mul_pow]
  have hs' : s ^ (2 ^ (n + m)) = 1 := by
    rw [pow_add, pow_mul, hs, one_pow]
  have ht' : t ^ (2 ^ (n + m)) = 1 := by
    rw [Nat.add_comm, pow_add, pow_mul, ht, one_pow]
  rw [hs', ht', one_mul]

private lemma inv_mapsTo_locus :
    Set.MapsTo (ι[A.X].left) (twoPowerTorsionLocus A) (twoPowerTorsionLocus A) := by
  rintro x ⟨n, s, hs, rfl⟩
  refine ⟨n, s⁻¹, by simp [inv_pow, hs], ?_⟩
  rw [Hom.inv_def, Over.comp_left, Scheme.Hom.comp_apply]

private lemma inv_mapsTo_closure :
    Set.MapsTo (ι[A.X].left) (closure (twoPowerTorsionLocus A))
      (closure (twoPowerTorsionLocus A)) :=
  (inv_mapsTo_locus A).closure (ι[A.X].left.continuous)

private lemma torsion_mulRight_mapsTo_closure
    (t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (m : ℕ) (ht : t ^ (2 ^ m) = 1) :
    Set.MapsTo (GrpObj.mulRight t).hom.left (closure (twoPowerTorsionLocus A))
      (closure (twoPowerTorsionLocus A)) := by
  apply Set.MapsTo.closure _ (GrpObj.mulRight t).hom.left.continuous
  rintro x ⟨n, s, hs, rfl⟩
  exact ⟨n + m, s * t, torsion_pow_mul A s t n m hs ht,
    (mulRight_apply_section A s t).symm⟩

private lemma mulRight_mapsTo_closure
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (hs : s.left (default : Spec (CommRingCat.of K)) ∈ closure (twoPowerTorsionLocus A)) :
    Set.MapsTo (GrpObj.mulRight s).hom.left (closure (twoPowerTorsionLocus A))
      (closure (twoPowerTorsionLocus A)) := by
  apply Set.MapsTo.closure_left _ (GrpObj.mulRight s).hom.left.continuous isClosed_closure
  rintro x ⟨n, t, ht, rfl⟩
  rw [mulRight_apply_section, mul_comm, ← mulRight_apply_section]
  exact torsion_mulRight_mapsTo_closure A t n ht hs

/-- The actual sections landing in the Zariski closure form a subgroup. -/
def twoPowerTorsionClosureSectionSubgroup :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) where
  carrier := {s | s.left (default : Spec (CommRingCat.of K)) ∈ closure (twoPowerTorsionLocus A)}
  one_mem' := subset_closure (section_torsion_one A)
  mul_mem' := by
    intro s t hs ht
    change (s * t).left (default : Spec (CommRingCat.of K)) ∈
      closure (twoPowerTorsionLocus A)
    rw [← mulRight_apply_section]
    exact mulRight_mapsTo_closure A t ht hs
  inv_mem' := by
    intro s hs
    change (s⁻¹).left (default : Spec (CommRingCat.of K)) ∈
      closure (twoPowerTorsionLocus A)
    rw [Hom.inv_def]
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact inv_mapsTo_closure A hs

/-- Translation by any section in the closure preserves the entire closure. -/
theorem image_closure_twoPowerTorsionLocus_mulRight
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (hs : s.left (default : Spec (CommRingCat.of K)) ∈ closure (twoPowerTorsionLocus A)) :
    (GrpObj.mulRight s).hom.left '' closure (twoPowerTorsionLocus A) =
      closure (twoPowerTorsionLocus A) := by
  apply Set.Subset.antisymm (mulRight_mapsTo_closure A s hs).image_subset
  intro x hx
  have hsinv : s⁻¹ ∈ twoPowerTorsionClosureSectionSubgroup A :=
    (twoPowerTorsionClosureSectionSubgroup A).inv_mem hs
  refine ⟨(GrpObj.mulRight s⁻¹).hom.left x, mulRight_mapsTo_closure A s⁻¹ hsinv hx, ?_⟩
  have hcomp : (GrpObj.mulRight s⁻¹).hom ≫ (GrpObj.mulRight s).hom = 𝟙 A.X := by
    change ((𝟙 A.X) * (toUnit A.X ≫ s⁻¹)) ≫
      ((𝟙 A.X) * (toUnit A.X ≫ s)) = 𝟙 A.X
    rw [MonObj.comp_mul]
    simp [GrpObj.comp_inv]
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hcomp]
  rfl

/-- The exact section-level closed-subgroup prerequisite. -/
theorem twoPowerTorsionClosureSubgroup : TwoPowerTorsionClosureSubgroupStatement.{u} := by
  intro K _ A
  refine ⟨twoPowerTorsionClosureSectionSubgroup A, fun _ => Iff.rfl, ?_⟩
  intro s hs
  exact image_closure_twoPowerTorsionLocus_mulRight A s hs

end Langlands.AbelianScheme.Tate
