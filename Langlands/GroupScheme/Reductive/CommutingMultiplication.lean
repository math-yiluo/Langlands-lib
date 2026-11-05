import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.SemidirectProduct
import Langlands.GroupScheme.CentralIsogeny.ProjectionCentralIsogeny

/-! # Multiplication of commuting subgroup schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {H K G : GroupScheme S}
variable (j : H ⟶ G) (i : K ⟶ G)
variable (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
  Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))

include hc in
/-- Multiplication of two commuting subgroup maps is multiplicative on all tests. -/
theorem subgroupMultiplication_mul {T : Over S} (x y : T ⟶ H.X ⊗ K.X) :
    (x * y) ≫ subgroupMultiplication j i =
      (x ≫ subgroupMultiplication j i) * (y ≫ subgroupMultiplication j i) := by
  simp only [subgroupMultiplication, MonObj.comp_mul, ← Category.assoc,
    MonObj.mul_comp]
  exact (hc T (y ≫ fst H.X K.X) (x ≫ snd H.X K.X)).mul_mul_mul_comm _ _

/-- The actual subgroup multiplication map is a homomorphism when the two
images commute on every test scheme. -/
def commutingSubgroupMultiplicationHom : H ⊗ K ⟶ G := by
  letI : IsMonHom (subgroupMultiplication j i) :=
    Semidirect.isMonHom_of_mul_comp _ (fun x y => subgroupMultiplication_mul j i hc x y)
  exact Grp.homMk (subgroupMultiplication j i)

@[simp] theorem commutingSubgroupMultiplicationHom_hom :
    (commutingSubgroupMultiplicationHom j i hc).hom.hom = subgroupMultiplication j i :=
  rfl

/-- The product multiplication image contains the image of its first factor. -/
theorem range_left_le_commutingSubgroupMultiplicationHom :
    SubgroupFunctor.range j ≤
      SubgroupFunctor.range (commutingSubgroupMultiplicationHom j i hc) := by
  intro T x hx
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨lift h 1, ?_⟩
  change lift h 1 ≫ subgroupMultiplication j i = h ≫ j.hom.hom
  rw [comp_subgroupMultiplication, MonObj.one_comp, mul_one]

/-- The product multiplication image contains the image of its second factor. -/
theorem range_right_le_commutingSubgroupMultiplicationHom :
    SubgroupFunctor.range i ≤
      SubgroupFunctor.range (commutingSubgroupMultiplicationHom j i hc) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨lift 1 y, ?_⟩
  change lift 1 y ≫ subgroupMultiplication j i = y ≫ i.hom.hom
  rw [comp_subgroupMultiplication, MonObj.one_comp, one_mul]

end Base

section Field

variable {k : Type u} [Field k]
variable {H K G : GroupScheme (Spec (CommRingCat.of k))}

/-- Surjective multiplication of commuting quasi-compact finite-type factors onto a
smooth group is flat, including nonsmooth factors. -/
theorem subgroupMultiplication_flat_of_surjective
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [LocallyOfFiniteType K.X.hom] [QuasiCompact K.X.hom] [Smooth G.X.hom]
    (j : H ⟶ G) (i : K ⟶ G)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left) :
    Flat (subgroupMultiplication j i).left := by
  let f := commutingSubgroupMultiplicationHom j i hc
  have : Surjective f.hom.hom.left := hs
  have : LocallyOfFiniteType (H ⊗ K).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.fst H.X.hom K.X.hom ≫ H.X.hom)
    infer_instance
  have : QuasiCompact (H ⊗ K).X.hom := by
    change QuasiCompact (Limits.pullback.fst H.X.hom K.X.hom ≫ H.X.hom)
    infer_instance
  exact flat_of_surjective f

/-- For closed commuting subgroups of a smooth affine group, surjectivity of
multiplication suffices for its flatness. -/
theorem subgroupMultiplication_flat_of_closedSubgroups
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left) :
    Flat (subgroupMultiplication j i).left := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion i.hom.hom.left := hi
  have : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : LocallyOfFiniteType K.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : QuasiCompact H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : QuasiCompact K.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact subgroupMultiplication_flat_of_surjective j i hc hs

end Field

end Langlands.GroupScheme
