import Langlands.GroupScheme.SubgroupFunctor

/-! # Range transport through group-scheme monomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {H K G : GroupScheme S}

/-- Postcomposition carries the image of `i` to the image of `i ≫ j` on each
test scheme. -/
def rangePostcompHom (i : H ⟶ K) (j : K ⟶ G) (U : Over S) :
    (range i).carrier U →* (range (i ≫ j)).carrier U where
  toFun x := ⟨x.1 ≫ j.hom.hom, by
    obtain ⟨y, hy⟩ := mem_range.mp x.2
    apply mem_range.mpr
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy]⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.1 y.1 _)

/-- Postcomposition by a monomorphism identifies the two range groups on each
test scheme. -/
def rangePostcompEquiv (i : H ⟶ K) (j : K ⟶ G) [Mono j.hom.hom] (U : Over S) :
    (range i).carrier U ≃* (range (i ≫ j)).carrier U :=
  MulEquiv.ofBijective (rangePostcompHom i j U) ⟨by
    intro x y h
    apply Subtype.ext
    exact (cancel_mono j.hom.hom).mp (congrArg Subtype.val h), by
    intro x
    obtain ⟨y, hy⟩ := mem_range.mp x.2
    refine ⟨⟨y ≫ i.hom.hom, mem_range.mpr ⟨y, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change (y ≫ i.hom.hom) ≫ j.hom.hom = x.1
    rw [Category.assoc, ← Grp.comp_hom_hom]
    exact hy⟩

@[simp] theorem rangePostcompEquiv_apply_coe (i : H ⟶ K) (j : K ⟶ G)
    [Mono j.hom.hom] (U : Over S) (x : (range i).carrier U) :
    (rangePostcompEquiv i j U x : U ⟶ G.X) = (x : U ⟶ K.X) ≫ j.hom.hom :=
  rfl

/-- A monic postcomposition reflects and preserves triviality of the all-test
range subgroup functor. -/
theorem range_comp_eq_bot_iff (i : H ⟶ K) (j : K ⟶ G) [Mono j.hom.hom] :
    range (i ≫ j) = ⊥ ↔ range i = ⊥ := by
  constructor
  · intro h
    apply ext
    intro U
    rw [bot_carrier]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply (cancel_mono j.hom.hom).mp
    rw [MonObj.one_comp]
    have hx' := (rangePostcompHom i j U ⟨x, hx⟩).2
    change x ≫ j.hom.hom ∈ (range (i ≫ j)).carrier U at hx'
    rwa [h, bot_carrier, Subgroup.mem_bot] at hx'
  · intro h
    apply ext
    intro U
    rw [bot_carrier]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy⟩ := mem_range.mp hx
    have hy' : y ≫ i.hom.hom ∈ (range i).carrier U := mem_range.mpr ⟨y, rfl⟩
    rw [h, bot_carrier, Subgroup.mem_bot] at hy'
    rw [← hy, Grp.comp_hom_hom, ← Category.assoc, hy', MonObj.one_comp]

end Langlands.GroupScheme.SubgroupFunctor
