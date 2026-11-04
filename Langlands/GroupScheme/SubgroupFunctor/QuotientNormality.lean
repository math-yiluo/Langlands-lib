import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Normality in fpqc quotient squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {G Q H R : GroupScheme S}

/-- Membership in a represented subgroup can be tested after locally lifting
any chosen point along an fpqc quotient. -/
theorem mem_range_of_local_quotient_lift (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left] (i : H ⟶ R) [Mono i.hom.hom]
    {T : Over S} (x : T ⟶ Q.X) (z : T ⟶ R.X)
    (h : ∀ (V : Over S) (a : V ⟶ T) (g : V ⟶ G.X),
      a ≫ x = g ≫ q.hom.hom → a ≫ z ∈ (range i).carrier V) :
    z ∈ (range i).carrier T := by
  let V : Over S := Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let a : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let g : V ⟶ G.X := Over.homMk (pullback.snd x.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have : EffectiveEpi a.left := by
    change EffectiveEpi (pullback.fst x.left q.hom.hom.left)
    infer_instance
  exact mem_range_of_comp_mem_range i a
    (h V a g (Over.OverMorphism.ext pullback.condition))

variable {B BQ : GroupScheme S}

/-- In a commuting quotient square with fpqc vertical maps and monic target
inclusion, normality of the original subgroup descends to the quotient subgroup. -/
theorem isNormal_range_of_fpqc_square
    (i : B ⟶ G) (q : G ⟶ Q) (p : B ⟶ BQ) (j : BQ ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left] [Mono j.hom.hom]
    (hsquare : i ≫ q = p ≫ j) (hnormal : (range i).IsNormal) :
    (range j).IsNormal := by
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  apply mem_range_of_local_quotient_lift q j g
  intro V a g' hg
  apply mem_range_of_local_quotient_lift p j (a ≫ y)
  intro W b y' hy
  have hs : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom) hsquare
  have hnormal' := hnormal W (b ≫ g') (y' ≫ i.hom.hom)
    (Subgroup.mem_top _) (mem_range.mpr ⟨y', rfl⟩)
  obtain ⟨z, hz⟩ := mem_range.mp hnormal'
  refine mem_range.mpr ⟨z ≫ p.hom.hom, ?_⟩
  calc
    (z ≫ p.hom.hom) ≫ j.hom.hom =
        (z ≫ i.hom.hom) ≫ q.hom.hom := by
      rw [Category.assoc, ← hs, ← Category.assoc]
    _ = ((b ≫ g') * (y' ≫ i.hom.hom) * (b ≫ g')⁻¹) ≫ q.hom.hom := by rw [hz]
    _ = b ≫ (a ≫ (g * (y ≫ j.hom.hom) * g⁻¹)) := by
      simp only [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul,
        GrpObj.comp_inv, Category.assoc]
      rw [← hg, hs, ← Category.assoc y' p.hom.hom j.hom.hom, ← hy]
      simp only [Category.assoc]

end Langlands.GroupScheme.SubgroupFunctor
