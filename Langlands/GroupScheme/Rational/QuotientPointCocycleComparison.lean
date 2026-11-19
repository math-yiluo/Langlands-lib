import Langlands.GroupScheme.Rational.QuotientPointCocycle
import Langlands.GroupScheme.CocycleCohomology

/-! # Recovering and comparing quotient points from cocycles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientPointCocycle

variable {S : Scheme.{u}} {N G Q : GroupScheme S} {U : Over S}
  (n : N ⟶ G) (q : G ⟶ Q)
  (hker : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
  [Mono n.hom.hom]

set_option backward.isDefEq.respectTransparency false in
/-- A cocycle whose image in the ambient group is a coboundary comes from
a quotient point and a lift of that point on the same cover. -/
theorem exists_quotientPoint_of_isTrivial_map [EffectiveEpi U.hom]
    (ξ : Cocycle N U) (hξ : (ξ.map n).IsTrivial) :
    ∃ (y : 𝟙_ (Over S) ⟶ Q.X) (g : U ⟶ G.X) (hg : g ≫ q.hom.hom = toUnit U ≫ y),
      ∀ {Z : Over S} (a b : Z ⟶ U),
        ξ.toFun a b = (obstruction n q hker y g hg).toFun a b := by
  obtain ⟨g, hg⟩ := hξ
  have hcomp {Z : Over S} (a b : Z ⟶ U) : a ≫ g ≫ q.hom.hom = b ≫ g ≫ q.hom.hom := by
    have h := congrArg (fun t : Z ⟶ G.X => t ≫ q.hom.hom) (hg a b)
    change (ξ.toFun a b ≫ n.hom.hom) ≫ q.hom.hom =
      ((a ≫ g) * (b ≫ g)⁻¹) ≫ q.hom.hom at h
    rw [kernelPoint_comp n q hker, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      Category.assoc] at h
    exact mul_inv_eq_one.mp h.symm
  obtain ⟨s, hs, hsbase⟩ := exists_section_of_forall_eq (g ≫ q.hom.hom) hcomp
  let y : 𝟙_ (Over S) ⟶ Q.X := Over.homMk s hsbase
  have hy : g ≫ q.hom.hom = toUnit U ≫ y :=
    Over.OverMorphism.ext hs.symm
  refine ⟨y, g, hy, fun a b => (cancel_mono n.hom.hom).mp ?_⟩
  rw [obstruction_toFun_comp]
  exact hg a b

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying the quotient point by the image of a base point of the
ambient group leaves the class of the obstruction unchanged. -/
theorem cohomologous_obstruction_of_mul
    (y y' : 𝟙_ (Over S) ⟶ Q.X) (x : 𝟙_ (Over S) ⟶ G.X)
    (g g' : U ⟶ G.X) (hg : g ≫ q.hom.hom = toUnit U ≫ y)
    (hg' : g' ≫ q.hom.hom = toUnit U ≫ y')
    (h : y' = y * (x ≫ q.hom.hom)) :
    (obstruction n q hker y g hg).Cohomologous (obstruction n q hker y' g' hg') := by
  let u := toUnit U ≫ x
  have hu : (g * u) ≫ q.hom.hom = toUnit U ≫ y' := by
    rw [MonObj.mul_comp, hg, h, MonObj.comp_mul]
    simp only [u, Category.assoc]
  have hk : g' * (g * u)⁻¹ ∈ (SubgroupFunctor.range n).carrier U := by
    rw [hker, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, hg', hu, mul_inv_cancel]
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp hk
  have hfg : g' = (f ≫ n.hom.hom) * g * u := by rw [hf]; group
  have hp {Z : Over S} (a : Z ⟶ U) :
      a ≫ g' = (a ≫ f ≫ n.hom.hom) * (a ≫ g) * (toUnit Z ≫ x) := by
    rw [hfg]
    simp only [MonObj.comp_mul, u, comp_toUnit_assoc]
  refine ⟨f⁻¹, fun a b => (cancel_mono n.hom.hom).mp ?_⟩
  rw [obstruction_toFun_comp, hp a, hp b]
  simp only [Cocycle.twist, MonObj.mul_comp, GrpObj.comp_inv, GrpObj.inv_comp,
    inv_inv, Category.assoc, obstruction_toFun_comp]
  group

/-- The kernel-valued obstruction exhausts cocycles that become coboundaries
and depends only on the quotient point modulo an ambient base point. -/
def QuotientPointCocycleComparisonStatement : Prop :=
  ∀ {S : Scheme.{u}} {N G Q : GroupScheme S} {U : Over S}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [EffectiveEpi U.hom],
    (∀ (ξ : Cocycle N U), (ξ.map n).IsTrivial →
      ∃ (y : 𝟙_ (Over S) ⟶ Q.X) (g : U ⟶ G.X) (hg : g ≫ q.hom.hom = toUnit U ≫ y),
        ∀ {Z : Over S} (a b : Z ⟶ U),
          ξ.toFun a b = (obstruction n q hker y g hg).toFun a b) ∧
    (∀ (y y' : 𝟙_ (Over S) ⟶ Q.X) (x : 𝟙_ (Over S) ⟶ G.X)
      (g g' : U ⟶ G.X) (hg : g ≫ q.hom.hom = toUnit U ≫ y)
      (hg' : g' ≫ q.hom.hom = toUnit U ≫ y'), y' = y * (x ≫ q.hom.hom) →
      (obstruction n q hker y g hg).Cohomologous (obstruction n q hker y' g' hg'))

theorem quotientPointCocycleComparison : QuotientPointCocycleComparisonStatement.{u} := by
  intro S N G Q U n q hker _ _
  exact ⟨exists_quotientPoint_of_isTrivial_map n q hker,
    cohomologous_obstruction_of_mul n q hker⟩

end Langlands.GroupScheme.QuotientPointCocycle
