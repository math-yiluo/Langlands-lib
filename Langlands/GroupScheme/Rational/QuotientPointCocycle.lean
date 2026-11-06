import Langlands.GroupScheme.TorsorCocycle
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Kernel cocycles obstructing lifts of quotient points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientPointCocycle

variable {S : Scheme.{u}} {N G Q : GroupScheme S}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    {U : Over S} (y : Over.mk (𝟙 S) ⟶ Q.X)
    (g : U ⟶ G.X) (hg : g ≫ q.hom.hom = toUnit U ≫ y)

include hker hg in
/-- The difference between two restrictions of a local lift lies in the full kernel. -/
theorem difference_mem_range {Z : Over S} (a b : Z ⟶ U) :
    ∃ v : Z ⟶ N.X, v ≫ n.hom.hom = (a ≫ g) * (b ≫ g)⁻¹ := by
  apply SubgroupFunctor.mem_range.mp
  rw [hker, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, Category.assoc, hg, comp_toUnit_assoc, comp_toUnit_assoc,
    mul_inv_cancel]

variable [Mono n.hom.hom]

/-- The actual kernel-valued cocycle of a local lift of a quotient point. -/
def obstruction : Cocycle N U :=
  (Cocycle.coboundary g).lift n (difference_mem_range n q hker y g hg)

theorem obstruction_toFun_comp {Z : Over S} (a b : Z ⟶ U) :
    (obstruction n q hker y g hg).toFun a b ≫ n.hom.hom =
      (a ≫ g) * (b ≫ g)⁻¹ :=
  Cocycle.lift_toFun _ _ _ a b

include hker in
omit [Mono n.hom.hom] in
/-- Every point of the represented full kernel is killed by the quotient map. -/
theorem kernelPoint_comp {Z : Over S} (v : Z ⟶ N.X) :
    (v ≫ n.hom.hom) ≫ q.hom.hom = 1 := by
  apply (mem_range_kernelι_iff q _).mp
  rw [← hker]
  exact SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩

/-- A trivial obstruction corrects the local lift to a point over the base. -/
theorem exists_lift_of_isTrivial [EffectiveEpi U.hom]
    (h : (obstruction n q hker y g hg).IsTrivial) :
    ∃ x : Over.mk (𝟙 S) ⟶ G.X, x ≫ q.hom.hom = y := by
  obtain ⟨f, hf⟩ := h
  let c : U ⟶ G.X := (f ≫ n.hom.hom)⁻¹ * g
  have hc {Z : Over S} (a b : Z ⟶ U) : a ≫ c = b ≫ c := by
    have hab := congrArg (fun v : Z ⟶ N.X => v ≫ n.hom.hom) (hf a b)
    rw [obstruction_toFun_comp, MonObj.mul_comp, GrpObj.inv_comp,
      Category.assoc, Category.assoc] at hab
    dsimp only [c]
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
    calc
      (a ≫ f ≫ n.hom.hom)⁻¹ * (a ≫ g) =
          (a ≫ f ≫ n.hom.hom)⁻¹ *
            ((a ≫ g) * (b ≫ g)⁻¹) * (b ≫ g) := by group
      _ = _ := by rw [hab]; group
  obtain ⟨s, hs, hsbase⟩ := exists_section_of_forall_eq c hc
  let x : Over.mk (𝟙 S) ⟶ G.X := Over.homMk s hsbase
  have hx : toUnit U ≫ x = c := Over.OverMorphism.ext hs
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi U.hom).mp
  have he : toUnit U ≫ x ≫ q.hom.hom = toUnit U ≫ y := by
    rw [← Category.assoc, hx]
    dsimp only [c]
    rw [MonObj.mul_comp, GrpObj.inv_comp, kernelPoint_comp n q hker,
      inv_one, one_mul, hg]
  exact congrArg (fun v => v.left) he

/-- A point over the base trivializes the obstruction of every supplied local lift. -/
theorem isTrivial_of_exists_lift
    (h : ∃ x : Over.mk (𝟙 S) ⟶ G.X, x ≫ q.hom.hom = y) :
    (obstruction n q hker y g hg).IsTrivial := by
  obtain ⟨x, hx⟩ := h
  have hd : g * (toUnit U ≫ x)⁻¹ ∈ (SubgroupFunctor.range n).carrier U := by
    rw [hker, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp,
      Category.assoc, hx, hg, mul_inv_cancel]
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp hd
  refine ⟨f, fun {Z} a b => ?_⟩
  apply (cancel_mono n.hom.hom).mp
  rw [obstruction_toFun_comp, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, Category.assoc, hf, MonObj.comp_mul, MonObj.comp_mul,
    GrpObj.comp_inv, GrpObj.comp_inv, comp_toUnit_assoc, comp_toUnit_assoc]
  group

/-- Exactness at a quotient point, expressed by its actual cover cocycle. -/
theorem isTrivial_iff_exists_lift [EffectiveEpi U.hom] :
    (obstruction n q hker y g hg).IsTrivial ↔
      ∃ x : Over.mk (𝟙 S) ⟶ G.X, x ≫ q.hom.hom = y :=
  ⟨exists_lift_of_isTrivial n q hker y g hg,
    isTrivial_of_exists_lift n q hker y g hg⟩

include hker in
/-- Cocycles that all vanish on a fixed cover turn local lifts into
surjectivity on points over the base. -/
theorem surjective_of_local_lifts [EffectiveEpi U.hom]
    (hvanish : ∀ ξ : Cocycle N U, ξ.IsTrivial)
    (hlift : ∀ z : Over.mk (𝟙 S) ⟶ Q.X,
      ∃ v : U ⟶ G.X, v ≫ q.hom.hom = toUnit U ≫ z) :
    Function.Surjective
      (fun x : Over.mk (𝟙 S) ⟶ G.X => x ≫ q.hom.hom) := by
  intro z
  obtain ⟨v, hv⟩ := hlift z
  exact exists_lift_of_isTrivial n q hker z v hv
    (hvanish (obstruction n q hker z v hv))

end Langlands.GroupScheme.QuotientPointCocycle
