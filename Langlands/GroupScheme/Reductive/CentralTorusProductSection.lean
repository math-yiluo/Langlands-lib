import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Surjectivity of a subgroup product from surjectivity onto a quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G Z D Q : GroupScheme S}

set_option linter.defProp false in
/-- If every point in the kernel of `q` factors through `i`, and `d` followed by `q` is
surjective on underlying schemes, then multiplying the images of `i` and `d` is surjective
on underlying schemes. A section of the product map is built on the fibre product of `q`
and `d ≫ q`, whose first projection is surjective by base change. -/
def surjective_subgroupProductMap_of_kernel_le_of_surjective_comp
    (i : Z ⟶ G) (d : D ⟶ G) (q : G ⟶ Q)
    (hker : SubgroupFunctor.kernel q ≤ SubgroupFunctor.range i)
    (hs : Function.Surjective (d ≫ q).hom.hom.left) :
    Function.Surjective (subgroupProductMap i d).left := by
  let f := q.hom.hom.left
  let g := (d ≫ q).hom.hom.left
  let P : Over S := Over.mk (pullback.fst f g ≫ G.X.hom)
  let p₁ : P ⟶ G.X := Over.homMk (pullback.fst f g)
  let p₂ : P ⟶ D.X := Over.homMk (pullback.snd f g) (by
    change pullback.snd f g ≫ D.X.hom = pullback.fst f g ≫ G.X.hom
    rw [← Over.w (d ≫ q).hom.hom, ← Over.w q.hom.hom, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Q.X.hom) pullback.condition.symm)
  have hcomm : p₁ ≫ q.hom.hom = p₂ ≫ d.hom.hom ≫ q.hom.hom := by
    ext
    exact pullback.condition
  have hmem : p₁ * (p₂ ≫ d.hom.hom)⁻¹ ∈ (SubgroupFunctor.kernel q).carrier P := by
    change (p₁ * (p₂ ≫ d.hom.hom)⁻¹) ≫ q.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hcomm, Category.assoc, mul_inv_cancel]
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp (hker P hmem)
  have hsec : lift z p₂ ≫ subgroupProductMap i d = p₁ := by
    simp only [subgroupProductMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hz,
      inv_mul_cancel_right]
  have : Surjective g := ⟨hs⟩
  have hsurj : Function.Surjective (pullback.fst f g) :=
    (inferInstance : Surjective (pullback.fst f g)).surj
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  refine ⟨(lift z p₂).left y, ?_⟩
  have h := congrArg (fun φ : P ⟶ G.X => φ.left y) hsec
  simpa [p₁, Scheme.Hom.comp_apply] using h

/-- Specialization to a represented fppf quotient whose kernel is the range of `i`. -/
theorem surjective_subgroupProductMap_of_isFppfQuotient
    (i : Z ⟶ G) (d : D ⟶ G) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hs : Function.Surjective (d ≫ q).hom.hom.left) :
    Function.Surjective (subgroupProductMap i d).left := by
  refine surjective_subgroupProductMap_of_kernel_le_of_surjective_comp i d q ?_ hs
  rw [← hq.2.2.2, SubgroupFunctor.range_kernelι]

end Langlands.GroupScheme
