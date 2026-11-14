import Langlands.GroupScheme.SubgroupFunctor.FppfImage

/-! # Containment of full inverse images using fppf subgroup images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {B : Scheme.{u}} {G Q H : GroupScheme B}
    {F : SubgroupFunctor G} {E : SubgroupFunctor Q} {q : G ⟶ Q}

/-- If a monomorphic subgroup contains both a subgroup with a given actual
fppf image and the full quotient kernel, it contains the full inverse image
of that fppf image. -/
theorem IsFppfImage.comap_le_range
    (h : IsFppfImage F E q) (i : H ⟶ G) [Mono i.hom.hom]
    (hF : F ≤ range i) (hker : range (kernelι q) ≤ range i) :
    E.comap q ≤ range i := by
  obtain ⟨A, C, j, l, p, hj, hl, hp, hpf, hps, hpl⟩ := h
  let : Flat p.hom.hom.left := hpf
  let : Surjective p.hom.hom.left := hps
  let : LocallyOfFinitePresentation p.hom.hom.left := hpl
  intro T x hx
  change x ≫ q.hom.hom ∈ E.carrier T at hx
  rw [← hl.2] at hx
  obtain ⟨y, hy⟩ := mem_range.mp hx
  let V : Over B := Over.mk (pullback.fst y.left p.hom.hom.left ≫ T.hom)
  let a : V ⟶ T := Over.homMk (pullback.fst y.left p.hom.hom.left) rfl
  let z : V ⟶ A.X := Over.homMk (pullback.snd y.left p.hom.hom.left) (by
    rw [← Over.w p.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  have haz : a ≫ y = z ≫ p.hom.hom := Over.OverMorphism.ext pullback.condition
  have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  have he : (a ≫ x) ≫ q.hom.hom = (z ≫ j.hom.hom) ≫ q.hom.hom := by
    rw [Category.assoc, ← hy, ← Category.assoc, haz, Category.assoc,
      Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hp]
  have hd : (a ≫ x) * (z ≫ j.hom.hom)⁻¹ ∈ (range i).carrier V := by
    apply hker V
    apply (mem_range_kernelι_iff q _).mpr
    rw [MonObj.mul_comp, GrpObj.inv_comp, he, mul_inv_cancel]
  have hz : z ≫ j.hom.hom ∈ (range i).carrier V := by
    apply hF V
    rw [← hj.2]
    exact mem_range.mpr ⟨z, rfl⟩
  have hax : a ≫ x ∈ (range i).carrier V := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      ((range i).carrier V).mul_mem hd hz
  exact mem_range_of_comp_mem_range i a hax

/-- The canonical inclusion on each test scheme induced by full inverse-image
containment; the underlying ambient point is unchanged. -/
def IsFppfImage.comapRangeInclusion
    (h : IsFppfImage F E q) (i : H ⟶ G) [Mono i.hom.hom]
    (hF : F ≤ range i) (hker : range (kernelι q) ≤ range i)
    (T : Over B) :
    (E.comap q).carrier T →* (range i).carrier T :=
  Subgroup.inclusion (h.comap_le_range i hF hker T)

@[simp]
theorem IsFppfImage.comapRangeInclusion_val
    (h : IsFppfImage F E q) (i : H ⟶ G) [Mono i.hom.hom]
    (hF : F ≤ range i) (hker : range (kernelι q) ≤ range i)
    (T : Over B) (x : (E.comap q).carrier T) :
    (h.comapRangeInclusion i hF hker T x).val = x.val := rfl

end Langlands.GroupScheme.SubgroupFunctor
