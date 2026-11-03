import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Fppf images and full inverse images of represented subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {B : Scheme.{u}} {G Q : GroupScheme B}

/-- A homomorphism induces an actual fppf morphism between representatives of
its source and target subgroup functors. -/
def IsFppfImage (F : SubgroupFunctor G) (E : SubgroupFunctor Q) (q : G ⟶ Q) : Prop :=
  ∃ (H K : GroupScheme B) (i : H ⟶ G) (j : K ⟶ Q) (p : H ⟶ K),
    F.IsRepresentedBy i ∧ E.IsRepresentedBy j ∧ i ≫ q = p ≫ j ∧
      Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
        LocallyOfFinitePresentation p.hom.hom.left

namespace IsFppfImage

variable {F : SubgroupFunctor G} {E : SubgroupFunctor Q} {q : G ⟶ Q}

/-- An actual fppf image contains the ordinary all-test image. -/
theorem map_le (h : IsFppfImage F E q) : F.map q ≤ E := by
  obtain ⟨H, K, i, j, p, hi, hj, hp, _, _, _⟩ := h
  rintro T x ⟨g, hg, rfl⟩
  rw [← hi.2] at hg
  obtain ⟨y, rfl⟩ := mem_range.mp hg
  rw [← hj.2]
  refine mem_range.mpr ⟨y ≫ p.hom.hom, ?_⟩
  change (y ≫ p.hom.hom) ≫ j.hom.hom = (y ≫ i.hom.hom) ≫ q.hom.hom
  rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hp]

/-- If a represented subgroup contains the full actual kernel, it is the
full inverse image of its actual fppf image. -/
theorem comap_eq_of_kernel_le (h : IsFppfImage F E q)
    (hker : range (kernelι q) ≤ F) : E.comap q = F := by
  apply le_antisymm
  · obtain ⟨H, K, i, j, p, hi, hj, hp, hpf, hps, hpl⟩ := h
    let : Mono i.hom.hom := hi.1
    let : Flat p.hom.hom.left := hpf
    let : Surjective p.hom.hom.left := hps
    let : LocallyOfFinitePresentation p.hom.hom.left := hpl
    intro T x hx
    change x ≫ q.hom.hom ∈ E.carrier T at hx
    rw [← hj.2] at hx
    obtain ⟨y, hy⟩ := mem_range.mp hx
    let V : Over B := Over.mk (pullback.fst y.left p.hom.hom.left ≫ T.hom)
    let a : V ⟶ T := Over.homMk (pullback.fst y.left p.hom.hom.left) rfl
    let z : V ⟶ H.X := Over.homMk (pullback.snd y.left p.hom.hom.left) (by
      rw [← Over.w p.hom.hom, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w y]
      rfl)
    have haz : a ≫ y = z ≫ p.hom.hom :=
      Over.OverMorphism.ext pullback.condition
    have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
    have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
    have : LocallyOfFinitePresentation a.left := by
      change LocallyOfFinitePresentation (pullback.fst _ _)
      infer_instance
    have he : (a ≫ x) ≫ q.hom.hom = (z ≫ i.hom.hom) ≫ q.hom.hom := by
      rw [Category.assoc, ← hy, ← Category.assoc, haz, Category.assoc,
        Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hp]
    have hd : (a ≫ x) * (z ≫ i.hom.hom)⁻¹ ∈ F.carrier V := by
      apply hker V
      apply (mem_range_kernelι_iff q _).mpr
      rw [MonObj.mul_comp, GrpObj.inv_comp, he, mul_inv_cancel]
    have hz : z ≫ i.hom.hom ∈ F.carrier V := by
      rw [← hi.2]
      exact mem_range.mpr ⟨z, rfl⟩
    have hax : a ≫ x ∈ F.carrier V := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using (F.carrier V).mul_mem hd hz
    rw [← hi.2] at hax ⊢
    exact mem_range_of_comp_mem_range i a hax
  · exact map_le_iff_le_comap.mp h.map_le

end IsFppfImage

section Square

variable {H G' H' : GroupScheme B}
    {F : SubgroupFunctor G} {E : SubgroupFunctor H}
    {F' : SubgroupFunctor G'} {E' : SubgroupFunctor H'}
    (j : H ⟶ G) (q : G ⟶ G') (p : H ⟶ H') (j' : H' ⟶ G')

/-- Equality of subgroup inverse images descends through a commuting quotient
square when both subgroups are already full inverse images. -/
theorem comap_eq_of_quotient_square (hsq : j ≫ q = p ≫ j')
    (hF : F'.comap q = F) (hE : E'.comap p = E)
    (hcomp : F'.comap j' = E') : F.comap j = E := by
  rw [← hF, ← comap_comp, hsq, comap_comp, hcomp, hE]

/-- Actual fppf subgroup images containing the full quotient kernels provide
both full inverse-image identities needed for a quotient-square comparison. -/
theorem comap_eq_of_fppfImage_quotient_square (hsq : j ≫ q = p ≫ j')
    (hF : IsFppfImage F F' q) (hE : IsFppfImage E E' p)
    (hkerF : range (kernelι q) ≤ F) (hkerE : range (kernelι p) ≤ E)
    (hcomp : F'.comap j' = E') : F.comap j = E :=
  comap_eq_of_quotient_square j q p j' hsq
    (hF.comap_eq_of_kernel_le hkerF) (hE.comap_eq_of_kernel_le hkerE) hcomp

end Square

end Langlands.GroupScheme.SubgroupFunctor
