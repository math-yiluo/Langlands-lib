import Langlands.GroupScheme.SubgroupFunctor.FppfImage

/-! # Comparing subgroup functors by their quotient and kernel intersection -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {B : Scheme.{u}} {G Q : GroupScheme B}

/-- The part of an all-test subgroup lying in the full scheme-theoretic kernel
of a homomorphism. -/
def kernelIntersection (F : SubgroupFunctor G) (q : G ⟶ Q) : SubgroupFunctor G :=
  range (kernelι q) ⊓ F

theorem mem_kernelIntersection {F : SubgroupFunctor G} {q : G ⟶ Q}
    {T : Over B} {x : T ⟶ G.X} :
    x ∈ (F.kernelIntersection q).carrier T ↔
      x ≫ q.hom.hom = 1 ∧ x ∈ F.carrier T := by
  change x ∈ (range (kernelι q)).carrier T ∧ x ∈ F.carrier T ↔ _
  rw [mem_range_kernelι_iff]

/-- Comparison on any representative of the full kernel controls the kernel
intersection, without assuming that the whole kernel belongs to the subgroup. -/
theorem kernelIntersection_le_of_comap_le
    {F E : SubgroupFunctor G} {U : GroupScheme B} (q : G ⟶ Q) (r : U ⟶ G)
    (hk : range (kernelι q) = range r)
    (h : F.comap r ≤ E.comap r) : F.kernelIntersection q ≤ E := by
  intro T x hx
  have hxk : x ∈ (range r).carrier T := by
    rw [← hk]
    exact hx.1
  obtain ⟨y, rfl⟩ := mem_range.mp hxk
  exact h T hx.2

namespace IsFppfImage

/-- Two all-test subgroups agree if one is contained in the other, its fppf
quotient contains the other's image, and it contains their kernel intersection. -/
theorem eq_of_kernelIntersection_le
    {E F : SubgroupFunctor G} {E' : SubgroupFunctor Q} {q : G ⟶ Q}
    (h : IsFppfImage E E' q) (hEF : E ≤ F) (hF : F.map q ≤ E')
    (hker : F.kernelIntersection q ≤ E) : F = E := by
  apply le_antisymm
  · obtain ⟨H, K, i, j, p, hi, hj, hp, hpf, hps, hpl⟩ := h
    let : Mono i.hom.hom := hi.1
    let : Flat p.hom.hom.left := hpf
    let : Surjective p.hom.hom.left := hps
    let : LocallyOfFinitePresentation p.hom.hom.left := hpl
    intro T x hx
    have hxq : x ≫ q.hom.hom ∈ E'.carrier T :=
      hF T ⟨x, hx, rfl⟩
    rw [← hj.2] at hxq
    obtain ⟨y, hy⟩ := mem_range.mp hxq
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
    have hz : z ≫ i.hom.hom ∈ E.carrier V := by
      rw [← hi.2]
      exact mem_range.mpr ⟨z, rfl⟩
    have hd : (a ≫ x) * (z ≫ i.hom.hom)⁻¹ ∈ E.carrier V := by
      apply hker V
      rw [mem_kernelIntersection]
      exact ⟨by rw [MonObj.mul_comp, GrpObj.inv_comp, he, mul_inv_cancel],
        (F.carrier V).mul_mem (F.comp_mem a hx) ((F.carrier V).inv_mem (hEF V hz))⟩
    have hax : a ≫ x ∈ E.carrier V := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using (E.carrier V).mul_mem hd hz
    rw [← hi.2] at hax ⊢
    exact mem_range_of_comp_mem_range i a hax
  · exact hEF

end IsFppfImage

section Square

variable {H G' H' : GroupScheme B}
    {F : SubgroupFunctor G} {E : SubgroupFunctor H}
    {F' : SubgroupFunctor G'} {E' : SubgroupFunctor H'}
    (i : H ⟶ G) (q : G ⟶ G') (p : H ⟶ H') (i' : H' ⟶ G')

/-- Quotient comparison and comparison on the kernel intersection lift to an
intersection identity, using actual local lifts from the subgroup's fppf image. -/
theorem comap_eq_of_fppfImage_of_kernelIntersection_le
    (hsq : i ≫ q = p ≫ i')
    (hE : IsFppfImage E E' p) (hEF : E.map i ≤ F) (hF : F.map q ≤ F')
    (hquot : F'.comap i' = E')
    (hker : (F.comap i).kernelIntersection p ≤ E) : F.comap i = E := by
  apply hE.eq_of_kernelIntersection_le (map_le_iff_le_comap.mp hEF) _ hker
  intro T x hx
  obtain ⟨y, hy, rfl⟩ := hx
  change T ⟶ H.X at y
  rw [← hquot]
  change (y ≫ p.hom.hom) ≫ i'.hom.hom ∈ F'.carrier T
  have hs : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ i'.hom.hom :=
    congrArg (fun f => f.hom.hom) hsq
  rw [Category.assoc, ← hs, ← Category.assoc]
  exact hF T ⟨y ≫ i.hom.hom, hy, rfl⟩

end Square

end Langlands.GroupScheme.SubgroupFunctor
