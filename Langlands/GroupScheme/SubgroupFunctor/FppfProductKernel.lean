import Langlands.GroupScheme.SubgroupFunctor.FppfImage

/-! # Local products with the full kernel of an fppf subgroup image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {B : Scheme.{u}} {G Q : GroupScheme B}

/-- Actual cover and ordered factors lifting a point through an fppf subgroup
image, with the right factor in the full kernel. -/
structure KernelProductFactorization (F : SubgroupFunctor G) (q : G ⟶ Q)
    {T : Over B} (x : T ⟶ G.X) where
  cover : Over B
  projection : cover ⟶ T
  projection_flat : Flat projection.left
  projection_surjective : Surjective projection.left
  projection_lfp : LocallyOfFinitePresentation projection.left
  left : cover ⟶ G.X
  right : cover ⟶ G.X
  left_mem : left ∈ F.carrier cover
  right_eq_one : right ≫ q.hom.hom = 1
  factorization : projection ≫ x = left * right

namespace IsFppfImage

variable {F : SubgroupFunctor G} {E : SubgroupFunctor Q} {q : G ⟶ Q}

/-- Choose the actual pullback cover and kernel-product factorization from the
fppf morphism between subgroup representatives. -/
def kernelProductFactorization (h : IsFppfImage F E q)
    {T : Over B} (x : T ⟶ G.X) (hx : x ≫ q.hom.hom ∈ E.carrier T) :
    KernelProductFactorization F q x :=
  Classical.choice (by
    obtain ⟨H, K, i, j, p, hi, hj, hp, hpf, hps, hpl⟩ := h
    let : Flat p.hom.hom.left := hpf
    let : Surjective p.hom.hom.left := hps
    let : LocallyOfFinitePresentation p.hom.hom.left := hpl
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
    have haf : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
    have has : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
    have hal : LocallyOfFinitePresentation a.left := by
      change LocallyOfFinitePresentation (pullback.fst _ _)
      infer_instance
    have he : (a ≫ x) ≫ q.hom.hom = (z ≫ i.hom.hom) ≫ q.hom.hom := by
      rw [Category.assoc, ← hy, ← Category.assoc, haz, Category.assoc,
        Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hp]
    refine ⟨{ cover := V
              projection := a
              projection_flat := haf
              projection_surjective := has
              projection_lfp := hal
              left := z ≫ i.hom.hom
              right := (z ≫ i.hom.hom)⁻¹ * (a ≫ x)
              left_mem := ?_
              right_eq_one := ?_
              factorization := ?_ }⟩
    · rw [← hi.2]
      exact mem_range.mpr ⟨z, rfl⟩
    · rw [MonObj.mul_comp, GrpObj.inv_comp, he, inv_mul_cancel]
    · simp only [mul_inv_cancel_left])

/-- The inverse image of an actual fppf subgroup image is the fppf-local
ordered product of the source subgroup with the full scheme-theoretic kernel. -/
theorem fppfLocallyInProduct_kernel_iff (h : IsFppfImage F E q)
    {T : Over B} (x : T ⟶ G.X) :
    FppfLocallyInProduct F (range (kernelι q)) x ↔
      x ≫ q.hom.hom ∈ E.carrier T := by
  constructor
  · intro hx
    have hmap := h.map_le
    obtain ⟨H, K, i, j, p, hi, hj, hp, hpf, hps, hpl⟩ := h
    let : Mono j.hom.hom := hj.1
    obtain ⟨V, v, hf, hs, hl, f, n, hF, hn, he⟩ := hx
    let : Flat v.left := hf
    let : Surjective v.left := hs
    let : LocallyOfFinitePresentation v.left := hl
    have hv : v ≫ (x ≫ q.hom.hom) ∈ E.carrier V := by
      rw [← Category.assoc, he, MonObj.mul_comp,
        (mem_range_kernelι_iff q n).mp hn, mul_one]
      exact hmap V ⟨f, hF, rfl⟩
    rw [← hj.2] at hv ⊢
    exact mem_range_of_comp_mem_range j v hv
  · intro hx
    let d := h.kernelProductFactorization x hx
    exact ⟨d.cover, d.projection, d.projection_flat, d.projection_surjective,
      d.projection_lfp, d.left, d.right, d.left_mem,
      (mem_range_kernelι_iff q d.right).mpr d.right_eq_one, d.factorization⟩

end IsFppfImage

end Langlands.GroupScheme.SubgroupFunctor
