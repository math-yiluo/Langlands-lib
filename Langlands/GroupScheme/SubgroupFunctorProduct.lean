import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Exact products of subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- `F` is the pointwise product `A B`: every point is exactly a product of one
point of `A` and one point of `B`, over the same test scheme. -/
def IsPointwiseProduct (F A B : SubgroupFunctor G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G.X),
    x ∈ F.carrier T ↔
      ∃ a ∈ A.carrier T, ∃ b ∈ B.carrier T, a * b = x

/-- The exact product `A N` when `A` normalizes `N`. Its carrier is the
two-factor product itself on every test scheme. -/
def normalizedProduct (A N : SubgroupFunctor G) (hN : N.IsNormalizedBy A) :
    SubgroupFunctor G where
  carrier T :=
    { carrier := {x | ∃ a ∈ A.carrier T, ∃ n ∈ N.carrier T, a * n = x}
      one_mem' := ⟨1, (A.carrier T).one_mem, 1, (N.carrier T).one_mem, one_mul 1⟩
      mul_mem' := by
        rintro x y ⟨a, ha, n, hn, rfl⟩ ⟨b, hb, m, hm, rfl⟩
        refine ⟨a * b, (A.carrier T).mul_mem ha hb,
          (b⁻¹ * n * (b⁻¹)⁻¹) * m,
          (N.carrier T).mul_mem (hN T b⁻¹ n ((A.carrier T).inv_mem hb) hn) hm, ?_⟩
        simp only [inv_inv, mul_assoc, mul_inv_cancel_left]
      inv_mem' := by
        rintro x ⟨a, ha, n, hn, rfl⟩
        refine ⟨a⁻¹, (A.carrier T).inv_mem ha, a * n⁻¹ * a⁻¹,
          hN T a n⁻¹ ha ((N.carrier T).inv_mem hn), ?_⟩
        simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev] }
  comp_mem a x := by
    rintro ⟨b, hb, n, hn, rfl⟩
    exact ⟨a ≫ b, A.comp_mem a hb, a ≫ n, N.comp_mem a hn,
      (MonObj.comp_mul a b n).symm⟩

theorem mem_normalizedProduct {A N : SubgroupFunctor G} {hN : N.IsNormalizedBy A}
    {T : Over S} {x : T ⟶ G.X} :
    x ∈ (normalizedProduct A N hN).carrier T ↔
      ∃ a ∈ A.carrier T, ∃ n ∈ N.carrier T, a * n = x :=
  Iff.rfl

theorem normalizedProduct_isPointwiseProduct (A N : SubgroupFunctor G)
    (hN : N.IsNormalizedBy A) :
    (normalizedProduct A N hN).IsPointwiseProduct A N :=
  fun _ _ => Iff.rfl

/-- Exact two-factor products are uniquely determined by their factors. -/
theorem IsPointwiseProduct.eq {F F' A B : SubgroupFunctor G}
    (h : F.IsPointwiseProduct A B) (h' : F'.IsPointwiseProduct A B) : F = F' :=
  ext fun T => Subgroup.ext fun x => (h T x).trans (h' T x).symm

theorem le_normalizedProduct_left (A N : SubgroupFunctor G) (hN : N.IsNormalizedBy A) :
    A ≤ normalizedProduct A N hN :=
  fun T x hx => ⟨x, hx, 1, (N.carrier T).one_mem, mul_one x⟩

theorem le_normalizedProduct_right (A N : SubgroupFunctor G) (hN : N.IsNormalizedBy A) :
    N ≤ normalizedProduct A N hN :=
  fun T x hx => ⟨1, (A.carrier T).one_mem, x, hx, one_mul x⟩

theorem normalizedProduct_le {A N F : SubgroupFunctor G} (hN : N.IsNormalizedBy A)
    (hA : A ≤ F) (hNF : N ≤ F) : normalizedProduct A N hN ≤ F := by
  rintro T x ⟨a, ha, n, hn, rfl⟩
  exact (F.carrier T).mul_mem (hA T ha) (hNF T hn)

theorem normalizedProduct_mono {A N A' N' : SubgroupFunctor G}
    (hN : N.IsNormalizedBy A) (hN' : N'.IsNormalizedBy A')
    (hA : A ≤ A') (hNN' : N ≤ N') :
    normalizedProduct A N hN ≤ normalizedProduct A' N' hN' := by
  rintro T x ⟨a, ha, n, hn, rfl⟩
  exact ⟨a, hA T ha, n, hNN' T hn, rfl⟩

theorem map_mono (f : H ⟶ G) {A B : SubgroupFunctor H} (h : A ≤ B) :
    A.map f ≤ B.map f := by
  rintro T x ⟨a, ha, rfl⟩
  exact ⟨a, h T ha, rfl⟩

/-- The inverse-image functor describes intersection with the represented
subgroup after mapping back to the ambient group, on every test scheme. -/
theorem mem_map_comap_iff (f : H ⟶ G) (F : SubgroupFunctor G)
    (T : Over S) (x : T ⟶ G.X) :
    x ∈ ((F.comap f).map f).carrier T ↔
      x ∈ (range f).carrier T ∧ x ∈ F.carrier T := by
  rw [map_comap]
  rfl

end Langlands.GroupScheme.SubgroupFunctor
