import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Represented fppf-local subgroup products

The factorization of a point is allowed after a flat surjective locally finitely
presented relative cover. The predicates assert no representability theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- A point belongs fppf-locally to the ordered product of two subgroup functors
when it factors as such a product after one flat surjective locally finitely
presented map of arbitrary relative test schemes. -/
def FppfLocallyInProduct (F N : SubgroupFunctor G) {T : Over S} (x : T ⟶ G.X) : Prop :=
  ∃ (V : Over S) (v : V ⟶ T),
    Flat v.left ∧ Surjective v.left ∧ LocallyOfFinitePresentation v.left ∧
      ∃ p n : V ⟶ G.X,
        p ∈ F.carrier V ∧ n ∈ N.carrier V ∧ v ≫ x = p * n

/-- An actual closed subgroup represents the fppf-local product, by equality of
membership on every scheme test. This does not require factorization on the
original test and does not assert existence of a representative. -/
structure IsFppfProduct (F N : SubgroupFunctor G) (i : P ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  mem_range_iff : ∀ (T : Over S) (x : T ⟶ G.X),
    x ∈ (range i).carrier T ↔ FppfLocallyInProduct F N x

namespace FppfLocallyInProduct

variable {F F' N N' : SubgroupFunctor G} {T : Over S}

/-- An actual product on the original test gives a local factorization using
the identity cover. -/
theorem of_mul {p n : T ⟶ G.X} (hp : p ∈ F.carrier T) (hn : n ∈ N.carrier T) :
    FppfLocallyInProduct F N (p * n) :=
  ⟨T, 𝟙 T, by change Flat (𝟙 T.left); infer_instance,
    by change Surjective (𝟙 T.left); infer_instance,
    by change LocallyOfFinitePresentation (𝟙 T.left); infer_instance,
    p, n, hp, hn, Category.id_comp _⟩

/-- Each point of the left factor belongs to the local product. -/
theorem of_left {x : T ⟶ G.X} (hx : x ∈ F.carrier T) :
    FppfLocallyInProduct F N x := by
  simpa only [mul_one] using of_mul hx (N.carrier T).one_mem

/-- Each point of the right factor belongs to the local product. -/
theorem of_right {x : T ⟶ G.X} (hx : x ∈ N.carrier T) :
    FppfLocallyInProduct F N x := by
  simpa only [one_mul] using of_mul (F.carrier T).one_mem hx

/-- Enlarging either subgroup functor preserves local product membership. -/
theorem mono {x : T ⟶ G.X} (hx : FppfLocallyInProduct F N x)
    (hF : F ≤ F') (hN : N ≤ N') : FppfLocallyInProduct F' N' x := by
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ := hx
  exact ⟨V, v, hf, hs, hl, p, n, hF V hp, hN V hn, he⟩

end FppfLocallyInProduct

namespace IsFppfProduct

variable {F N : SubgroupFunctor G} {i : P ⟶ G} {j : Q ⟶ G}

/-- The represented local product contains its left factor on all tests. -/
theorem left_le (hi : IsFppfProduct F N i) : F ≤ range i :=
  fun T _ hx => (hi.mem_range_iff T _).mpr (FppfLocallyInProduct.of_left hx)

/-- The represented local product contains its right factor on all tests. -/
theorem right_le (hi : IsFppfProduct F N i) : N ≤ range i :=
  fun T _ hx => (hi.mem_range_iff T _).mpr (FppfLocallyInProduct.of_right hx)

/-- Two representatives of the same fppf-local product have the same all-test image. -/
theorem range_eq (hi : IsFppfProduct F N i) (hj : IsFppfProduct F N j) :
    range i = range j := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  exact (hi.mem_range_iff T x).trans (hj.mem_range_iff T x).symm

end IsFppfProduct

end Langlands.GroupScheme.SubgroupFunctor
