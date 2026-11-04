import Langlands.GroupScheme.SubgroupFunctor.FppfProduct

/-! # Composing fppf-local subgroup factorizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Every point of `A`, on every relative scheme test, belongs fppf-locally
to the ordered product of `F` and `N`. -/
def FppfLocallyContainedInProduct (A F N : SubgroupFunctor G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G.X),
    x ∈ A.carrier T → FppfLocallyInProduct F N x

namespace FppfLocallyInProduct

variable {F N N' : SubgroupFunctor G} {T V : Over S}

/-- A local factorization after an fppf cover yields a local factorization
on the original test by composing its witnessing cover. -/
theorem of_comp {x : T ⟶ G.X} (v : V ⟶ T)
    (hf : Flat v.left) (hs : Surjective v.left)
    (hl : LocallyOfFinitePresentation v.left)
    (hx : FppfLocallyInProduct F N (v ≫ x)) :
    FppfLocallyInProduct F N x := by
  obtain ⟨W, w, hwf, hws, hwl, p, n, hp, hn, he⟩ := hx
  let : Flat v.left := hf
  let : Surjective v.left := hs
  let : LocallyOfFinitePresentation v.left := hl
  let : Flat w.left := hwf
  let : Surjective w.left := hws
  let : LocallyOfFinitePresentation w.left := hwl
  refine ⟨W, w ≫ v, ?_, ?_, ?_, p, n, hp, hn, ?_⟩
  · change Flat (w.left ≫ v.left)
    infer_instance
  · change Surjective (w.left ≫ v.left)
    infer_instance
  · change LocallyOfFinitePresentation (w.left ≫ v.left)
    infer_instance
  · simpa only [Category.assoc] using he

/-- Left multiplication by a point of the left subgroup preserves a
local factorization, with its existing cover. -/
theorem mul_left {x p : T ⟶ G.X}
    (hx : FppfLocallyInProduct F N x) (hp : p ∈ F.carrier T) :
    FppfLocallyInProduct F N (p * x) := by
  obtain ⟨V, v, hf, hs, hl, a, n, ha, hn, he⟩ := hx
  refine ⟨V, v, hf, hs, hl, (v ≫ p) * a, n,
    (F.carrier V).mul_mem (F.comp_mem v hp) ha, hn, ?_⟩
  rw [MonObj.comp_mul, he, mul_assoc]

/-- Replace the right factor of a local product by another local
factorization, composing the two covers. -/
theorem replace_right {x : T ⟶ G.X}
    (hx : FppfLocallyInProduct F N x)
    (hN : FppfLocallyContainedInProduct N F N') :
    FppfLocallyInProduct F N' x := by
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩ := hx
  apply of_comp v hf hs hl
  rw [he]
  exact (hN V n hn).mul_left hp

end FppfLocallyInProduct

namespace FppfLocallyContainedInProduct

variable {A F N N' : SubgroupFunctor G}

/-- An actual subgroup containment gives local containment in the
product with any left subgroup. -/
theorem of_le (h : A ≤ N) : FppfLocallyContainedInProduct A F N :=
  fun T _ hx => FppfLocallyInProduct.of_right (h T hx)

/-- Local containment of a right factor can be substituted in local
containment of another subgroup. -/
theorem replace_right (hA : FppfLocallyContainedInProduct A F N)
    (hN : FppfLocallyContainedInProduct N F N') :
    FppfLocallyContainedInProduct A F N' :=
  fun T x hx => (hA T x hx).replace_right hN

/-- If `N'` lies in `N`, the local products with a fixed left factor
coincide as soon as `N` locally factors through that left factor and `N'`. -/
theorem product_iff (hN : FppfLocallyContainedInProduct N F N')
    (hN' : N' ≤ N) {T : Over S} (x : T ⟶ G.X) :
    FppfLocallyInProduct F N x ↔ FppfLocallyInProduct F N' x :=
  ⟨fun hx => hx.replace_right hN, fun hx => hx.mono le_rfl hN'⟩

end FppfLocallyContainedInProduct

end Langlands.GroupScheme.SubgroupFunctor
