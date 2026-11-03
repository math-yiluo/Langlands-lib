import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws

/-! # A geometric criterion for represented fppf products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H N P : GroupScheme S}

/-- An fppf factorization of the ordered multiplication morphism through a
closed subgroup represents the ordered fppf-local product on every test. -/
theorem isFppfProduct_of_fppf_factorization
    (i : H ⟶ G) (j : N ⟶ G) (p : P ⟶ G)
    (hp : IsClosedSubgroup p) (q : H.X ⊗ N.X ⟶ P.X)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hq : q ≫ p.hom.hom =
      (fst H.X N.X ≫ i.hom.hom) * (snd H.X N.X ≫ j.hom.hom)) :
    IsFppfProduct (range i) (range j) p := by
  let : IsClosedImmersion p.hom.hom.left := hp
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  refine ⟨hp, fun T x => ?_⟩
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    let V : Over S := Over.mk (pullback.fst y.left q.left ≫ T.hom)
    let v : V ⟶ T := Over.homMk (pullback.fst y.left q.left) rfl
    let z : V ⟶ H.X ⊗ N.X :=
      Over.homMk (pullback.snd y.left q.left) (by
        rw [← Over.w q, ← Category.assoc, ← pullback.condition,
          Category.assoc, Over.w y]
        rfl)
    have hz : v ≫ y = z ≫ q := Over.OverMorphism.ext pullback.condition
    refine ⟨V, v, ?_, ?_, ?_,
      z ≫ fst H.X N.X ≫ i.hom.hom, z ≫ snd H.X N.X ≫ j.hom.hom,
      mem_range.mpr ⟨z ≫ fst H.X N.X, Category.assoc _ _ _⟩,
      mem_range.mpr ⟨z ≫ snd H.X N.X, Category.assoc _ _ _⟩, ?_⟩
    · change Flat (pullback.fst y.left q.left)
      infer_instance
    · change Surjective (pullback.fst y.left q.left)
      infer_instance
    · change LocallyOfFinitePresentation (pullback.fst y.left q.left)
      infer_instance
    · rw [← Category.assoc, hz, Category.assoc, hq, MonObj.comp_mul]
  · rintro ⟨V, v, hf, hs, hl, h, n, hh, hn, he⟩
    obtain ⟨h', hh⟩ := mem_range.mp hh
    obtain ⟨n', hn⟩ := mem_range.mp hn
    let : Flat v.left := hf
    let : Surjective v.left := hs
    let : LocallyOfFinitePresentation v.left := hl
    apply mem_range_of_comp_mem_range p v
    apply mem_range.mpr
    refine ⟨lift h' n' ≫ q, ?_⟩
    rw [Category.assoc, hq, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      hh, hn, he]

end Langlands.GroupScheme.SubgroupFunctor
