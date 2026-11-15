import Langlands.Geometry.Analytic.SchemeAnalytificationMorphism
import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.SchemeAnalytificationRationalPoints

/-! # Statement: analytifications of morphisms of schemes exist, are unique and are functorial -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology

/-- Statement (Berkovich 1990, Theorem 3.4.1 with steps (2)–(3) of its proof;
Conrad–Temkin 2009, Theorem 2.2.3; for the Library's polynomial-locus model): for a
complete nonarchimedean nontrivially normed field `K`,

* for schemes `X` and `Y` locally of finite type over `K` and a morphism `g : X ⟶ Y`
  over `Spec K`: (1) there is exactly one continuous map of glued analytifications
  satisfying `IsAnalytificationMap` for `g`; and every such map `F` (2) is compatible
  with the center maps, `π_Y ∘ F = g ∘ π_X`, and (3) sends the analytic point of a
  `K`-point `p` of `X` to the analytic point of the `K`-point `g ∘ p` of `Y`;
* (4) for morphisms `g : X ⟶ Y` and `g' : Y ⟶ Z` over `Spec K`, the composite of
  analytifications of `g` and of `g'` is an analytification of `g ≫ g'`. -/
def SchemeAnalytificationMorphismStatement : Prop :=
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) (f' : Y ⟶ Spec (CommRingCat.of K))
      [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (g : X ⟶ Y) (hg : g ≫ f' = f),
      (∃! F : C(Space K f, Space K f'), IsAnalytificationMap K f f' g hg F) ∧
      ∀ F : C(Space K f, Space K f'), IsAnalytificationMap K f f' g hg F →
        (∀ z : Space K f, center K f' (F z) = g (center K f z)) ∧
        ∀ p : RingPoint K (Over.mk f) K,
          F (analyticRationalPoint K f p) =
            analyticRationalPoint K f' (p ≫ Over.homMk g hg)) ∧
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X Y Z : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K))
    (f' : Y ⟶ Spec (CommRingCat.of K)) (f'' : Z ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] [LocallyOfFiniteType f'']
    (g : X ⟶ Y) (hg : g ≫ f' = f) (g' : Y ⟶ Z) (hg' : g' ≫ f'' = f')
    (F : C(Space K f, Space K f')) (F' : C(Space K f', Space K f'')),
    IsAnalytificationMap K f f' g hg F → IsAnalytificationMap K f' f'' g' hg' F' →
      IsAnalytificationMap K f f'' (g ≫ g') (by rw [Category.assoc, hg', hg]) (F'.comp F)

end Langlands.Analytic.SchemeAnalytification
