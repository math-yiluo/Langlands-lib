import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.CocycleRelativeTrivialization
import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.Global.AdelicGroupLocalPoints

/-! # First cohomology of simply connected groups over number fields and real places -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a semisimple simply connected group `G` over a number field `F`, the map from `H¹(F, G)`
to the product of `H¹(F_w, G)` over the real places `w` is bijective. Classes are represented by
cocycles on covers `Spec L → Spec F` of finite separable extensions `L`, and local classes by
cocycles on the base-changed covers `Spec (F_w ⊗ L) → Spec F_w`.

Injectivity: two cocycles on `Spec L` whose base changes are cohomologous at every real place
are cohomologous. Surjectivity: for every family of cocycles at the real places on the
base-changed covers of `Spec L`, there are a finite separable extension `L'` of `F`, an
`F`-algebra map `L → L'` and a cocycle on `Spec L'` whose base change at every real place is
cohomologous to the refinement of the given local cocycle to `Spec (F_w ⊗ L')`. -/
def SimplyConnectedRealPlacesCohomologyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G →
    (∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (ξ₁ ξ₂ : Cocycle G (Over.mk (algebraBaseMap F L))),
      (∀ w : NumberField.InfinitePlace F, w.IsReal →
        let b := algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w))
        let r := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap F L))
        ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap F L)) ⟶
            ((baseChange b).obj G).X,
          ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion F (.inl w))))}
            (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap F L))),
            (ξ₂.baseChange b _ r).toFun x y = ((ξ₁.baseChange b _ r).twist f).toFun x y) →
      ∃ f : Over.mk (algebraBaseMap F L) ⟶ G.X,
        ∀ {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ Over.mk (algebraBaseMap F L)),
          ξ₂.toFun x y = (ξ₁.twist f).toFun x y) ∧
    (∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (c : ∀ w : {w : NumberField.InfinitePlace F // w.IsReal},
        Cocycle ((baseChange (algebraBaseMap F
            (Langlands.Global.placeCompletion F (.inl w.1)))).obj G)
          ((Over.pullback (algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w.1)))).obj
            (Over.mk (algebraBaseMap F L)))),
      ∃ (L' : Type u) (_ : Field L') (_ : Algebra F L') (_ : FiniteDimensional F L')
        (_ : Algebra.IsSeparable F L') (e : L →ₐ[F] L')
        (ξ : Cocycle G (Over.mk (algebraBaseMap F L'))),
        ∀ w : {w : NumberField.InfinitePlace F // w.IsReal},
          let b := algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w.1))
          let r' := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap F L'))
          let s : Over.mk (algebraBaseMap F L') ⟶ Over.mk (algebraBaseMap F L) :=
            Over.homMk (Spec.map (CommRingCat.ofHom (e : L →+* L'))) (by
              dsimp only [Over.mk_hom, algebraBaseMap]
              rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
          ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap F L')) ⟶
              ((baseChange b).obj G).X,
            ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion F (.inl w.1))))}
              (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap F L'))),
              ((c w).refine ((Over.pullback b).map s)).toFun x y =
                ((ξ.baseChange b _ r').twist f).toFun x y)

end Langlands.GroupScheme
