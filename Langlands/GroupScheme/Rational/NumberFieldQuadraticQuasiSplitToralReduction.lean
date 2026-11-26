import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Statement: anisotropic toral representatives of quadratic cocycles

For a semisimple group over a number field whose Dynkin diagram has no nontrivial
symmetry and which becomes quasi-split over a quadratic extension `L`, every cocycle on
the cover `Spec L → Spec F` that is trivial at the real places comes from a cocycle of a
maximal torus that splits over `L` and is anisotropic over `F`. The module states this
and proves nothing.
-/

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Let `F` be a number field, `G` a semisimple group over `F` with actual Tits index
data `d` such that every permutation of the simple vertices preserving the Cartan
pairings is the identity, and `L/F` a quadratic Galois extension such that `G_L` is
quasi-split. Every cocycle of `G` on the cover `Spec L → Spec F` that is trivial at
every real place is cohomologous to the image of a cocycle, trivial at every real
place, of a maximal `F`-torus `T` of `G` that splits over `L` and is anisotropic over
`F`. Triviality at a real place `w` means triviality of the base change to the actual
pullback of the cover to the completion `F_w`. This combines Platonov–Rapinchuk,
*Algebraic Groups and Number Theory*, Lemma 6.17 (printed p. 329) and Lemma 6.28
(printed pp. 369–370); the splitting and anisotropy of `T` come from the absence of
diagram symmetries. -/
def NumberFieldQuadraticQuasiSplitToralReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    (∀ π : d.Vertex ≃ d.Vertex,
      (∀ a b, d.cartan (π a) (π b) = d.cartan a b) → π = Equiv.refl d.Vertex) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) →
      ∀ ξ : Cocycle G (GaloisCocycle.cover F L),
        (∀ w : InfinitePlace F, w.IsReal →
          let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
          let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
          (ξ.baseChange b _ r).IsTrivial) →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
          (η : Cocycle T.toGrp (GaloisCocycle.cover F L)),
          IsMaximalTorus i ∧
          IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F L)).obj T.toGrp) ∧
          IsAnisotropic T.toGrp ∧
          (∀ w : InfinitePlace F, w.IsReal →
            let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
            let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
            (η.baseChange b _ r).IsTrivial) ∧
          ξ.Cohomologous (η.map i)

end Langlands.GroupScheme
