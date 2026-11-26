import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.SimplyConnected.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Cohomology of quasi-split trialitarian groups over totally complex number fields

This module states, and does not prove, that a simply connected quasi-split group of type
`³D₄` or `⁶D₄` over a number field without real places has trivial Galois cohomology in
degree one (Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, §6.8).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a totally complex number field `F`, every cocycle of a simply connected, absolutely
almost-simple, quasi-split group `G` of trialitarian type on a finite Galois field cover
`Spec L → Spec F` is a coboundary on that cover. The type is given by actual index data `d`
whose Cartan pairings are those of `CartanMatrix.D 4` under the numbering `e`: vertex `1` is
the centre, and each of the three leaves is moved by some element of the absolute Galois
group under the star action. These are the forms `³D₄` and `⁶D₄`. No local triviality is
assumed. -/
def TotallyComplexQuasiSplitTrialitarianCocycleVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → IsQuasiSplit G →
    (∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) →
    (∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial

end Langlands.GroupScheme
