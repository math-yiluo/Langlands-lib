import Langlands.GroupScheme.SimplyConnected.TypeD4CentralCharacters
import Langlands.GroupScheme.SimplyConnected.TitsObstructionRootVanishing
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # The middle Tits class of anisotropic outer type `A_{2m+1}` over totally complex fields -/

universe u

open AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Over a totally complex number field, an anisotropic simply connected absolutely
almost-simple group of outer type `A_{2m+1}` has nonzero Tits obstruction at the middle
fundamental weight. The type is given by an actual Tits index numbered by
`CartanMatrix.A (2 * m + 1)`, the outer form by an element of the absolute Galois group
acting nontrivially on the simple vertices, and the middle fundamental weight is the
integral fundamental weight at the vertex numbered `m`, which the star action fixes. -/
def NumberFieldTotallyComplexOuterTypeAMiddleObstructionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom H.X.hom]
      [LocallyOfFiniteType H.X.hom] (d : TitsIndexData H) (m : ℕ)
      (e : d.Vertex ≃ Fin (2 * m + 1)) (hsc : IsSimplyConnected H),
      IsAbsolutelyAlmostSimple H →
      (∀ a b, d.cartan a b = CartanMatrix.A (2 * m + 1) (e a) (e b)) →
      (∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex), d.star σ a ≠ a) →
      IsAnisotropic H →
      ∀ w : d.pinning.starFixedWeights,
        w.val = d.absoluteFundamentalCharacter hsc (e.symm ⟨m, by omega⟩) →
        d.pinning.titsObstruction hsc w ≠ 0

end Langlands.GroupScheme
