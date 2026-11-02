import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition
import Mathlib.GroupTheory.DoubleCoset

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

/-! # Conjugating standard Levis -/

/-- Transport of a standard Levi by a normalizing point acting on its simple-root subset, and independence of the lift. -/
def StandardLeviConjugationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      let rootSubset := fun J : Set (characterLattice T) =>
        {x : relativeRootSpan i |
          (x : ℚ ⊗[ℤ] characterLattice T) ∈ Langlands.LinearAlgebra.RationalSpan.toRat '' J}
      (∀ J J' : Set (characterLattice T),
        J ⊆ simpleRelativeRoots i ν → J' ⊆ simpleRelativeRoots i ν →
        ∀ n : normalizerPoints i,
          relativeWeylAction i (QuotientGroup.mk n) '' rootSubset J' = rootSubset J →
          standardLevi i ν J' =
            (standardLevi i ν J).comap
              (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).hom) ∧
      ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
        ∀ n n' : normalizerPoints i,
          (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n' →
          (standardLevi i ν J).comap
              (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).inv =
            (standardLevi i ν J).comap
              (G.innerIso (n' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).inv

end Langlands.GroupScheme
