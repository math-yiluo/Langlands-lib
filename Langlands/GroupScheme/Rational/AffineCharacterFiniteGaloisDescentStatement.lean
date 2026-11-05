import Langlands.GroupScheme.GaloisPointRational
import Mathlib.FieldTheory.Galois.GaloisClosure

/-! # Finite-Galois fields of definition for affine characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An extension-field character of an arbitrary affine group agrees on base-field
rational points with a character defined over a finite Galois intermediate field. -/
def AffineCharacterFiniteGaloisDescentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    (ψ : rationalCharacters (GaloisPointComparison.baseChanged k K G)),
    ∃ E : FiniteGaloisIntermediateField k K,
      ∃ ψE : rationalCharacters (GaloisPointComparison.baseChanged k E G),
        ∀ g : rationalPoints G,
          algebraMap E K
            (rationalCharacterEval ψE (GaloisPointComparison.rationalExtend k E G g) : E) =
          (rationalCharacterEval ψ (GaloisPointComparison.rationalExtend k K G g) : K)

end Langlands.GroupScheme
