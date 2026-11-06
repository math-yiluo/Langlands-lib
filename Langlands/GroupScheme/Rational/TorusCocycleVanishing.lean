import Langlands.GroupScheme.TorsorCocycle
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.FieldTheory.Galois.Basic

/-! # Triviality of torus cocycles on finite Galois covers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual torus cocycle on a finite Galois field cover is a coboundary. -/
def HasTrivialTorusCocycles (K : Type u) [Field K] : Prop :=
  ∀ (T : GroupScheme (Spec (CommRingCat.of K))), IsTorus T →
    ∀ (L : Type u) [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L]
      (ξ : Cocycle T (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      ξ.IsTrivial

end Langlands.GroupScheme
