import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Torsion torus cocycles over number fields split in cyclotomic extensions

This module states that a torus cocycle over a number field whose `m`-th power is
trivial becomes trivial after adjoining a root of unity whose order has only prime
factors dividing `m`. The statement is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `T` be a torus over a number field `K` and `τ` a cocycle of `T` on a finite Galois
field cover `Spec L → Spec K` whose `m`-th power is trivial for some `m > 0`. Then there is
a positive integer `N` whose prime factors all divide `m` such that `τ` becomes trivial
after base change to every field extension of `K` containing a primitive `N`-th root of
unity. The `m`-th power of `τ` is its image under the endomorphism `m • 𝟙 T`, which raises
points of `T` to the `m`-th power. -/
def NumberFieldTorusCocycleCyclotomicSplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (T : CommGroupScheme (Spec (CommRingCat.of K))), IsTorus T.toGrp →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)) (m : ℕ), 0 < m →
      (τ.map (CommGroupScheme.groupHom (m • 𝟙 T))).IsTrivial →
      ∃ N : ℕ, 0 < N ∧ (∀ q : ℕ, q.Prime → q ∣ N → q ∣ m) ∧
        ∀ (E : Type u) [Field E] [Algebra K E] (ζ : E), IsPrimitiveRoot ζ N →
          (τ.baseChangePullback (algebraBaseMap K E)).IsTrivial

end Langlands.GroupScheme
