import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.Defs

/-! # Artinian detection of a filtered exhaustion of a quasi-finite scheme -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A directed increasing family of subschemes of a quasi-finite scheme over
a noetherian base contains the whole scheme at one stage if it does so after
every local Artinian base change. -/
def QuasiFiniteArtinianExhaustionStatement : Prop :=
  ∀ (S X : Scheme.{u}) [IsNoetherian S] (f : X ⟶ S),
    LocallyOfFiniteType f → LocallyQuasiFinite f → QuasiCompact f →
    ∀ (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X),
      (∀ i, IsImmersion (j i)) →
      (∀ i k, i ≤ k → ∃ a : Y i ⟶ Y k, a ≫ j k = j i) →
      (∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
        (b : Spec (CommRingCat.of R) ⟶ S),
        ∃ i, IsIso (pullback.snd (j i) (pullback.fst f b))) →
      ∃ i, IsIso (j i)

end Langlands.AlgebraicGeometry
