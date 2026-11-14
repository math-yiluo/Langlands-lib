import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Finiteness of separated etale morphisms from local fibre counts -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- A quasi-compact separated etale morphism is finite if its geometric fibre
cardinality is constant after every base change from a local ring. The common
cardinality depends on the local ring and its base map, but precedes all choices
of algebraically closed field and algebra structure. -/
def EtaleLocalCardinalityFinitenessStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    QuasiCompact f → IsSeparated f → Etale f →
    (∀ (R : Type u) [CommRing R] [IsLocalRing R]
        (b : Spec (CommRingCat.of R) ⟶ Y),
      ∃ n : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
        Nat.card {x : Spec (CommRingCat.of k) ⟶ X //
          x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ b} = n) →
    IsFinite f

end Langlands.AlgebraicGeometry
