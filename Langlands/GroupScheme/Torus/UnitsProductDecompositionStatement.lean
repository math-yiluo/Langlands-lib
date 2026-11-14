import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Statement: invertible functions on a product of irreducible varieties -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Invertible functions on a product** (Milne, *Algebraic Groups* (2017),
Proposition 12.48). Let `X` and `Y` be irreducible algebraic varieties over an algebraically
closed field `k`. Every morphism `u : X × Y → 𝔾_m` is of the form `u = u₁ · u₂` with
`u₁ : X → 𝔾_m` and `u₂ : Y → 𝔾_m`, that is, `u(x, y) = u₁(x) u₂(y)`. -/
def UnitsProductDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X Y : Over (Spec (CommRingCat.of k))),
    LocallyOfFiniteType X.hom → QuasiCompact X.hom → IsSeparated X.hom →
      IsReduced X.left → IrreducibleSpace X.left →
    LocallyOfFiniteType Y.hom → QuasiCompact Y.hom → IsSeparated Y.hom →
      IsReduced Y.left → IrreducibleSpace Y.left →
    ∀ u : X ⊗ Y ⟶ (Gm (Spec (CommRingCat.of k))).X,
      ∃ (u₁ : X ⟶ (Gm (Spec (CommRingCat.of k))).X) (u₂ : Y ⟶ (Gm (Spec (CommRingCat.of k))).X),
        u = (fst X Y ≫ u₁) * (snd X Y ≫ u₂)

end Langlands.GroupScheme
