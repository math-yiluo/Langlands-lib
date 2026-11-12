import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple

/-!
# Smoothness and absolute almost-simplicity of even orthogonal groups

The statement that, over every field `K` of any characteristic, the orthogonal group
scheme `O(q)` of an ordinary quadratic form `q` on `K^(2m)`, `m ≥ 3`, with invertible polar
matrix is smooth, and its identity component is absolutely almost simple. This is a
statement only.
-/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- For every field `K`, every `m ≥ 3` and every scalar quadratic form `q` on `K^(2m)` whose
polar matrix is invertible, the isometry group `O(q)` is smooth, and, with this smoothness,
its identity component `O(q)⁰` is absolutely almost simple. This is a statement only. -/
def OrdinaryOrthogonalGeometryStatement : Prop :=
  ∀ (K : Type u) [Field K] (m : ℕ), 3 ≤ m →
    ∀ q : (FirstKindInvolution.scalar K).QuadraticForms (Fin (2 * m)),
      (FirstKindInvolution.scalar K).IsNondegenerateQuadratic q →
      ∃ h : Smooth ((FirstKindInvolution.scalar K).isometryGroup q).X.hom,
        haveI := h
        IsAbsolutelyAlmostSimple ((FirstKindInvolution.scalar K).connectedIsometryGroup q)

end Langlands.GroupScheme.Quaternionic
