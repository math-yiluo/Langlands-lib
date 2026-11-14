import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentation
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Existence of an orthogonal Morita comparison of the row representation -/

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- Over every algebraically closed extension, a nondegenerate quadratic form
over a central division algebra of orthogonal dimension type has a split
orthogonal Morita comparison retaining its actual row representation.

The reduced row dimension is `m * degree = 2 * n`. The comparison identifies
the extended row representation with `degree` copies of the split
`2 * n`-dimensional inverse-right representation, over all coefficient algebras. -/
def OrthogonalMoritaRepresentationStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D]
    (degree m n : ℕ),
    0 < degree → 4 ≤ n → Module.finrank K D = degree ^ 2 →
    m * degree = 2 * n →
    ∀ σ : FirstKindInvolution K D,
      Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
      ∀ q : σ.QuadraticForms (Fin m),
        σ.IsNondegenerateQuadratic q →
        ∀ (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L],
          Nonempty (OrthogonalMoritaComparison σ q L degree n)

end Langlands.GroupScheme.Quaternionic
