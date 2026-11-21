import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable

/-!
# Square-integrable representations of `GL_n(F)` are not parabolically induced

A consequence of Casselman's square-integrability criterion (Casselman 1995, Theorem 4.4.6):
an irreducible square-integrable representation of `GL_n(F)` is not isomorphic to a
representation smoothly induced from a proper standard block parabolic subgroup. Stated as a
proposition, not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

/-- An irreducible square-integrable representation `π` of `GL_n(F)`, for a nonarchimedean
local field `F` of characteristic zero, is not isomorphic to the unnormalized smooth induction,
from the standard upper block parabolic subgroup of a block shape with at least two blocks, of
any smooth representation `Ξ` of the Levi product (inflated to the parabolic subgroup through
the Levi projection). The carrier of `Ξ` lies in the universe of the carrier of `π`, as in
`IsSigmaDiscreteSeries`. A consequence of Casselman's criterion (Casselman 1995,
Theorem 4.4.6); see the paired Markdown. -/
def SquareIntegrableNotInducedStatement.{v, w} : Prop :=
  ∀ (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ) (V : Type w) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V),
    π.IsIrreducible → JacquetLanglands.IsSquareIntegrable π →
      ∀ B : BlockShape n, 2 ≤ B.length →
        ∀ (X : Type w) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi F) X),
          IsSmooth Ξ →
            IsEmpty (π.Equiv
              (Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))))

end Langlands.BaseChange
