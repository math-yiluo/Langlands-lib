import Langlands.Global.RankinSelberg.RealUniformContinuationReduction
import Langlands.Global.RankinSelberg.RealLocalUniformUnequalContinuationProof
import Langlands.Global.RankinSelberg.RealLocalUniformPositiveEqualContinuationProof
import Langlands.Global.RankinSelberg.RealPlaceContragredientPairLProof

/-!
# The archimedean Rankin–Selberg functional equation at the real places

A proof of `Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`
(Jacquet 2009, Theorem 2.1 (i)–(iii), for `GL_n(ℝ) × GL_m(ℝ)`, in both the unequal-rank and the
equal-rank case): the Library's reduction `realPlaceUniformContinuationReduction` applied to the
real unequal-rank continuation `realLocalUniformUnequalContinuation`, the real positive
equal-rank continuation `realLocalUniformPositiveEqualContinuation` and the contragredient
pair-factor comparison `realPlaceContragredientPairL`. See the paired Markdown.
-/

universe u

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- **The Rankin–Selberg functional equation at a real place** (Jacquet 2009, Theorem 2.1),
for archimedean restrictions of global Whittaker functions of actual cuspidal realizations, in
unequal ranks `t < r` and in equal ranks (including `r = 0`). -/
theorem realPlaceFunctionalEquation : RealPlaceFunctionalEquationStatement.{u} :=
  realPlaceUniformContinuationReduction.{u} realLocalUniformUnequalContinuation
    realLocalUniformPositiveEqualContinuation realPlaceContragredientPairL.{u}

end Langlands.Global.RankinSelbergGlobal
