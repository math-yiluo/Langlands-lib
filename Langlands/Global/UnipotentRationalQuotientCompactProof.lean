import Langlands.Global.SplitUnipotentRationalQuotientCompact
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Compactness of `U(F) \ U(𝔸_F)` for smooth connected unipotent groups

Proof of the published proposition `UnipotentRationalQuotientCompactStatement`: for every
smooth connected unipotent affine group scheme `U` of finite type over a number field `F`,
the rational quotient `U(F) \ U(𝔸_F)` is compact. See the paired Markdown.
-/

universe u

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

/-- **Compactness for unipotent groups.** For every number field `F` and every smooth
connected unipotent affine group scheme `U` of finite type over `F`, the rational quotient
`RationalQuotient F U = U(F) \ U(𝔸_F)` is a compact space. -/
theorem unipotentRationalQuotientCompact : UnipotentRationalQuotientCompactStatement.{u} :=
  unipotentRationalQuotientCompact_of_split perfectFieldUnipotentSplit
    splitUnipotentAffineTorsorStatement

end Langlands.Global.AdelicGroupPoints
