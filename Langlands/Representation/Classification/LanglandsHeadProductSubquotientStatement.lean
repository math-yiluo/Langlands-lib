import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Category.Subquotients

/-!
# The summed Langlands head occurs in a binary product

Tadic 1986, Proposition A.4(ii), for two positive-rank multisegments and
actual representatives of their Langlands heads. The occurrence is an actual
smooth subquotient of the normalized upper-parabolic binary product.
This module states the assertion and supplies no proof.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Tadic 1986, Proposition A.4(ii): every Langlands head of `a + b` is a
subquotient of the normalized product of any Langlands heads of `a` and `b`.
Both factor ranks are positive; no irreducibility of their product is assumed. -/
def LanglandsHeadProductSubquotient : Prop :=
  letI := T.topology
  ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (a b : T.Multisegment.{max uF uV, uF})
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
    a.IsLanglandsHead A → b.IsLanglandsHead B → (a + b).IsLanglandsHead P →
      SmoothRep.IsSubquotient P ((T.binaryPositiveProductFunctor hm hn).obj (A, B))

end Langlands.Classification
