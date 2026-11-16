import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.RankinSelberg.UnequalSemilocalFactorizationStatement

/-! # The central sign over the infinite places and `S`

Cogdell 2004, proof of Theorem 4.1, p.220: for an actual cuspidal realization `T'` of
`GL_(t+1)` with a spectral presentation `P'` and a finite set `S ⊇ P'.exceptional` of finite
places, the scalars `ω'_v(-1)` of the central element `-1` at the infinite places (read off the
compact action, `realMinusOneScalar`, `complexMinusOneScalar`) and the minus-one scalars
`ζ_v` of the Whittaker models of the local components at the places of `S` multiply to `1`.
See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField
open Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance archimedeanSignSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance archimedeanSignSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, proof of Theorem 4.1, p.220: the central sign.**

Let `T'` be an actual cuspidal realization of `GL_(t+1)` over a number field `F`, `P'` a
spectral presentation of `T'` with irreducible admissible local components, `S` a finite set of
finite places containing `P'.exceptional`, and `ψv` a family of nontrivial additive characters
of the completions at the finite places. If, for each `v ∈ S`, `ζ_v` is the scalar by which
`-1` acts on the model of a nonzero Whittaker functional for `ψv v⁻¹` on the local component
of `P'` at `v`, then
`(∏_(v real) ω'_v(-1)) (∏_(w complex) ω'_w(-1)) ∏_(v ∈ S) ζ_v = 1`. -/
def ArchimedeanCentralSignStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (t : ℕ) (T' : Automorphic.CuspidalOperatorRealization F t)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (hI' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)), P'.exceptional ⊆ S →
  ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ζ : S → ℂˣ),
    (∀ v : S,
      letI := (padicField v.1).canonicalTopologicalData.topology
      letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
      ∃ ℓ : Whittaker.glInverseFunctionals (ψv v.1) t
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation,
        ℓ.val ≠ 0 ∧
        RankinSelberg.HasModelMinusOneScalar
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation
          ℓ (ζ v)) →
    (∏ v, realMinusOneScalar T' v) * (∏ w, complexMinusOneScalar T' w) *
      ∏ v : S, (ζ v : ℂ) = 1

end Langlands.Global.RankinSelbergGlobal
