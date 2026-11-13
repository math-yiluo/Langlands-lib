import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Automorphic.IrreducibleOperatorSubquotient
import Langlands.Representation.Classification.IsobaricSum

/-!
# Automorphy of isobaric sums of cuspidal representations

Getz–Hahn (2024), Theorem 10.7.5, at the finite places, for actual cuspidal
realizations of general linear groups over a number field. Let `π_1, …, π_k` be
cuspidal realizations of `GL_(m_i+1)` with total rank `r + 1`. There is an
irreducible automorphic subquotient `Q` of `GL_(r+1)` such that at every finite
place `v` the restriction of `Q` to `GL_(r+1)(F_v)` contains an irreducible
representation that is the local isobaric sum `π_(1,v) ⊞ ⋯ ⊞ π_(k,v)` and a
subquotient of the normalized induced representation `i(π_(1,v), …, π_(k,v))`.
See the paired Markdown for the sources and scope.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  IrreducibleOperatorSubquotient)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSubquotientOf)

/-- The canonical matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance isobaricGeneralLinearTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- **Automorphy of isobaric sums at the finite places** (Getz–Hahn 2024,
Theorem 10.7.5). Let `T i` (`i < k`) be actual cuspidal realizations of
`GL_(m i + 1)` over a number field `F`, with `∑ (m i + 1) = r + 1`, and spectral
presentations whose finite local components are irreducible and admissible. Then
there is an irreducible automorphic operator subquotient `Q` of `GL_(r+1)` such
that at every finite place `v` some irreducible admissible representation `A` of
`GL_(r+1)(F_v)`
- is an isobaric sum `π_(1,v) ⊞ ⋯ ⊞ π_(k,v)` of the local components,
- is a subquotient of the normalized induced representation
  `i(π_(1,v), …, π_(k,v))` from the standard upper block parabolic, and
- embeds into the restriction of `Q` to `GL_(r+1)(F_v)`. -/
def CuspidalIsobaricRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
    ∃ Q : IrreducibleOperatorSubquotient F r, ∀ v : FinitePlace F,
      ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
        (padicField v).canonicalTopologicalData.IsIsobaricSum.{u, u}
          (fun i => (((P i).localComponent v).padicObject (h i v).1 (h i v).2).obj)
          A.obj ∧
        IsSubquotientOf
          ((padicField v).canonicalNormalizedProductInduced
            ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
            (fun i => (((P i).localComponent v).padicObject
              (h i v).1 (h i v).2).obj.representation))
          A.obj.representation ∧
        ∃ f : A.obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
          Function.Injective f.toLinearMap

end Langlands.Global
