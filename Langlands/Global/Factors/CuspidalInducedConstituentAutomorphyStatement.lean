import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Automorphic.IrreducibleOperatorSubquotient

/-!
# Automorphy of the constituents of cuspidally induced representations

Langlands' theorem (Getz–Hahn 2024, Theorem 10.7.1, first half; Langlands 1979,
Proposition 2 with Lemma 1), at the finite places, for representations of
`GL_(r+1)` induced from actual cuspidal realizations over a number field. Let
`π_1, …, π_k` be cuspidal realizations of `GL_(m_i+1)` with total rank `r + 1`.
Choose at every finite place `v` an irreducible admissible subquotient `A_v` of
the normalized induced representation `i(π_(1,v), …, π_(k,v))`, spherical for
all `v` outside a finite set. Then some irreducible automorphic subquotient `Q`
of `GL_(r+1)` contains `A_v` in its restriction to `GL_(r+1)(F_v)` for every
finite place `v`. See the paired Markdown for the sources and scope.
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
open Correspondence (AutomorphicObject sphericalSubgroup IsSubquotientOf)

/-- The canonical matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance constituentGeneralLinearTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- **Constituents of cuspidally induced representations are automorphic**, at the
finite places (Langlands; Getz–Hahn 2024, Theorem 10.7.1, first half). Let `T i`
(`i < k`) be actual cuspidal realizations of `GL_(m i + 1)` over a number field `F`,
with `∑ (m i + 1) = r + 1`, and spectral presentations whose finite local
components are irreducible and admissible. For every finite place `v` let `A v` be
an irreducible admissible representation of `GL_(r+1)(F_v)` that is a subquotient
of the normalized induced representation `i(π_(1,v), …, π_(k,v))` from the standard
upper block parabolic, and suppose that `A v` has a nonzero `GL_(r+1)(O_v)`-fixed
vector for every `v` outside a finite set `S`. Then there is an irreducible
automorphic operator subquotient `Q` of `GL_(r+1)` such that for every finite place
`v` the representation `A v` embeds into the restriction of `Q` to
`GL_(r+1)(F_v)`. -/
def CuspidalInducedConstituentAutomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (S : Finset (FinitePlace F)),
    (∀ v : FinitePlace F,
      IsSubquotientOf
        ((padicField v).canonicalNormalizedProductInduced
          ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
          (fun i => (((P i).localComponent v).padicObject
            (h i v).1 (h i v).2).obj.representation))
        (A v).obj.representation) →
    (∀ v ∉ S,
      fixedVectors (A v).obj.representation (sphericalSubgroup (padicField v) r) ≠ ⊥) →
    ∃ Q : IrreducibleOperatorSubquotient F r, ∀ v : FinitePlace F,
      ∃ f : (A v).obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective f.toLinearMap

end Langlands.Global
