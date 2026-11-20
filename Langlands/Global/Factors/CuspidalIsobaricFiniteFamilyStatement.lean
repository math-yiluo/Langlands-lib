import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Representation.Classification.IsobaricSum

/-! The family of finite-place isobaric sums used in global automorphy. -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSubquotientOf sphericalSubgroup)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

local instance {F : Type u} [Field F] [NumberField F] (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- The finite local components of the supplied cuspidal presentations have
isobaric sums at every finite place. These sums occur in the given normalized
block inductions and are spherical outside a single finite set. -/
def CuspidalIsobaricFiniteFamilyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
    ∃ (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
      (S : Finset (FinitePlace F)),
      (∀ v, (padicField v).canonicalTopologicalData.IsIsobaricSum.{u, u}
        (fun i => (((P i).localComponent v).padicObject (h i v).1 (h i v).2).obj) (A v).obj) ∧
      (∀ v, IsSubquotientOf
        ((padicField v).canonicalNormalizedProductInduced
          ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
          (fun i => (((P i).localComponent v).padicObject (h i v).1 (h i v).2).obj.representation))
        (A v).obj.representation) ∧
      (∀ v ∉ S, fixedVectors (A v).obj.representation (sphericalSubgroup (padicField v) r) ≠ ⊥)

end Langlands.Global
