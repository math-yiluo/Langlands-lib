import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Correspondence.UnramifiedNormalization

/-!
# Rigidity of cuspidal inducing data from unramified local components

Jacquet–Shalika (1981), *Euler products II*, Theorem (4.4), in the form of
Getz–Hahn (2024), Theorem 10.7.2, for actual cuspidal realizations of general
linear groups over a number field. Let `σ_1, …, σ_k` and `σ'_1, …, σ'_k'` be
cuspidal realizations of `GL_(m_i+1)` and `GL_(m'_j+1)` with total rank `r + 1`.
Suppose that outside a finite set of finite places every local component is
unramified and the normalized parabolically induced representations of
`GL_(r+1)(F_v)` have a common spherical irreducible admissible subquotient. Then
`k = k'` and, after a permutation, the two lists have equal ranks and equivalent
full operator realizations. See the paired Markdown for the sources and scope.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uQ

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  PositiveRankCuspidalClass)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSphericalClass sphericalSubgroup IsSubquotientOf)

/-- The canonical matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance inducingDataGeneralLinearTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

/-- **Rigidity of cuspidal inducing data** (Jacquet–Shalika 1981 II, Theorem (4.4);
Getz–Hahn 2024, Theorem 10.7.2). Let `T i` (`i < k`) and `T' j` (`j < k'`) be actual
cuspidal realizations of `GL_(m i + 1)` and `GL_(m' j + 1)` over a number field `F`,
with `∑ (m i + 1) = ∑ (m' j + 1) = r + 1`, and spectral presentations whose finite
local components are irreducible and admissible. Suppose that at every finite place
`v` outside a finite set `S` every local component is spherical (its canonical p-adic
class has a representative with a nonzero `GL(O_v)`-fixed vector) and some spherical
irreducible admissible representation of
`GL_(r+1)(F_v)` is a subquotient of both normalized induced representations
`i(σ_(1,v), …, σ_(k,v))` and `i(σ'_(1,v), …, σ'_(k',v))` from the standard upper block
parabolics. Then there is a bijection `e : Fin k ≃ Fin k'` with `m' (e i) = m i` and
`T' (e i)` equivalent to `T i`, as an equality of positive-rank cuspidal classes. -/
def CuspidalInducingDataRigidityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k k' : ℕ) (m : Fin k → ℕ) (m' : Fin k' → ℕ)
    (hm : ∑ i, (m i + 1) = r + 1) (hm' : ∑ j, (m' j + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (T' : ∀ j, CuspidalOperatorRealization F (m' j))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (P' : ∀ j, CuspidalSpectralPresentation.{u, uQ} (T' j))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (h' : ∀ j, HasIrreducibleAdmissibleComponents (P' j))
    (S : Finset (FinitePlace F)),
    (∀ v ∉ S,
      (∀ i, IsSphericalClass (padicField v) (localClass (P i) (h i) v)) ∧
      (∀ j, IsSphericalClass (padicField v) (localClass (P' j) (h' j) v)) ∧
      ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
        fixedVectors A.obj.representation (sphericalSubgroup (padicField v) r) ≠ ⊥ ∧
        IsSubquotientOf
          ((padicField v).canonicalNormalizedProductInduced
            ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
            (fun i => (((P i).localComponent v).padicObject
              (h i v).1 (h i v).2).obj.representation))
          A.obj.representation ∧
        IsSubquotientOf
          ((padicField v).canonicalNormalizedProductInduced
            ⟨k', fun j => m' j + 1, fun _ => Nat.succ_pos _, hm'⟩
            (fun j => (((P' j).localComponent v).padicObject
              (h' j v).1 (h' j v).2).obj.representation))
          A.obj.representation) →
    ∃ e : Fin k ≃ Fin k', ∀ i,
      (⟨m i, (T i).isoClass⟩ : PositiveRankCuspidalClass F) =
        ⟨m' (e i), (T' (e i)).isoClass⟩

end Langlands.Global
