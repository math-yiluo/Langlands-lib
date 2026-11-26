import Langlands.Correspondence.HenniartCompatibleInjections
import Langlands.Correspondence.HenniartRankExtension

/-!
# Compatibility of Henniart's candidate with cyclic base change of prime degree

Interface E3 of the operator's plan note on the external inputs of the local
Langlands correspondence for `GL_n`, for the Library's candidate: the rank
extensions `Extension.rankExtension` of the stable candidate images (Henniart
2000, §4.4). Over a cyclic prime-degree step `M/L`, one weak cyclic base change
`Ch` sends the candidate image of a Weil class over `L` to the candidate images
of the constituents of its restriction to `W_M` (route note §6.5, (CI1)), and
the candidate over `M` is equivariant for the action of `W_L` (route note
§6.5, (CI2)). Both properties are asked in every rank where the candidates are
defined. Definitions and a proposition only.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

open Langlands.Correspondence StableMap

namespace Numerical

variable {p : ℕ} [Fact p.Prime]

/-- (CI1) for the candidate, in every rank where it is defined: if the candidate
is defined over `L` in rank `k + 1` and over `M` in the rank of every member of a
restriction decomposition `m` of `σ`, then `Ch` sends the candidate image of `σ`
to the multiset of the candidate images of the members of `m`. -/
def IsCandidateBaseChangeCompatible (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S) : Prop :=
  ∀ (k : ℕ) (hL : StableExistsAt.{uK, uW, uV, uW} S.base k.succPNat)
    (σ : IrreducibleWeilClass.{uK, uW} S.base k.succPNat)
    (m : Multiset (Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat)),
    IsRestrictionDecomposition S σ m →
      ∀ hm : ∀ τ ∈ m, StableExistsAt.{uK, uW, uV, uW} S.top τ.1.succPNat,
        Ch k (Extension.rankExtension S.base hL σ) =
          m.pmap (fun τ h => ⟨τ.1, Extension.rankExtension S.top h τ.2⟩) hm

/-- (CI2) for the candidate over `M`, in every rank where it is defined: the
candidate sends the conjugate of `τ` by `w ∈ W_L` to the Galois conjugate of the
candidate image of `τ` by the image of `w` in `Gal(M/L)`. -/
def IsCandidateGaloisEquivariant (S : CyclicPrimeStep.{uK} p) : Prop :=
  ∀ (k : ℕ) (hM : StableExistsAt.{uK, uW, uV, uW} S.top k.succPNat)
    (w : Weil.Local.localWeilGroup S.base)
    (τ : IrreducibleWeilClass.{uK, uW} S.top k.succPNat),
    Extension.rankExtension S.top hM (weilConjugate S w τ) =
      S.galoisConjugate (Weil.Local.finiteGaloisQuotient S.base S.top S.embedding S.isGalois w)
        k (Extension.rankExtension S.top hM τ)

end Numerical

open Numerical

/-- Interface E3 for the Library's candidate: for every cyclic prime-degree step
there is one weak cyclic base change compatible with the candidate in the sense
of (CI1), and the candidate over the top field satisfies (CI2), in every rank
where the candidates are defined. -/
def CandidateBaseChangeCompatibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p),
    ∃ Ch : CyclicBaseChangeMap.{uK, uV} S,
      IsWeakCyclicBaseChange S Ch ∧ IsCandidateBaseChangeCompatible.{uK, uW, uV} S Ch ∧
        IsCandidateGaloisEquivariant.{uK, uW, uV} S

end Langlands.Henniart
