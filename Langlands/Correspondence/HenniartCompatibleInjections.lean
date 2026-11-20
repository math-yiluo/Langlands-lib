import Langlands.Correspondence.HenniartCyclicBaseChange
import Langlands.Correspondence.HenniartNumericalStatement
import Langlands.VirtualRepresentation.Weil.GroupTransport
import Langlands.Weil.Local.ExtensionParameters
import Langlands.Weil.Local.FiniteGaloisReciprocity
import Langlands.Weil.Representation.DirectSum

/-!
# Numerical injections compatible with cyclic base change

Definitions and the rank-bounded premise (I4) of Option II of the operator's
numerical LLC route note (§6.5, hypothesis (CI) and Remark `rem:CI2`).
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

open Langlands.Correspondence

namespace Numerical

variable {p : ℕ} [Fact p.Prime]

/-- The restriction of `σ` along the Weil map for `S.embedding` is the direct
sum of the classes in `m`. A list enumerates the summands with multiplicity. -/
def IsRestrictionDecomposition (S : CyclicPrimeStep.{uK} p) {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} S.base k.succPNat)
    (m : Multiset (Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat)) : Prop :=
  ∃ l : List (Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat),
    (l : Multiset _) = m ∧
      Weil.Local.extensionRestrictClass S.base S.top S.embedding (weilClassForget S.base σ) =
        FiniteRepresentation.directSumClass (fun i : Fin l.length =>
          weilClassForget S.top (l.get i).2)

/-- Pull back a rank-`k + 1` Weil class on `S.top` along conjugation by `w`. -/
def weilConjugate (S : CyclicPrimeStep.{uK} p) (w : Weil.Local.localWeilGroup S.base)
    {k : ℕ} :
    IrreducibleWeilClass.{uK, uW} S.top k.succPNat ≃
      IrreducibleWeilClass.{uK, uW} S.top k.succPNat :=
  FiniteRepresentation.continuousIrreducibleRestrictEquiv
    (Weil.Local.finiteGaloisWeilConjugation S.base S.top S.embedding S.isGalois w) (k + 1)

/-- In ranks up to `N`, base change sends the image of `σ` to the multiset of
images of the constituents of its restriction, with their ranks and multiplicities. -/
def IsBaseChangeCompatible (S : CyclicPrimeStep.{uK} p) (Ch : CyclicBaseChangeMap.{uK, uV} S)
    (N : ℕ)
    (φL : ∀ k : ℕ, k + 1 ≤ N → IrreducibleWeilClass.{uK, uW} S.base k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat)
    (φM : ∀ k : ℕ, k + 1 ≤ N → IrreducibleWeilClass.{uK, uW} S.top k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) : Prop :=
  ∀ (k : ℕ) (hk : k + 1 ≤ N) (σ : IrreducibleWeilClass.{uK, uW} S.base k.succPNat)
    (m : Multiset (Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat)),
    IsRestrictionDecomposition S σ m →
      ∀ hm : ∀ τ ∈ m, τ.1 + 1 ≤ N,
        Ch k (φL k hk σ) = m.pmap (fun τ h => ⟨τ.1, φM τ.1 h τ.2⟩) hm

/-- In ranks up to `N`, if the image of a Weil class is fixed by the entire
Galois group of the step, then the Weil class is fixed by all base Weil conjugations. -/
def ReflectsGaloisInvariance (S : CyclicPrimeStep.{uK} p) (N : ℕ)
    (φM : ∀ k : ℕ, k + 1 ≤ N → IrreducibleWeilClass.{uK, uW} S.top k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) : Prop :=
  ∀ (k : ℕ) (hk : k + 1 ≤ N) (τ : IrreducibleWeilClass.{uK, uW} S.top k.succPNat),
    (∀ g : S.Gal, S.galoisConjugate g k (φM k hk τ) = φM k hk τ) →
      ∀ w : Weil.Local.localWeilGroup S.base, weilConjugate S w τ = τ

/-- Over every p-adic field, every numerical injection in a positive rank
strictly below `N` is surjective. -/
def SurjectiveBelowRank (N : ℕ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (K : PadicField.{uK} q) (k : ℕ), k + 1 < N →
    ∀ φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
      IsNumericalInjection K φ → Function.Surjective φ

end Numerical

open Numerical

/-- Input (I4). Given numerical surjectivity below `N`, every cyclic prime-degree
step has numerical injections up to `N` compatible with a common weak base
change and reflecting Galois invariance on the top field. -/
def CompatibleNumericalInjectionsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p) (N : ℕ),
    SurjectiveBelowRank.{uK, uW, uV} N →
      ∃ (φL : ∀ k : ℕ, k + 1 ≤ N → IrreducibleWeilClass.{uK, uW} S.base k.succPNat →
          SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat)
        (φM : ∀ k : ℕ, k + 1 ≤ N → IrreducibleWeilClass.{uK, uW} S.top k.succPNat →
          SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat)
        (Ch : CyclicBaseChangeMap.{uK, uV} S),
        (∀ (k : ℕ) (hk : k + 1 ≤ N),
          IsNumericalInjection S.base (φL k hk) ∧ IsNumericalInjection S.top (φM k hk)) ∧
        IsWeakCyclicBaseChange S Ch ∧ IsBaseChangeCompatible S Ch N φL φM ∧
        ReflectsGaloisInvariance S N φM

end Langlands.Henniart
