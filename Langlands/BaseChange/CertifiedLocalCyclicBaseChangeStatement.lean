import Langlands.BaseChange.SigmaLiftOnSupercuspidals
import Langlands.Correspondence.HenniartCyclicBaseChange

/-!
# Local cyclic base change of prime degree certified by σ-lifts

For every cyclic prime-degree step `M/L` of p-adic fields, some map `Ch` from supercuspidal
classes over `L` to multisets of supercuspidal classes over `M` has the numerical properties
(W1)–(W4) of weak local cyclic base change (`Numerical.IsWeakCyclicBaseChange`, input (I3))
and is certified by σ-lift character identities on supercuspidal classes
(`IsSigmaLiftOnSupercuspidals`) for every nonidentity `σ ∈ Gal(M/L)`. The second property is
the hypothesis on the local map in clause N′ of
`Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement`.
A statement only; see the paired Markdown.
-/

namespace Langlands.BaseChange

universe uK uV

/-- Every cyclic prime-degree step `S` of p-adic fields has a local base-change map `Ch` on
supercuspidal classes that satisfies the weak clauses (W1)–(W4)
(`Numerical.IsWeakCyclicBaseChange`) and, for every `σ ∈ S.Gal` with `σ ≠ 1`, is certified by
σ-lifts on supercuspidal classes (`IsSigmaLiftOnSupercuspidals S.embedding Ch σ`):
Henniart–Lemaire (2011), II.2.7 and II.4.6–II.4.12; Arthur–Clozel (1989), Chapter I, §6. -/
def CertifiedLocalCyclicBaseChangeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : Langlands.Henniart.Numerical.CyclicPrimeStep.{uK} p),
    ∃ Ch : Langlands.Henniart.Numerical.CyclicBaseChangeMap.{uK, uV} S,
      Langlands.Henniart.Numerical.IsWeakCyclicBaseChange S Ch ∧
        ∀ σ : S.Gal, σ ≠ 1 → IsSigmaLiftOnSupercuspidals.{uK, uV} S.embedding Ch σ

end Langlands.BaseChange
