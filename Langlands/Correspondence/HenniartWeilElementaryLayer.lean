import Langlands.Correspondence.HenniartPolarPart
import Langlands.Correspondence.HenniartRefinedStrata
import Langlands.Correspondence.HenniartLaumonDeligneStatement
import Langlands.Weil.Local.ExtensionGalois
import Langlands.Weil.Local.ExtensionResidue

/-!
# The truncated Weil-side elementary layer of the numerical LLC route

Operator route note `operator-numerical-llc-route-2026-11-16` (16 November 2026), §5.1
(Propositions `prop:unram`, `prop:rank1`, `prop:tame`, Corollary `cor:14`, in the forms
of Proposition `prop:tworeductions`(a) and of the proof of Proposition `prop:LDcount`)
and Proposition `prop:LDcount`. Sources: Henniart (1988), Proposition 2.2, §3.1,
Corollaire 1.4, Proposition 4.3; Koch (1984), Satz 3 and Satz 4.

Two predicates on embeddings of p-adic fields (unramified of degree `i`; tamely and
totally ramified of degree `m`) and six proposition definitions. Nothing is proved here.
-/

namespace Langlands.Henniart

namespace Numerical

/-- `L/K`, along the embedding `ι`, is unramified of degree `i`: the degree `[L : K]`
and the residue degree `f(L/K)` both equal `i`. -/
def IsUnramifiedOfDegree.{uK, uL} {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (L : PadicField.{uL} p) (ι : K.Carrier →ₐ[Padic p] L.Carrier) (i : ℕ) : Prop :=
  Weil.Local.extensionDegree K L ι = i ∧ Weil.Local.extensionResidueDegree K L ι = i

/-- `L/K`, along the embedding `ι`, is tamely and totally ramified of degree `m`:
`[L : K] = m`, the residue degree `f(L/K)` is `1`, and `p` does not divide `m`. -/
def IsTameTotallyRamifiedOfDegree.{uK, uL} {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (L : PadicField.{uL} p) (ι : K.Carrier →ₐ[Padic p] L.Carrier) (m : ℕ) : Prop :=
  Weil.Local.extensionDegree K L ι = m ∧ Weil.Local.extensionResidueDegree K L ι = 1 ∧
    ¬ p ∣ m

end Numerical

open Numerical

/-- Unramified descent (route note, Proposition `prop:unram` in the form of Proposition
`prop:tworeductions`(a); Henniart 1988, Proposition 2.2; Koch 1984, Satz 3), with
`n = k + 1`.
(a) `W_K(n, s, f)` is empty unless `f ≥ 1`, `f ∣ n` and `f ∣ s`.
(b) Let `f ≥ 1`, `f ∣ n`, `f ∣ s`. If `T_L(n/f, s/f) = τ(n/f, s/f; q_L)` for every
`i ∣ f` and every unramified extension `L/K` of degree `i`, then
`|W_K(n, s, f)| = ν(n, f, s; q_K)` in `ℕ∞`. -/
def WeilUnramifiedDescentCountStatement.{uK, uW} : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k s f : ℕ),
    (weilRefinedStratum.{uK, uW} K k s f).Nonempty → 1 ≤ f ∧ f ∣ k + 1 ∧ f ∣ s) ∧
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k s f : ℕ),
    1 ≤ f → f ∣ k + 1 → f ∣ s →
    (∀ i : ℕ, i ∣ f → ∀ (L : PadicField.{uK} p) (ι : K.Carrier →ₐ[Padic p] L.Carrier),
      IsUnramifiedOfDegree K L ι i →
        weilTwistIrreducibleCount.{uK, uW} L ((k + 1) / f - 1) (s / f) =
          (polarTwistCount L.canonicalTopologicalData.residueCardinality
            ((k + 1) / f) (s / f) : ℕ∞)) →
    (weilRefinedStratum.{uK, uW} K k s f).encard =
      (polarPartCount K.canonicalTopologicalData.residueCardinality (k + 1) f s : ℕ∞)

/-- Rank one (route note, Proposition `prop:rank1`): `T_K(1, 0) = q_K − 1`, and
`T_K(1, s) = (q_K − 1)² q_K^(s − 1)` for `s ≥ 1`. -/
def WeilRankOneCountStatement.{uK, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    weilTwistIrreducibleCount.{uK, uW} K 0 0 =
        ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) ∧
      ∀ s : ℕ, 1 ≤ s →
        weilTwistIrreducibleCount.{uK, uW} K 0 s =
          (((K.canonicalTopologicalData.residueCardinality - 1) ^ 2 *
              K.canonicalTopologicalData.residueCardinality ^ (s - 1) : ℕ) : ℕ∞)

/-- Tame reduction in truncated form (route note, Proposition `prop:tame` and the proof
of Proposition `prop:LDcount`(c); Koch 1984, Satz 4; Henniart 1988, §3.1). Let
`n = p^r m` with `p ∤ m`. Suppose that for every `r' ≤ r`, every tamely and totally
ramified extension `L/K` of degree dividing `m` and every `j < p^r' e_L`,
`C_L(p^r', j) = (q_L − 1) q_L^j`. Then `C_K(n, j) = (q_K − 1) q_K^j` for every
`j < n e_K`. The rank `p^r m` is written `p ^ r * m - 1 + 1`, as `m ≥ 1`. -/
def WeilTameReductionStatement.{uK, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (r m : ℕ), ¬ p ∣ m →
    (∀ r' : ℕ, r' ≤ r →
      ∀ (L : PadicField.{uK} p) (ι : K.Carrier →ₐ[Padic p] L.Carrier) (d : ℕ), d ∣ m →
        IsTameTotallyRamifiedOfDegree K L ι d →
        ∀ j : ℕ, j < p ^ r' * L.canonicalTopologicalData.ramificationIndex →
          weilConductorCount.{uK, uW} L (p ^ r' - 1) j =
            (((L.canonicalTopologicalData.residueCardinality - 1) *
                L.canonicalTopologicalData.residueCardinality ^ j : ℕ) : ℕ∞)) →
    ∀ j : ℕ, j < p ^ r * m * K.canonicalTopologicalData.ramificationIndex →
      weilConductorCount.{uK, uW} K (p ^ r * m - 1) j =
        (((K.canonicalTopologicalData.residueCardinality - 1) *
            K.canonicalTopologicalData.residueCardinality ^ j : ℕ) : ℕ∞)

/-- Henniart (1988), Corollaire 1.4 (route note, Corollary `cor:14`): for `n = p^r` and
every integer `l ≥ 1` (the `λ` of the sources), `C_K(p^r, p^r l) = q_K · C_K(p^r, p^r l − 1)`
in `ℕ∞`. -/
def WeilConductorCountStepStatement.{uK, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (r l : ℕ), 1 ≤ l →
    weilConductorCount.{uK, uW} K (p ^ r - 1) (p ^ r * l) =
      (K.canonicalTopologicalData.residueCardinality : ℕ∞) *
        weilConductorCount.{uK, uW} K (p ^ r - 1) (p ^ r * l - 1)

/-- The truncated Théorème 1.3 of the proof of route note Proposition `prop:LDcount`(c):
assuming (LD), `C_K(k + 1, j) = (q_K − 1) q_K^j` for every p-adic field `K` and all
`j < (k + 1) e_K`. -/
def WeilTruncatedConductorCountStatement.{uK, uW} : Prop :=
  LaumonDeligneCountStatement.{uK, uW} →
    ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k j : ℕ),
      j < (k + 1) * K.canonicalTopologicalData.ramificationIndex →
        weilConductorCount.{uK, uW} K k j =
          (((K.canonicalTopologicalData.residueCardinality - 1) *
              K.canonicalTopologicalData.residueCardinality ^ j : ℕ) : ℕ∞)

/-- Route note, Proposition `prop:LDcount`: assuming (LD), for every p-adic field `K`
and all `k, s, f` with `s < (k + 1) e_K`, `|W_K(k + 1, s, f)| = ν(k + 1, f, s; q_K)`
in `ℕ∞`. -/
def LaumonDeligneWeilCountStatement.{uK, uW} : Prop :=
  LaumonDeligneCountStatement.{uK, uW} →
    ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k s f : ℕ),
      s < (k + 1) * K.canonicalTopologicalData.ramificationIndex →
        (weilRefinedStratum.{uK, uW} K k s f).encard =
          (polarPartCount K.canonicalTopologicalData.residueCardinality (k + 1) f s : ℕ∞)

end Langlands.Henniart
