import Langlands.Representation.Classification.TadicMultisegments

/-!
# Three lemmas of Tadić's exhaustion argument

Tadić 1986, Lemma 4.8(ii) (existence of the factorization), Lemma 6.3 and
Corollary A.6(ii) (for finitely many factors), for actual smooth complex
representations of `GL_n(F)`. All assertions below are proposition definitions;
none is proved.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Tadić 1986 Lemma 4.8(ii), existence part, p.360: assume `(U^m)`. Let `π` be an
irreducible unitarizable representation of `GL_(m+1)` that is not a Zelevinsky socle
`⟨a(n,d)^ρ⟩` with `n, d > 0` and `ρ` unitary cuspidal. Then `π` is isomorphic to the
normalized product of a finite family of members of `X_m`. Tadić's `m` is `m + 1`
here. -/
def TadicBlockReduction : Prop :=
  letI := T.topology
  ∀ m : ℕ, TadicSocleUnitarity.{uF, uV} F T m →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + 1) F.Carrier),
      Representation.IsIrreducible π.representation → IsUnitarizable π.representation →
      (¬ ∃ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d),
          0 < n ∧ ρ.IsUnitary ∧ (tadicMultisegment ρ n d hd).IsZelevinskySocle π) →
      ∃ (B : BlockShape (m + 1))
        (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
        (∀ i, IsTadicXBlock m (σ i)) ∧
          Nonempty (π ≅ (T.normalizedProductInductionFunctor B).obj σ)

/-- Tadić 1986 Lemma 6.3, p.366: for `0 < n < d` and every cuspidal `ρ`, a
Langlands head of `a(n,d)^ρ` is never isomorphic to a Zelevinsky socle of
`a(n,d)^ρ`: `L(a(n,d)^ρ) ≇ ⟨a(n,d)^ρ⟩`. -/
def TadicRectangleHeadSocleDistinct : Prop :=
  letI := T.topology
  ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d), 0 < n → n < d →
    ∀ {N : ℕ} (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      (tadicMultisegment ρ n d hd).IsLanglandsHead π →
        (tadicMultisegment ρ n d hd).IsZelevinskySocle π' → ¬ Nonempty (π ≅ π')

/-- Tadić 1986 Corollary A.6(ii), p.375, for finitely many factors: if `π_i` is a
Langlands head of `a_i` for each block of `B` and the normalized product of the
`π_i` is irreducible, then that product is a Langlands head of `∑ a_i`:
`L(a_1) × ⋯ × L(a_k) = L(a_1 + ⋯ + a_k)`. -/
def IrreducibleLanglandsHeadProduct : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n) (a : Fin B.length → T.Multisegment.{max uF uV, uF})
    (π : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, (a i).IsLanglandsHead (π i)) →
      Representation.IsIrreducible
        ((T.normalizedProductInductionFunctor B).obj π).representation →
      (∑ i, a i).IsLanglandsHead ((T.normalizedProductInductionFunctor B).obj π)

/-- Tadić 1986 Lemma 4.8(ii) (existence), Lemma 6.3 and Corollary A.6(ii) together. -/
def TadicExhaustionLemmaStatements : Prop :=
  TadicBlockReduction.{uF, uV} F T ∧ TadicRectangleHeadSocleDistinct.{uF, uV} F T ∧
    IrreducibleLanglandsHeadProduct.{uF, uV} F T

end Langlands.Classification
