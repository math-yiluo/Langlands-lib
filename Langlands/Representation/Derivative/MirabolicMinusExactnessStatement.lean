import Langlands.Representation.Derivative.MirabolicMinus

/-!
# Exactness of the mirabolic minus functors

The four actual Bernstein–Zelevinsky minus functors, unnormalized and
determinant-normalized `Ψ⁻ : P_(n+1) → GL_n` and `Φ⁻ : P_(n+2) → P_(n+1)`, carry
short exact sequences of smooth complex representations to short exact sequences
of their underlying intertwiners. This module states that assertion and proves
nothing.
-/

namespace Langlands.Derivative.Mirabolic

open CategoryTheory GeneralLinear HarmonicAnalysis

/-- The functor `J` carries every short exact sequence of actual intertwiners to a
short exact sequence: for `i : A ⟶ B` injective, `q : B ⟶ C` surjective and
`range i = ker q`, the maps `J.map i` and `J.map q` are injective and surjective
with `range (J.map i) = ker (J.map q)`. -/
def MapsShortExactIntertwiners.{uG, uH, uV} {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H]
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H) : Prop :=
  ∀ (A B C : SmoothRep.{0, uG, uV} ℂ G) (i : A ⟶ B) (q : B ⟶ C),
    Function.Injective (SmoothRep.hom i) →
    Function.Surjective (SmoothRep.hom q) →
    LinearMap.range (SmoothRep.hom i).toLinearMap =
      LinearMap.ker (SmoothRep.hom q).toLinearMap →
    Function.Injective (SmoothRep.hom (J.map i)) ∧
      LinearMap.range (SmoothRep.hom (J.map i)).toLinearMap =
        LinearMap.ker (SmoothRep.hom (J.map q)).toLinearMap ∧
      Function.Surjective (SmoothRep.hom (J.map q))

/-- Exactness of the actual unnormalized `Ψ⁻`, unnormalized `Φ⁻`, normalized `Ψ⁻`
and normalized `Φ⁻` functors, for every `n` and every supplied nontrivial unitary
additive character `ψ`. -/
def MinusExactnessStatement.{uF, uV} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  (∀ n : ℕ, MapsShortExactIntertwiners (psiMinusUnnormalized.{uV} T n)) ∧
  (∀ n : ℕ, ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    MapsShortExactIntertwiners (phiMinusUnnormalized.{uV} T ψ n)) ∧
  (∀ n : ℕ, MapsShortExactIntertwiners (psiMinus.{uV} T n)) ∧
  (∀ n : ℕ, ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    MapsShortExactIntertwiners (phiMinus.{uV} T ψ n))

end Langlands.Derivative.Mirabolic
