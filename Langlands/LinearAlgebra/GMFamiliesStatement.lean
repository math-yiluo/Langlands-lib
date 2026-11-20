import Langlands.LinearAlgebra.GMFamilies

/-! # Statements of Arthur's lemmas on `(G, M)`-families

Arthur 2005, §17: Lemma 17.1 (`c_M` extends smoothly), Lemma 17.4 (the splitting formula),
Lemma 17.5 (the descent formula) and Lemma 17.6 (the alternate splitting formula), for the objects
of `Langlands.LinearAlgebra.GMFamilies`. The identities of smooth functions in Lemmas 17.4–17.6
are stated on the complement of finitely many hyperplanes of `i𝔞_M^*`, where every term is given
by its defining formula. -/

noncomputable section

open scoped RealInnerProductSpace ContDiff

universe u

namespace Langlands.GMFamily

/-- **Arthur 2005, Lemma 17.1.** For a `(G, M)`-family `{c_P}`, the function
`c_M(λ) = ∑_{P ∈ 𝓟(M)} c_P(λ) θ_P(λ)⁻¹` extends to a smooth function on `i𝔞_M^*`. -/
def SmoothExtensionStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : Finset E) (a : Submodule ℝ E), IsRootSet R → IsLeviSpace R a →
    ∀ c : Finset E → StrongDual ℝ a → ℂ, IsFamily R a c →
      ∃ f : StrongDual ℝ a → ℂ, ContDiff ℝ ∞ f ∧
        ∀ Λ : StrongDual ℝ a, (∀ S ∈ parabolics R a, theta a S Λ ≠ 0) → f Λ = cM R a c Λ

/-- **Arthur 2005, Lemma 17.4 (splitting formula).** For two `(G, M)`-families `{c_P}`, `{d_P}`,
`(cd)_M(λ) = ∑_{Q ∈ 𝓕(M)} c_M^Q(λ) d'_Q(λ_Q)`. -/
def SplittingFormulaStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : Finset E) (a : Submodule ℝ E), IsRootSet R → IsLeviSpace R a →
    ∀ c d : Finset E → StrongDual ℝ a → ℂ, IsFamily R a c → IsFamily R a d →
      ∃ E₀ : Finset a, (0 : a) ∉ E₀ ∧ ∀ Λ : StrongDual ℝ a, (∀ e ∈ E₀, Λ e ≠ 0) →
        cM R a (familyMul a c d) Λ =
          ∑ Q ∈ faces R a, cQM R a c Q Λ * dPrime R a d Q (paramProj a (faceSpace R a Q) Λ)

/-- **Arthur 2005, Lemma 17.5 (descent formula), for Levi subgroups over the same field.**
Let `M₁ ⊆ M` be Levi subgroups (`a₁ = 𝔞_{M₁} ⊇ a = 𝔞_M`, both Levi spaces of the root set `R`).
For a `(G, M₁)`-family `{c_{P₁}}`, the induced `(G, M)`-family, and `ξ ∈ 𝔞_{M₁}^M` in general
position, `c_M(λ) = ∑_{L₁ ∈ 𝓛(M₁)} d_{M₁}^G(M, L₁) c_{M₁}^{Q₁}(λ)`, with `Q₁` the section attached
to `ξ`. The case of a Levi subgroup `M₁` over a proper extension of the field of `M` is not stated
(see the Markdown). -/
def DescentFormulaStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : Finset E) (a a₁ : Submodule ℝ E), IsRootSet R → IsLeviSpace R a₁ → IsLeviSpace R a →
    a ≤ a₁ →
    ∀ c₁ : Finset E → StrongDual ℝ a₁ → ℂ, IsFamily R a₁ c₁ →
      ∀ ξ ∈ a₁ ⊓ aᗮ,
        (∀ L₁ ∈ leviSpaces R a₁, dDescent a (centralSpace R) a₁ L₁ ≠ 0 →
          ∀ p : E, p ∈ L₁ ⊓ (centralSpace R)ᗮ → p - ξ ∈ a ⊓ (centralSpace R)ᗮ →
            IsRegular R L₁ p) →
        ∃ E₀ : Finset a, (0 : a) ∉ E₀ ∧ ∀ Λ : StrongDual ℝ a, (∀ e ∈ E₀, Λ e ≠ 0) →
          cM R a (inducedFamily R a a₁ c₁) Λ =
            ∑ L₁ ∈ leviSpaces R a₁, (dDescent a (centralSpace R) a₁ L₁ : ℂ) *
              cQM R a₁ c₁ (descentSection R a (centralSpace R) ξ L₁) (extendParam a a₁ Λ)

/-- **Arthur 2005, Lemma 17.6 (alternate splitting formula).** For two `(G, M)`-families and
`ξ ∈ 𝔞_M^G` in general position, `(cd)_M(λ) = ∑_{L₁, L₂ ∈ 𝓛(M)} d_M^G(L₁, L₂) c_M^{Q₁}(λ) d_M^{Q₂}(λ)`,
with `(Q₁, Q₂)` the section attached to `ξ`. -/
def AlternateSplittingFormulaStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : Finset E) (a : Submodule ℝ E), IsRootSet R → IsLeviSpace R a →
    ∀ c d : Finset E → StrongDual ℝ a → ℂ, IsFamily R a c → IsFamily R a d →
      ∀ ξ ∈ a ⊓ (centralSpace R)ᗮ,
        (∀ L₁ ∈ leviSpaces R a, ∀ L₂ ∈ leviSpaces R a, dCoeff R a L₁ L₂ ≠ 0 →
          ∀ ξ₁ ξ₂ : E, ξ₁ ∈ L₁ ⊓ (centralSpace R)ᗮ → ξ₂ ∈ L₂ ⊓ (centralSpace R)ᗮ →
            (2 : ℝ) • ξ = ξ₁ - ξ₂ → IsRegular R L₁ ξ₁ ∧ IsRegular R L₂ ξ₂) →
        ∃ E₀ : Finset a, (0 : a) ∉ E₀ ∧ ∀ Λ : StrongDual ℝ a, (∀ e ∈ E₀, Λ e ≠ 0) →
          cM R a (familyMul a c d) Λ =
            ∑ L₁ ∈ leviSpaces R a, ∑ L₂ ∈ leviSpaces R a, (dCoeff R a L₁ L₂ : ℂ) *
              cQM R a c (splittingSection R ξ L₁ L₂).1 Λ *
                cQM R a d (splittingSection R ξ L₁ L₂).2 Λ

/-- Arthur's lemmas on `(G, M)`-families: the conjunction of the statements of this module. -/
def GMFamilyStatement : Prop :=
  SmoothExtensionStatement.{u} ∧ SplittingFormulaStatement.{u} ∧ DescentFormulaStatement.{u} ∧
    AlternateSplittingFormulaStatement.{u}

end Langlands.GMFamily
