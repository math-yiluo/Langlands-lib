import Langlands.Representation.Unitary.CompactQuotientNormalizedInductionDualityStatement
import Langlands.Representation.Unitary.Basic
import Langlands.HarmonicAnalysis.HomogeneousFunctions

/-! # Unitarity of normalized induction from a cocompact closed subgroup (Renard IV.2.3)

Renard 2026, IV.2.3 (printed pp.98–99 / PDF pp.104–105). For a closed subgroup `H` of a
t.d. group `G` with `H \ G` compact and a unitary representation `(τ, E)` of `H`, the
function `g ↦ ⟨f₁(g), f₂(g)⟩_E` of two elements of `i_H^G E` lies in
`𝒟(G, H, δ_{H\G})` (II.3.9), and integrating it against a positive `G`-invariant
functional `ν_{H\G}` on that space gives a `G`-invariant positive definite hermitian
form on `i_H^G τ`, which is therefore unitary.
-/

noncomputable section

universe uG v

namespace Langlands.Renard.CompactRepresentation

open Langlands.HarmonicAnalysis.HomogeneousFunctions

/-- Renard IV.2.3, (IV.2.3.1)–(IV.2.3.2): let `G` be a Hausdorff, locally compact,
nonarchimedean group, `H` a closed subgroup with `H \ G` compact, `χ` a smooth square root
with positive real values of the relative modular character `δ_{H\G}`, and `τ` a smooth
representation of `H` with an invariant positive definite hermitian form `⟨·, ·⟩_E`.
Then for all `f₁, f₂` in `i_H^G τ = ind_H^G(τ ⊗ χ)` the function
`g ↦ ⟨f₁(g), f₂(g)⟩_E` lies in the space `𝒟(G, H, δ_{H\G})` of II.3.9; and for every
nonzero, positive, right-`G`-invariant linear functional `ν` on `𝒟(G, H, δ_{H\G})`, the
form `⟨f₁, f₂⟩ = ν(g ↦ ⟨f₁(g), f₂(g)⟩_E)` is a `G`-invariant positive definite hermitian
form on `i_H^G τ`. In particular `i_H^G τ` is unitary. -/
def CompactQuotientUnitaryInductionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [T2Space G] (H : Subgroup G) (hH : IsClosed (H : Set G)),
    ∀ [LocallyCompactSpace H] [CompactSpace (Induction.LeftQuotient H)],
      let δ : Induction.SmoothCharacter ℂ H :=
        Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val
      let D := renardSpace H hH
      let R := rightAction H (relativeModular H hH)
      ∀ χ : Induction.SmoothCharacter ℂ H,
        (∀ h : H, ∃ r : ℝ, 0 < r ∧ ((χ.toMonoidHom h : ℂˣ) : ℂ) = r) →
        (∀ h : H, ((χ.toMonoidHom h : ℂˣ) : ℂ) ^ 2 = ((δ.toMonoidHom h : ℂˣ) : ℂ)) →
      ∀ (τ : SmoothRep.{0, uG, v} ℂ H) (b : InvariantPositiveForm τ.representation),
        let σ := Langlands.twist χ.toMonoidHom τ.representation
        let I := Induction.CompactFunctions H σ
        let ev : I → G → τ := fun f g => Induction.eval H σ f.1 g
        let π := Induction.normalizedCompactInduced H χ τ.representation
        (∃ c : I → I → D,
          (∀ (f₁ f₂ : I) (g : G), (c f₁ f₂).val g = b.inner (ev f₁ g) (ev f₂ g)) ∧
          ∀ ν : Module.Dual ℂ D, ν ≠ 0 →
            (∀ (g : G) (f : D), ν (R g f) = ν f) →
            (∀ f : D, (∀ x : G, (f.val x).im = 0 ∧ 0 ≤ (f.val x).re) →
              (ν f).im = 0 ∧ 0 ≤ (ν f).re) →
            ∃ B : InvariantPositiveForm π, ∀ f₁ f₂ : I, B.inner f₁ f₂ = ν (c f₁ f₂)) ∧
          IsUnitarizable π

end Langlands.Renard.CompactRepresentation
