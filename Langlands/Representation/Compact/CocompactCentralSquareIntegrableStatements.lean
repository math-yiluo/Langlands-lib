import Langlands.Representation.Category.Twist
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Unitary.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RepresentationTheory.Semisimple

/-! # Integrals over `G/A` for a cocompact central subgroup `A` (Renard IV.3.3, Remark)

Renard 2026, IV.3.3, Remark (printed p.102 / PDF p.108): if `A` is a subgroup of `Z(G)` with
`Z(G)/A` compact, integrals over `G/Z(G)` may be replaced by integrals over `G/A` without
affecting their convergence, and the results of IV.3.2–IV.3.3 remain valid. The definitions of
IV.3.2 are kept (the centre acts by a unitary character); only the integrals over `G/Z(G)` are
replaced by integrals over `G/A`.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.3.3, Remark, for a t.d. group `G`, a closed normal subgroup `A ≤ Z(G)` with
`Z(G)/A` compact, a Haar measure `μZ` on `G/Z(G)` and a Haar measure `μ` on `G/A`, both also
right invariant. Write `SqIntModA π` when `Z(G)` acts on `π` by a unitary character and every
function on `G/A` with values `|ℓ(π(g) x)|` is square integrable for `μ`, and `EssSqIntModA π`
when some smooth twist of `π` satisfies `SqIntModA`. Then:

* (convergence) if `Z(G)` acts on `π` by a unitary character, the coefficient norms of `π` are
  square integrable on `G/Z(G)` exactly when they are on `G/A`;
* (IV.3.2, Proposition) an irreducible `π` with `EssSqIntModA π` is admissible;
* (IV.3.2, Lemma) an admissible `π` with `SqIntModA π` is unitarizable and semisimple;
* (IV.3.3, Lemma) (i) an irreducible `π` with `EssSqIntModA π` has a formal degree `d > 0`
  for `μ`: every function `F` on `G/A` with `F(gA) = ℓ₁(π(g) x₁) ℓ₂(π(g⁻¹) x₂)` is integrable
  with `∫ F dμ = ℓ₁(x₂) ℓ₂(x₁) / d`; (ii) for non-isomorphic irreducible `π₁`, `π₂` with
  `EssSqIntModA` and the same central character, such integrals over `G/A` vanish;
* (IV.3.3, Corollary) matrix coefficients of pairwise non-isomorphic irreducible
  representations with `EssSqIntModA` and a common central character, at nonzero vectors and
  functionals, are linearly independent. -/
def CocompactCentralSquareIntegrableStatements : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Subgroup G) [A.Normal], IsClosed (A : Set G) → A ≤ Subgroup.center G →
    CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G)) →
    ∀ [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
      (μZ : Measure (G ⧸ Subgroup.center G)) [μZ.IsHaarMeasure] [μZ.IsMulRightInvariant]
      [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
      (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    let ActsBy : SmoothRep.{0, u, v} ℂ G → (Subgroup.center G →* ℂˣ) → Prop := fun π χ =>
      ∀ (z : Subgroup.center G) (x : π), π.representation (z : G) x = (χ z : ℂ) • x
    let SqIntModA : SmoothRep.{0, u, v} ℂ G → Prop := fun π =>
      (∃ χ : Subgroup.center G →* ℂˣ, (∀ z, ‖(χ z : ℂ)‖ = 1) ∧ ActsBy π χ) ∧
        ∀ (ℓ : SmoothDual π.representation) (x : π) (F : G ⧸ A → ℝ),
          (∀ g : G, F (QuotientGroup.mk g) =
            ‖(ℓ : Module.Dual ℂ π) (π.representation g x)‖) →
          MemLp F 2 μ
    let EssSqIntModA : SmoothRep.{0, u, v} ℂ G → Prop := fun π =>
      ∃ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)), SqIntModA (π.twist ω hω)
    -- convergence is unaffected
    (∀ π : SmoothRep.{0, u, v} ℂ G,
      (∃ χ : Subgroup.center G →* ℂˣ, (∀ z, ‖(χ z : ℂ)‖ = 1) ∧ ActsBy π χ) →
      ∀ (ℓ : SmoothDual π.representation) (x : π)
        (FZ : G ⧸ Subgroup.center G → ℝ) (FA : G ⧸ A → ℝ),
        (∀ g : G, FZ (QuotientGroup.mk g) =
          ‖(ℓ : Module.Dual ℂ π) (π.representation g x)‖) →
        (∀ g : G, FA (QuotientGroup.mk g) =
          ‖(ℓ : Module.Dual ℂ π) (π.representation g x)‖) →
        (MemLp FZ 2 μZ ↔ MemLp FA 2 μ)) ∧
    -- IV.3.2, Proposition
    (∀ π : SmoothRep.{0, u, v} ℂ G, π.IsIrreducible → EssSqIntModA π → π.IsAdmissible) ∧
    -- IV.3.2, Lemma
    (∀ π : SmoothRep.{0, u, v} ℂ G, π.IsAdmissible → SqIntModA π →
      IsUnitarizable π.representation ∧
        Representation.IsSemisimpleRepresentation π.representation) ∧
    -- IV.3.3, Lemma
    ((∀ π : SmoothRep.{0, u, v} ℂ G, π.IsIrreducible → EssSqIntModA π →
      ∃ d : ℝ, 0 < d ∧
        ∀ (x₁ x₂ : π) (ℓ₁ ℓ₂ : SmoothDual π.representation) (F : G ⧸ A → ℂ),
          (∀ g : G, F (QuotientGroup.mk g) =
            (ℓ₁ : Module.Dual ℂ π) (π.representation g x₁) *
              (ℓ₂ : Module.Dual ℂ π) (π.representation g⁻¹ x₂)) →
          Integrable F μ ∧
            ∫ q, F q ∂μ = (ℓ₁ : Module.Dual ℂ π) x₂ * (ℓ₂ : Module.Dual ℂ π) x₁ / d) ∧
    ∀ π₁ π₂ : SmoothRep.{0, u, v} ℂ G, π₁.IsIrreducible → π₂.IsIrreducible →
      EssSqIntModA π₁ → EssSqIntModA π₂ → IsEmpty (π₁ ≅ π₂) →
      (∃ χ : Subgroup.center G →* ℂˣ, ActsBy π₁ χ ∧ ActsBy π₂ χ) →
      ∀ (x₁ : π₁) (x₂ : π₂) (ℓ₁ : SmoothDual π₁.representation)
        (ℓ₂ : SmoothDual π₂.representation) (F : G ⧸ A → ℂ),
        (∀ g : G, F (QuotientGroup.mk g) =
          (ℓ₁ : Module.Dual ℂ π₁) (π₁.representation g x₁) *
            (ℓ₂ : Module.Dual ℂ π₂) (π₂.representation g⁻¹ x₂)) →
        Integrable F μ ∧ ∫ q, F q ∂μ = 0) ∧
    -- IV.3.3, Corollary
    ∀ (r : ℕ) (π : Fin r → SmoothRep.{0, u, v} ℂ G),
      (∀ i, (π i).IsIrreducible) → (∀ i, EssSqIntModA (π i)) →
      (∀ i j, i ≠ j → IsEmpty (π i ≅ π j)) →
      (∃ χ : Subgroup.center G →* ℂˣ, ∀ i, ActsBy (π i) χ) →
      ∀ (x : ∀ i, π i) (ℓ : ∀ i, SmoothDual (π i).representation),
        (∀ i, x i ≠ 0) → (∀ i, ℓ i ≠ 0) →
        LinearIndependent ℂ (fun i => matrixCoefficient (π i).representation (ℓ i) (x i))

end Langlands.Renard.CompactRepresentation
