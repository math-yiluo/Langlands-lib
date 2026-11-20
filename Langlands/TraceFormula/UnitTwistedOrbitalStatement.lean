import Langlands.TraceFormula.TwistedOrbital
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Twisted orbital integrals of a compact open subgroup's characteristic function

These derived statements isolate the quotient-measure calculation underlying Getz–Hahn
2024, Lemma 17.8.3 and its proof (printed p. 464), for twisted orbital integrals as in
(18.32) (printed p. 487). The source obtains the local coset condition using properness
and Exercise 17.15 (printed p. 470).

`UnitTwistedOrbitalIntegralStatement` gives integrability and the value `μ(K) / μC(C ∩ K)`
for supplied compatible measures, conditional on the coset property at `δ`.
`RestrictedProductTwistedCosetStatement` reduces the coset property to the factors of a
restricted product. `SplitTwistedCosetStatement` reduces it for the cyclic shift to the
ordinary coset property at the ordered product `δ 0 * δ 1 * ⋯ * δ m`.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration
open scoped RestrictedProduct

universe u w

/-- The twisted orbital integral of the characteristic function of a compact open subgroup.
Let `K` be a compact open subgroup of `G`, `θ` a continuous endomorphism with `θ K ⊆ K`, and
`δ ∈ K`. If every `x` with `x⁻¹ * δ * θ x ∈ K` is `c * k` with `c` in the `θ`-centralizer `C`
of `δ` and `k ∈ K`, then for compatible quotient measures the twisted orbit function of the
characteristic function of `K` is integrable and its integral is `μ(K) / μC(C ∩ K)`. -/
def UnitTwistedOrbitalIntegralStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (θ : G →* G), Continuous θ →
    ∀ (K : Subgroup G), IsCompact (K : Set G) → IsOpen (K : Set G) →
    (∀ k ∈ K, θ k ∈ K) →
    ∀ δ ∈ K,
    ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
      [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
      (μC : Measure (twistedCentralizer θ δ))
      [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
      (ν : Measure (LeftQuotient (twistedCentralizer θ δ))),
      IsCompatible (twistedCentralizer θ δ) μ μC ν →
      (∀ x : G, x⁻¹ * δ * θ x ∈ K →
        ∃ c ∈ twistedCentralizer θ δ, ∃ k ∈ K, x = c * k) →
      Integrable
          (twistedOrbitFunction θ δ ((K : Set G).indicator fun _ => (1 : ℂ))) ν ∧
        twistedOrbitalIntegral θ δ ν ((K : Set G).indicator fun _ => (1 : ℂ)) =
          (((μ (K : Set G)).toReal /
            (μC (Subtype.val ⁻¹' (K : Set G))).toReal : ℝ) : ℂ)

/-- Coset decompositions on a restricted product. Let `θ` act on the restricted product of
the `G i` with respect to subgroups `K i` componentwise by endomorphisms `θ' i` with
`θ' i (K i) ⊆ K i`. If in every factor each `y` with `y⁻¹ * δ i * θ' i y ∈ K i` is `c * k` with
`c` in the `θ' i`-centralizer of `δ i` and `k ∈ K i`, then each `x` of the restricted product
whose twisted conjugate `x⁻¹ * δ * θ x` lies in `K i` at every `i` is `c * k` with `c` in the
`θ`-centralizer of `δ` and `k i ∈ K i` for every `i`. -/
def RestrictedProductTwistedCosetStatement : Prop :=
  ∀ {ι : Type w} {G : ι → Type u} [∀ i, Group (G i)] (K : ∀ i, Subgroup (G i))
    (θ' : ∀ i, G i →* G i), (∀ i, ∀ k ∈ K i, θ' i k ∈ K i) →
    ∀ (θ : (Πʳ i, [G i, K i]) →* (Πʳ i, [G i, K i])), (∀ x i, θ x i = θ' i (x i)) →
    ∀ δ : Πʳ i, [G i, K i],
      (∀ i, ∀ y : G i, y⁻¹ * δ i * θ' i y ∈ K i →
        ∃ c ∈ twistedCentralizer (θ' i) (δ i), ∃ k ∈ K i, y = c * k) →
      ∀ x : Πʳ i, [G i, K i], (∀ i, (x⁻¹ * δ * θ x) i ∈ K i) →
        ∃ c ∈ twistedCentralizer θ δ, ∃ k : Πʳ i, [G i, K i], (∀ i, k i ∈ K i) ∧ x = c * k

/-- Coset decompositions for the cyclic shift. Let `θ` be the cyclic shift
`(θ x) i = x (i + 1)` on `Fin (m + 1) → H`, let `K` be a subgroup of `H` and let `δ` have all
components in `K`. If each `y` with `y⁻¹ * N * y ∈ K`, where
`N = δ 0 * δ 1 * ⋯ * δ m`, is `c * k` with `c` commuting with `N` and `k ∈ K`, then each `x`
whose twisted conjugate `x⁻¹ * δ * θ x` has all components in `K` is `c * k` with `c` in the
`θ`-centralizer of `δ` and all components of `k` in `K`. -/
def SplitTwistedCosetStatement : Prop :=
  ∀ {H : Type u} [Group H] (K : Subgroup H) (m : ℕ)
    (θ : (Fin (m + 1) → H) →* (Fin (m + 1) → H)), (∀ x, θ x = x ∘ finRotate (m + 1)) →
    ∀ δ : Fin (m + 1) → H, (∀ i, δ i ∈ K) →
      (∀ y : H, y⁻¹ * (List.ofFn δ).prod * y ∈ K →
        ∃ c ∈ Subgroup.centralizer {(List.ofFn δ).prod}, ∃ k ∈ K, y = c * k) →
      ∀ x : Fin (m + 1) → H, (∀ i, (x⁻¹ * δ * θ x) i ∈ K) →
        ∃ c ∈ twistedCentralizer θ δ, ∃ k : Fin (m + 1) → H, (∀ i, k i ∈ K) ∧ x = c * k

end Langlands.TraceFormula
