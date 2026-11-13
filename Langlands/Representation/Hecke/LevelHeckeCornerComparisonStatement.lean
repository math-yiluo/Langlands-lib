import Langlands.Representation.Hecke.Corner
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Shimura.LevelHeckeAlgebra

/-!
# The measure-free level Hecke algebra and the Haar-measure `H(G, K)`

For a t.d. group `G` with a left Haar measure `μ` and a compact open subgroup `K`, the algebra
`ℂ[G/K]^K` of left `K`-invariant finitely supported functions on `G/K` with coset convolution is
isomorphic to the corner `H(G, K) = e_K H(G) e_K` of bi-`K`-invariant test functions with
`μ`-convolution, by `a ↦ μ(K)⁻¹ a`, compatibly with the actions on `K`-fixed vectors.
-/

namespace Langlands.Hecke

open MeasureTheory Langlands.Shimura.LevelHecke

universe u v

/-- Comparison of the two Hecke algebras of a compact open subgroup (Renard III.1.5 and
VI.9.4): for a t.d. group `G` with a left Haar measure `μ` and a compact open subgroup `K`,
there is a complex-linear multiplicative bijection `e` from `LevelHeckeAlgebra ℂ K` onto
`HeckeAlgebra.Corner μ K hK` with `e(a)(x) = μ(K)⁻¹ a(xK)`, and for every smooth representation
the action of `a` on `K`-fixed vectors is the Hecke action of `e(a)`. -/
def LevelHeckeCornerComparisonStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    ∃ e : LevelHeckeAlgebra ℂ K.toSubgroup ≃ₗ[ℂ] HeckeAlgebra.Corner μ K hK,
      (∀ a b : LevelHeckeAlgebra ℂ K.toSubgroup, e (a * b) = e a * e b) ∧
      (∀ (a : LevelHeckeAlgebra ℂ K.toSubgroup) (x : G),
        e a x = (μ.real (K : Set G) : ℂ)⁻¹ *
          (show HeckeSpace ℂ K.toSubgroup K.toSubgroup from a).1
            (x : G ⧸ K.toSubgroup)) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
        (hρ : IsSmooth ρ) (a : LevelHeckeAlgebra ℂ K.toSubgroup)
        (w : fixedVectors ρ K.toSubgroup),
        ((a • w : fixedVectors ρ K.toSubgroup) : V) =
          heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (e a)) w

end Langlands.Hecke
