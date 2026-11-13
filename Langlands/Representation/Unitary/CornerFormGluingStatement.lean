import Langlands.Representation.Hecke.CornerAction
import Langlands.Representation.Hecke.UnimodularStar
import Langlands.Representation.Unitary.Basic

/-!
# Gluing corner-adjoint forms on fixed vectors into an invariant inner product

The proposition `CornerFormGluingStatement` says: a smooth complex representation `ρ` of a
unimodular topological group is unitarizable as soon as, below some compact open
subgroup `K₀` with `ρ^{K₀} ≠ 0`, every fixed space `ρ^K` is a finite-dimensional simple
module over the corner `e_K H(G) e_K` that carries a positive definite Hermitian form
for which the involution `f ↦ f*`, `f*(x) = conj (f x⁻¹)`, is adjoint to the action.
-/

namespace Langlands

open MeasureTheory MeasureTheory.Measure

universe uG uV

/-- Corner forms glue to an invariant positive definite Hermitian form: steps 4 and 5 of
the outline in `Langlands/Representation/Unitary/CharacterLimitSubquotientsStatement.md`,
after Tadic (1986), proof of Theorem 2.7. -/
def CornerFormGluingStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K₀ : OpenSubgroup G), IsCompact (K₀ : Set G) →
    (∃ v₀ ∈ fixedVectors ρ K₀.toSubgroup, v₀ ≠ 0) →
    (∀ K : OpenSubgroup G, IsCompact (K : Set G) → K ≤ K₀ →
      FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) →
    (∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), K ≤ K₀ →
      letI := Hecke.cornerModule μ ρ hρ K hK
      IsSimpleModule (Hecke.HeckeAlgebra.Corner μ K hK) (fixedVectors ρ K.toSubgroup)) →
    (∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), K ≤ K₀ →
      ∃ b : InnerProductSpace.Core ℂ (fixedVectors ρ K.toSubgroup),
        ∀ (f : Hecke.HeckeAlgebra.Corner μ K hK) (x y : fixedVectors ρ K.toSubgroup),
          b.inner (Hecke.cornerAction μ ρ hρ K hK f x) y =
            b.inner x (Hecke.cornerAction μ ρ hρ K hK (star f) y)) →
    IsUnitarizable ρ

end Langlands
