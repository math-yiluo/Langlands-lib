import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.PointDefect

/-! # Closures of points of ramification index one have good charts -/

universe u

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- Let `R` be a discrete valuation ring and `A` an `R`-algebra of finite type. Let `J` be the
intersection of a non-empty set `S` of ideals, each of which is the preimage of the maximal
ideal under a point of `A` with values in a discrete valuation ring of ramification index one
over `R`. Then there is `s ∉ J` such that over every localization `A'` of `A` away from `s`
the ring `A' ⧸ J A'` is smooth over the residue field of `R` (after the harmless base change
to it) and `(A' ⧸ J A') ⊗_{A'} Ω_{A'/R}` is a free `A' ⧸ J A'`-module. -/
def GoodChartStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (J : Ideal A) (S : Set (Ideal A)),
    J = sInf S → S.Nonempty →
    (∀ p ∈ S, ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'')
      (_ : IsDiscreteValuationRing R'') (_ : Algebra R R'') (_ : IsLocalHom (algebraMap R R''))
      (ψ : A →ₐ[R] R''), IsRamificationIndexOne R R'' ∧
        (IsLocalRing.maximalIdeal R'').comap ψ = p) →
    ∃ s : A, s ∉ J ∧ ∀ (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalization.Away s A']
      [Algebra R A'] [IsScalarTower R A A'],
      Algebra.Smooth (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] (A' ⧸ J.map (algebraMap A A'))) ∧
      Module.Free (A' ⧸ J.map (algebraMap A A'))
        ((A' ⧸ J.map (algebraMap A A')) ⊗[A'] Ω[A'⁄R])

end Langlands.AlgebraicGeometry.DvrSmoothening
