import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed

/-! # The Galois criterion of semistable reduction from inertia of echelon two -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme

/-- Grothendieck's Galois criterion of semistable reduction over a strictly Henselian trait,
in the direction from inertia of echelon two to semiabelian reduction. Let `W` be a strictly
Henselian discrete valuation ring with fraction field `L`, let `A` be an abelian variety over
`L`, let `N` be a Néron model of `A` over `W` and let `ℓ` be a prime invertible in `W`.
Suppose that, for every geometric point of `Spec L` and all elements `g` and `h` of the
finite étale fundamental group of `Spec L`, `(g - 1) (h - 1) = 0` on the rational `ℓ`-adic
Tate module of `A`. Then the identity component of the geometric special fibre of `N` is an
extension of an abelian variety by a split torus. -/
def StrictHenselianEchelonTwoSemiabelianStatement : Prop :=
  ∀ (W L : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Field L] [Algebra W L] [IsFractionRing W L]
    (A : AbelianScheme (Spec (.of L))) (N : NeronModel W L A) (ℓ : ℕ) [Fact ℓ.Prime],
    IsUnit (ℓ : W) →
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
        (hu : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (.of L), ⊤)))
        (g h : FundamentalGroup s (geometricFiberFinite s)),
        ((Tate.PrimeAdic.rationalMonodromyRepresentation s
            (geometricFiberFinite s) torsionFiniteEtale A ℓ hu g).toLinearMap - 1) *
          ((Tate.PrimeAdic.rationalMonodromyRepresentation s
            (geometricFiberFinite s) torsionFiniteEtale A ℓ hu h).toLinearMap - 1) = 0) →
    N.HasGeometricSemiabelianReduction

end Langlands.AbelianScheme
