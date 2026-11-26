import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed

/-! # Quasi-unipotence of inertia on Tate modules of abelian varieties -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme

/-- Grothendieck's monodromy theorem for abelian varieties, element by element. Let `W` be a
strictly Henselian discrete valuation ring with fraction field `L`, let `A` be an abelian
variety over `L` and let `ℓ` be a prime invertible in `W`. For every geometric point of
`Spec L` and every element `g` of the finite étale fundamental group of `Spec L`, some
positive power of `g` acts unipotently on the rational `ℓ`-adic Tate module of `A`. -/
def AbelianInertiaQuasiUnipotentStatement : Prop :=
  ∀ (W L : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Field L] [Algebra W L] [IsFractionRing W L]
    (A : AbelianScheme (Spec (.of L))) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : W) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
      (hu : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (.of L), ⊤)))
      (g : FundamentalGroup s (geometricFiberFinite s)),
      ∃ m : ℕ, 0 < m ∧
        IsNilpotent ((Tate.PrimeAdic.rationalMonodromyRepresentation s
          (geometricFiberFinite s) torsionFiniteEtale A ℓ hu (g ^ m)).toLinearMap - 1)

end Langlands.AbelianScheme
