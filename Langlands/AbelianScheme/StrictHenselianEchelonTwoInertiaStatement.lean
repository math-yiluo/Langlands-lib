import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Unipotence of echelon two of an open subgroup of inertia on Tate modules -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme

/-- Grothendieck's theorem that an open subgroup of inertia acts unipotently of echelon two
on the Tate module of an abelian variety, over a strictly Henselian trait. Let `W` be a
strictly Henselian discrete valuation ring with fraction field `L`, let `A` be an abelian
variety over `L` and let `ℓ` be a prime invertible in `W`. For every geometric point of
`Spec L` there is an open subgroup `H` of the finite étale fundamental group of `Spec L`
such that `(g - 1) (h - 1) = 0` on the rational `ℓ`-adic Tate module of `A` for all `g` and
`h` in `H`. -/
def StrictHenselianEchelonTwoInertiaStatement : Prop :=
  ∀ (W L : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Field L] [Algebra W L] [IsFractionRing W L]
    (A : AbelianScheme (Spec (.of L))) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : W) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
      (hu : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (.of L), ⊤))),
      ∃ H : OpenSubgroup (FundamentalGroup s (geometricFiberFinite s)),
        ∀ g ∈ H, ∀ h ∈ H,
          ((Tate.PrimeAdic.rationalMonodromyRepresentation s
              (geometricFiberFinite s) torsionFiniteEtale A ℓ hu g).toLinearMap - 1) *
            ((Tate.PrimeAdic.rationalMonodromyRepresentation s
              (geometricFiberFinite s) torsionFiniteEtale A ℓ hu h).toLinearMap - 1) = 0

end Langlands.AbelianScheme
