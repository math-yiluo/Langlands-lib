import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed

/-! # The Néron–Ogg–Shafarevich criterion for good reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme

/-- The Néron–Ogg–Shafarevich criterion, in its inertia form. Let `V` be a discrete
valuation ring with fraction field `K`, let `B` be an abelian variety over `K` and let
`ℓ` be a prime invertible in `V`. Suppose that for every strictly Henselian discrete
valuation ring `W` with a local homomorphism `V → W` that carries the maximal ideal
of `V` onto a generator of the maximal ideal of `W`, with fraction field `L` over `K`,
and for every geometric point of `Spec L`, every element of the finite étale
fundamental group of `Spec L` acts trivially on the rational `ℓ`-adic Tate module of
the base change of `B` to `L`. Then `B` is the generic fibre of an abelian scheme
over `Spec V`. -/
def NeronOggShafarevichStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (B : AbelianScheme (Spec (.of K)))
    (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : V) →
    (∀ (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
        [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
        [Algebra V W] [IsLocalHom (algebraMap V W)],
        (maximalIdeal V).map (algebraMap V W) = maximalIdeal W →
      ∀ (L : Type u) [Field L] [Algebra W L] [IsFractionRing W L] [Algebra K L],
        (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) →
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
        (hu : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (.of L), ⊤)))
        (g : FundamentalGroup s (geometricFiberFinite s)),
        Tate.PrimeAdic.rationalMonodromyRepresentation s (geometricFiberFinite s)
          torsionFiniteEtale ((baseChange (Spec.algebraMap K L)).obj B) ℓ hu g = 1) →
    ∃ G : AbelianScheme (Spec (.of V)),
      Nonempty ((baseChange (Spec.algebraMap V K)).obj G ≅ B)

end Langlands.AbelianScheme
