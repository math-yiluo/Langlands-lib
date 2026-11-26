import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed

/-! # Semiabelian reduction from unipotent inertia -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme

/-- Grothendieck's Galois criterion of semistable reduction, in the direction from
unipotent inertia to semiabelian reduction. Let `V` be a discrete valuation ring with
fraction field `K`, let `B` be an abelian variety over `K`, let `N` be a Néron model of `B`
over `V` and let `ℓ` be a prime invertible in `V`. Suppose that for every strictly
Henselian discrete valuation ring `W` with a local homomorphism `V → W` that carries the
maximal ideal of `V` onto a generator of the maximal ideal of `W`, with fraction field `L`
over `K`, and for every geometric point of `Spec L`, every element of the finite étale
fundamental group of `Spec L` acts unipotently on the rational `ℓ`-adic Tate module of the
base change of `B` to `L`. Then the identity component of the geometric special fibre of
`N` is an extension of an abelian variety by a split torus. -/
def UnipotentInertiaSemiabelianReductionStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (B : AbelianScheme (Spec (.of K)))
    (N : NeronModel V K B) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : V) →
    (∀ (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
        [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
        [Algebra V W] [IsLocalHom (algebraMap V W)],
        (maximalIdeal V).map (algebraMap V W) = maximalIdeal W →
      ∀ (L : Type u) [Field L] [Algebra W L] [IsFractionRing W L] [Algebra K L],
        (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) →
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
        (hu : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (.of L), ⊤)))
        (g : FundamentalGroup s (geometricFiberFinite s)),
        IsNilpotent ((Tate.PrimeAdic.rationalMonodromyRepresentation s
          (geometricFiberFinite s) torsionFiniteEtale
          ((baseChange (Spec.algebraMap K L)).obj B) ℓ hu g).toLinearMap - 1)) →
    N.HasGeometricSemiabelianReduction

end Langlands.AbelianScheme
