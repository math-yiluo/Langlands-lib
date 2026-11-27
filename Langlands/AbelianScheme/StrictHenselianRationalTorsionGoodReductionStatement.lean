import Langlands.AbelianScheme.RaynaudSemiabelianCriterionStatement
import Mathlib.FieldTheory.Separable

/-! # Good reduction from prime-power torsion rational over a strict henselization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AbelianScheme

/-- Let `V` be a discrete valuation ring with fraction field `K`, let `B` be an abelian
variety over `K` with Néron model `N`, and let `ℓ` be a prime invertible in `V`. Let
`V → W` be a local homomorphism to a strictly Henselian discrete valuation ring such that
the maximal ideal of `V` generates the maximal ideal of `W` and the residue extension is
separable, and let `L` be a fraction field of `W` over `K`. If, for every `ν`, every
`ℓ ^ ν`-torsion point of the base change of `B` to `L` with values in an algebraic
closure of `L` is rational over `L`, then `N` is proper with geometrically connected
fibres. -/
def StrictHenselianRationalTorsionGoodReductionStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (B : AbelianScheme (Spec (CommRingCat.of K)))
    (N : NeronModel V K B)
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Algebra V W] [IsLocalHom (algebraMap V W)],
    (maximalIdeal V).map (algebraMap V W) = maximalIdeal W →
    Algebra.IsSeparable (ResidueField V) (ResidueField W) →
    ∀ (L : Type u) [Field L] [Algebra W L] [IsFractionRing W L] [Algebra K L],
    (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) →
    ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : V) →
    (∀ ν : ℕ, HasRationalGeometricTorsion ((baseChange (Spec.algebraMap K L)).obj B) (ℓ ^ ν)) →
      IsProper N.group.X.hom ∧ GeometricallyConnected N.group.X.hom

end Langlands.AbelianScheme
