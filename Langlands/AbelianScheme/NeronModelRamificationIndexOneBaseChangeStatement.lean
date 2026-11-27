import Langlands.AbelianScheme.NeronModel
import Mathlib.FieldTheory.Separable

/-! # Néron models and extensions of ramification index one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AbelianScheme

/-- Néron models of abelian varieties are compatible with extensions of discrete valuation
rings of ramification index one. Let `V → W` be a local homomorphism of discrete valuation
rings with fraction fields `K` and `L`, such that the maximal ideal of `V` generates the
maximal ideal of `W` and the residue field of `W` is separable over that of `V`. For every
Néron model `N` over `V` of an abelian variety over `K`, the base change of `N` to `W` is a
Néron model over `W` of its generic fibre: it is smooth, separated and quasi-compact of
finite type over `W` and has the Néron mapping property for smooth `W`-schemes. -/
def NeronModelRamificationIndexOneBaseChangeStatement : Prop :=
  ∀ (V K W L : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V W] [IsLocalHom (algebraMap V W)],
    (maximalIdeal V).map (algebraMap V W) = maximalIdeal W →
    Algebra.IsSeparable (ResidueField V) (ResidueField W) →
    ∀ (B : AbelianScheme (Spec (.of K))) (N : NeronModel V K B),
      NeronModelInfra.NeronModelPropertyBundle W L
        ((CommGroupScheme.baseChange (Spec.algebraMap V W)).obj N.group).X.hom

end Langlands.AbelianScheme
