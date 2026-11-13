import Langlands.Geometry.Building.IntegerOmegaApartmentRigidity
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Uniqueness of integer-valued omega-compatible apartment classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuation

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {D E : KPApartmentData i (order v)} {C : CentralizerDatum i}

/-- Full integer-valued V 6 identifies apartment classes for the same actual
maximal split torus and actual centralizer, over an arbitrary field. -/
theorem IsOmegaCompatible.eq_of_isMaximalSplitTorus
    (hD : IsOmegaCompatible v D C) (hE : IsOmegaCompatible v E C)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    D = E := by
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization.{u} k G hG S i hi
  have hpair : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha x hx hx1 => (hrank a ha x hx hx1).1.exists
  exact hD.eq_of_hasOppositeFactorPairs hE hG hi hpair

end IntegerValuation

/-- The uniqueness conclusion of KP Proposition 6.2.6 for an integer-valued
valuation on an arbitrary field, with no opposite-pair premise. -/
def IntegerOmegaCompatibleApartmentUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G)
      [Mono i.hom.hom.left],
      IsMaximalSplitTorus i →
      ∀ (C : CentralizerDatum i)
        (D E : KPApartmentData i (IntegerValuation.order v)),
        IntegerValuation.IsOmegaCompatible v D C →
        IntegerValuation.IsOmegaCompatible v E C → D = E

/-- Full integer-valued omega-compatible apartment classes are unique in every
universe. The actual opposite pairs come from rational rank-one factorization. -/
theorem integerOmegaCompatibleApartmentUniqueness :
    IntegerOmegaCompatibleApartmentUniquenessStatement.{u} := by
  intro k _ v G _ hG S i _ hi C D E hD hE
  exact hD.eq_of_isMaximalSplitTorus hE hG hi

end Langlands.Geometry.Building
