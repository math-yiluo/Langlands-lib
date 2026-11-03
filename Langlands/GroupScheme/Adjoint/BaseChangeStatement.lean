import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Statement: field base change of actual adjoint quotients -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Extension of the base field preserves the actual adjoint-quotient interface: the
base change of an adjoint quotient `q : G ⟶ A` along `Spec K ⟶ Spec k` is again an
adjoint quotient of `G_K` (Milne 17.62–17.63 and 19.5, 19.13; CGP A.1.8–A.1.12). -/
def AdjointQuotientBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G A : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ A),
    IsAdjointQuotient q →
      IsAdjointQuotient ((GroupScheme.baseChange (algebraBaseMap k K)).map q)

namespace AdjointQuotientBaseChangeStatement

variable (h : AdjointQuotientBaseChangeStatement.{u})
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {G A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A}
include h

/-- The base-changed quotient homomorphism satisfies the full interface. -/
theorem isAdjointQuotient (hq : IsAdjointQuotient q) :
    IsAdjointQuotient ((GroupScheme.baseChange (algebraBaseMap k K)).map q) :=
  h k K G A q hq

/-- The existing canonical comparison from the base-changed quotient to any supplied
adjoint quotient of `G_K`. -/
def quotientIso (hq : IsAdjointQuotient q)
    {A' : GroupScheme (Spec (CommRingCat.of K))}
    {q' : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ A'}
    (hq' : IsAdjointQuotient q') :
    (GroupScheme.baseChange (algebraBaseMap k K)).obj A ≅ A' :=
  (h.isAdjointQuotient hq).quotientIso hq'

/-- The comparison commutes with the actual maps from `G_K`. -/
theorem comp_quotientIso_hom (hq : IsAdjointQuotient q)
    {A' : GroupScheme (Spec (CommRingCat.of K))}
    {q' : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ A'}
    (hq' : IsAdjointQuotient q') :
    (GroupScheme.baseChange (algebraBaseMap k K)).map q ≫ (h.quotientIso hq hq').hom = q' :=
  (h.isAdjointQuotient hq).comp_quotientIso_hom hq'

/-- The comparison interface also named `comparisonIso`. -/
abbrev comparisonIso (hq : IsAdjointQuotient q)
    {A' : GroupScheme (Spec (CommRingCat.of K))}
    {q' : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ A'}
    (hq' : IsAdjointQuotient q') :
    (GroupScheme.baseChange (algebraBaseMap k K)).obj A ≅ A' :=
  h.quotientIso hq hq'

/-- The comparison commutes with the base-changed quotient map. -/
theorem comp_comparisonIso_hom (hq : IsAdjointQuotient q)
    {A' : GroupScheme (Spec (CommRingCat.of K))}
    {q' : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ A'}
    (hq' : IsAdjointQuotient q') :
    (GroupScheme.baseChange (algebraBaseMap k K)).map q ≫
      (h.comparisonIso hq hq').hom = q' :=
  h.comp_quotientIso_hom hq hq'

end AdjointQuotientBaseChangeStatement
end Langlands.GroupScheme
