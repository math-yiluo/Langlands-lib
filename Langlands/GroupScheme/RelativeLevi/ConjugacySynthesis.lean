import Langlands.GroupScheme.RelativeLevi.LocalTorusConjugacy
import Langlands.GroupScheme.RelativeLevi.ConjugacyStatement

/-! # Relative Levi conjugacy from structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

/-- The exact relative Levi conjugacy proposition follows from the three
torus statements, relative radical uniqueness, and self-normalization. -/
theorem relativeLeviConjugacy_of_structuralStatements
    (hExist : EtaleLocalMaximalTorusExistenceStatement.{u})
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u}) :
    RelativeLeviConjugacyStatement.{u} := by
  intro S G P U L L' i r l l' hG hi hr hl hl'
  exact relative_existsUnique_conjugator_of_etaleLocal_range
    hRadical hNormalizer G P U L L' i r l l' hG hi hr hl hl'
    (etaleLocallyRangeConjugate_of_torusStatements
      hExist hConjugacy hTorusLevi i l l' hG hi hl hl')

/-- Choose the unique global radical point obtained from the supplied
structural statements, retaining its conjugacy and uniqueness certificates. -/
def relativeLeviConjugatorFromStatements
    (hExist : EtaleLocalMaximalTorusExistenceStatement.{u})
    (hConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u})
    (hTorusLevi : RelativeTorusLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u})
    {S : Scheme.{u}} (G P U L L' : GroupScheme S)
    (i : P ⟶ G) (r : U ⟶ P) (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l)
    (hl' : IsRelativeLeviSubgroup l') :
    {n : Over.mk (𝟙 S) ⟶ U.X //
      (SubgroupFunctor.range l' =
        SubgroupFunctor.range (l ≫ (P.innerIso (n ≫ r.hom.hom)).hom)) ∧
      ∀ n' : Over.mk (𝟙 S) ⟶ U.X,
        SubgroupFunctor.range l' =
          SubgroupFunctor.range (l ≫ (P.innerIso (n' ≫ r.hom.hom)).hom) →
        n' = n} := by
  have h := relativeLeviConjugacy_of_structuralStatements
    hExist hConjugacy hTorusLevi hRadical hNormalizer
    S G P U L L' i r l l' hG hi hr hl hl'
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.GroupScheme.RelativeLevi
