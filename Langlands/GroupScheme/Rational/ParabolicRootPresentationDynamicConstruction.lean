import Langlands.GroupScheme.Rational.ParabolicRootPresentationExistenceReduction
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction

/-! # Actual root presentations from explicit dynamic structure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A presentation of the supplied maps, with four structural statements
retained explicitly. The simultaneous cocharacter is constructed internally. -/
def parabolicRootPresentationOfDynamicStructure
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    let := hG.isAffineHom
    ParabolicRootPresentation p l a := by
  let := hG.isAffineHom
  let χ := DynamicLeviConjugacy.parabolicLeviRealizingCocharacter hPD hGUR hG hp hl
  have hχ := DynamicLeviConjugacy.parabolicLeviRealizingCocharacter_spec hPD hGUR hG hp hl
  exact parabolicRootPresentationOfDynamicRealization
    hminimal hnegation hG hp hl ha χ hχ.1 hχ.2

/-- The exact universal existence target follows from four explicit structural
inputs, with no separate simultaneous-realization premise. -/
theorem parabolicRootPresentationExistenceStatement_of_dynamic
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u}) :
    ParabolicRootPresentationExistenceStatement.{u} := by
  intro k _ G hG P M A p l a hp hl ha
  exact ⟨parabolicRootPresentationOfDynamicStructure hminimal hnegation hPD hGUR hG hp hl ha⟩

/-- The separately owned dynamic-centralizer reductivity statement can supply
all geometric radical clauses through the published radical reduction. -/
theorem parabolicRootPresentationExistenceStatement_of_dynamic_centralizer
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hcentralizer : DynamicCentralizerReductiveStatement.{u}) :
    ParabolicRootPresentationExistenceStatement.{u} :=
  parabolicRootPresentationExistenceStatement_of_dynamic hminimal hnegation hPD
    (dynamicGeometricUnipotentRadical_of_centralizer hcentralizer)

end Langlands.GroupScheme
