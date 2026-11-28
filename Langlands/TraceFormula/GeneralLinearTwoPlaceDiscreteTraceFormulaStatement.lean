import Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement
import Langlands.TraceFormula.SingleOrbitSimpleTrace

/-!
# The simple discrete trace formula at two finite places for `GL_n`

This is the norm-one formulation of Arthur's *The invariant trace formula II. Global theory*,
Corollary 7.5 (printed p. 541), with regular elliptic support as the local cuspidality condition
and trace class as a hypothesis. The paired Markdown gives the source and the passage from
Hecke functions to smooth adelic test functions.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.JacquetLanglands Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

private local instance (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- For a smooth compactly supported adelic test on `GL_n` with regular elliptic support at
two distinct finite places, assume that the integrated action on the discrete spectrum is
trace class. Its trace has a finite geometric expansion for the canonical norm-one average.
The rational representatives are regular elliptic, pairwise nonconjugate over `F`, and cover
every rational class with a nonzero orbit function. -/
def GeneralLinearTwoPlaceDiscreteTraceFormulaStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ (hG : IsConnectedReductive GLₙ) (p₁ p₂ : Langlands.Global.FinitePlace F), p₁ ≠ p₂ →
    ∀ (f : AdelicGroupPoints F GLₙ → ℂ), IsAdelicTestFunction F GLₙ f →
    (∀ g ∈ tsupport f,
      IsRegularElliptic (FiniteAdelicGL.localProjection F n p₁
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n g))) ∧
      IsRegularElliptic (FiniteAdelicGL.localProjection F n p₂
        (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n g)))) →
    ∀ hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F GLₙ)),
      IsTraceClass (canonicalDiscreteIntegratedAction F GLₙ hG f hf) →
    let H := normOneSubgroup F GLₙ
    let Γ := rationalNormOneSubgroup F GLₙ
    let fOne := canonicalNormOneAverage F GLₙ hG f
    ∃ (m : ℕ) (r : Fin m → RationalGroupPoints F GLₙ),
      let q : Fin m → Γ := fun j => ⟨rationalNormOne F GLₙ (r j), ⟨r j, rfl⟩⟩
      (∀ j, IsRegularElliptic (GeneralLinearGroupPoints.rationalEquiv F n (r j))) ∧
      (∀ j k, IsTwistedConjugate Γ (MonoidHom.id H) (q j : H) (q k : H) → j = k) ∧
      (∀ δ : Γ, (∃ x : H, fOne (x⁻¹ * (δ : H) * x) ≠ 0) →
        ∃ j, IsTwistedConjugate Γ (MonoidHom.id H) (q j : H) (δ : H)) ∧
      SimpleTraceGeometricExpansion Γ (MonoidHom.id H) (Measure.haar : Measure H) fOne
        (operatorTrace (canonicalDiscreteIntegratedAction F GLₙ hG f hf)) q

end Langlands.TraceFormula
