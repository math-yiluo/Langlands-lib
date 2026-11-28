import Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement

/-! # Trace class on the discrete automorphic spectrum of `GL_n` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

private local instance (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- The `GL_n` case of discrete trace class (Getz–Hahn, Theorem 9.1.4) on the
canonical positive split-centre quotient, for every smooth compactly supported adelic test. -/
def GeneralLinearDiscreteTraceClassStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ (hG : IsConnectedReductive GLₙ) (f : AdelicGroupPoints F GLₙ → ℂ),
      IsAdelicTestFunction F GLₙ f →
      ∀ hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F GLₙ)),
        IsTraceClass (canonicalDiscreteIntegratedAction F GLₙ hG f hf)

end Langlands.TraceFormula
