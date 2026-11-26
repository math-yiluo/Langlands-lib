import Langlands.BaseChange.WeylIntegrationData

/-!
# The ordinary Weyl integration formula for `GL_n`

The ordinary Weyl integration formula over a nonarchimedean local field,
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), II.2.10, formula (2), stated as a decomposition
of Haar integrals of integrable functions.
-/

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula
open scoped Classical

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- The ordinary Weyl decomposition of Haar integrals on `GL_n(F)`, for an arbitrary
set of representatives of conjugacy classes of rational maximal tori and arbitrary
Haar measures on them. The centralizer and quotient measures are fixed for all
integrable inputs. -/
def WeylIntegrationFormulaStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
    (S : Set (WeylTorus F n)), WeylTorus.IsRepresentativeSet S →
    ∀ (μT : ∀ T : S, Measure T.val.val), (∀ T : S, (μT T).IsHaarMeasure) →
      (∀ T : S, Finite T.val.RationalWeylGroup) ∧
      ∃ (μC : ∀ (T : S) (γ : T.val.regularPoints),
          Measure (glCentralizer γ.val.val))
        (ν : ∀ (T : S) (γ : T.val.regularPoints),
          Measure (LeftQuotient (glCentralizer γ.val.val))),
        (∀ (T : S) (γ : T.val.regularPoints),
          ∃ (_ : (μC T γ).IsHaarMeasure) (_ : (μC T γ).IsMulRightInvariant),
            Measure.map Subtype.val (μC T γ) = Measure.map Subtype.val (μT T) ∧
            IsCompatible (glCentralizer γ.val.val) μF (μC T γ) (ν T γ)) ∧
        ∀ f : GeneralLinear n F → ℂ, Integrable f μF →
          (∀ T : S, ∀ᵐ γ ∂μT T, ∀ h : γ ∈ T.val.regularPoints,
            Integrable
              (twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) γ.val f)
              (ν T ⟨γ, h⟩)) ∧
          let integrand (T : S) (γ : T.val.val) : ℂ :=
            if h : γ ∈ T.val.regularPoints then
              (T.val.integrationWeight γ : ℂ) * orbitalIntegral γ.val (ν T ⟨γ, h⟩) f
            else 0
          (∀ T : S, Integrable (integrand T) (μT T)) ∧
          Summable (fun T : S => ∫ γ, ‖integrand T γ‖ ∂μT T) ∧
          (∫ g, f g ∂μF) = ∑' T : S, ∫ γ, integrand T γ ∂μT T

end Langlands.BaseChange
