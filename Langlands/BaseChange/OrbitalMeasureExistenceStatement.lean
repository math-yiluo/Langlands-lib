import Langlands.BaseChange.OrbitalIntegral
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Existence of the measures entering concordance

Henniart–Lemaire (2011), Chapter I, §§I.2.4–I.2.5 (printed pp. 14–17): for a nonarchimedean
local field `F`, a cyclic `F`-algebra `E` of degree `l` with generator `σ`, and Haar measures
`μF` on `GL_n(F)` and `μE` on `GL_n(E)`:

* (a) at every regular semisimple `γ` there is a right Haar measure on `G_γ(F)`, and every
  right Haar measure on `G_γ(F)` admits a quotient measure compatible with `μF`;
* (b) at every pair `(δ, γ)` with `N(δ)` conjugate to `γ` regular semisimple, every right Haar
  measure on `G_γ(F)` has an associated right Haar measure on `G^σ_δ(F)`, which admits a
  quotient measure compatible with `μE`.

This is a statement only; it is not proved here.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.JacquetLanglands

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- The measures over which `ConcordAt` and `VanishesOffNorms` quantify exist
(HL I.2.4–I.2.5, printed pp. 14–17). -/
def OrbitalMeasureExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
      (∀ γ : GeneralLinear n F, IsRegularSemisimple γ →
        (∃ μγ : Measure (glCentralizer γ), μγ.IsHaarMeasure ∧ μγ.IsMulRightInvariant) ∧
        ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant],
          ∃ νγ : Measure (LeftQuotient (glCentralizer γ)),
            IsCompatible (glCentralizer γ) μF μγ νγ) ∧
      (∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F), IsNormAssociated σ l δ γ →
        IsRegularSemisimple γ →
        ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant],
          ∃ (μδ : Measure (sigmaCentralizer σ n δ)) (_ : μδ.IsHaarMeasure)
            (_ : μδ.IsMulRightInvariant),
            IsAssociatedMeasure σ l δ γ μδ μγ ∧
              ∃ νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ)),
                IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ)

end Langlands.BaseChange
