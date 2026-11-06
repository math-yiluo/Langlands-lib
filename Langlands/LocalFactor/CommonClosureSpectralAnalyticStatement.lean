import Langlands.LocalFactor.CommonClosureSpectral
import Mathlib.Analysis.Analytic.Basic

/-!
# Analyticity of ordinary common-closure local constants

This is a proposition about every supplied local-constant system on the actual
continuous exact virtual groups, over every intermediate field. It asserts no
system existence and supplies no analyticity proof.
-/

universe uF uV

namespace Langlands.LocalFactor

open CommonClosure CommonClosureSpectral

/-- Analyticity of the ordinary Deligne spectral value for every actual
intermediate field and exact virtual class. This is the analytic consequence of
Tate (3.4.2) and (3.4.5), with all system and harmonic inputs retained. -/
def CommonClosureSpectralAnalyticStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (x : Virtual.{uF, uV} F E) (s : ℂ),
    AnalyticAt ℂ (fun z : ℂ =>
      (conditionalDeligneValue F e ε hε E ψ μ x z : ℂ)) s

end Langlands.LocalFactor
