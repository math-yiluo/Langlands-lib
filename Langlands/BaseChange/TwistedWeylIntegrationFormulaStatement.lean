import Langlands.BaseChange.WeylIntegrationData

/-!
# The cyclically twisted Weyl integration formula for `GL_n`

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), II.2.10, formula (1) (printed pp. 70–72): the
decomposition of Haar integrals on `GL_n(E)`, for a cyclic algebra `(E, σ, l)` over a
nonarchimedean local field `F`, into σ-orbital integrals over the regular norm images
of representatives of the rational maximal tori. The quotient `T(E)^{σ-1} \ T(E)` of
the source is replaced by its image under the norm in `T(F)`, with the restriction of
the rational torus Haar measure. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula
open scoped Classical

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- The cyclically twisted Weyl decomposition of Haar integrals on `GL_n(E)` for a
cyclic algebra `(E, σ, l)` over a nonarchimedean local field `F`
(Henniart–Lemaire 2011, II.2.10, formula (1)).

Fix a Haar measure `μE` on `GL_n(E)`, a set `S` of representatives of the rational
maximal tori, Haar measures `μT T` on their rational points, and right Haar measures
`μC T γ` on the centralizers of their regular points having the same images in
`GL_n(F)` as `μT T`. Then there are lifts `lift T γ ∈ T(E)` of the regular points `γ`
of the norm image, with `N(lift T γ) = γ`, right Haar measures `μD T γ` on their
σ-centralizers associated to `μC T γ`, and quotient measures `ν T γ` compatible with
`μE` and `μD T γ`, all fixed for every input, such that for each `μE`-integrable `φ`
the σ-orbit functions are integrable at almost every regular norm-image point, each
torus integrand `integrationWeight γ · Λ_σ(φ, lift T γ)`, extended by zero off the
regular norm image, is `μT T`-integrable, their L¹ norms are summable over `S`, and
their integrals sum to the integral of `φ`. -/
def TwistedWeylIntegrationFormulaStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type v) [CommRing E] [Algebra F E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)],
    IsCyclicAlgebra σ l →
    ∀ (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (S : Set (WeylTorus F n)), WeylTorus.IsRepresentativeSet S →
    ∀ (μT : ∀ T : S, Measure T.val.val), (∀ T : S, (μT T).IsHaarMeasure) →
    ∀ (μC : ∀ (T : S) (γ : T.val.regularPoints), Measure (glCentralizer γ.val.val)),
      (∀ (T : S) (γ : T.val.regularPoints),
        (μC T γ).IsHaarMeasure ∧ (μC T γ).IsMulRightInvariant ∧
          Measure.map Subtype.val (μC T γ) = Measure.map Subtype.val (μT T)) →
      ∃ (lift : ∀ T : S, (T.val.regularPoints ∩ T.val.normImage σ l : Set T.val.val) →
            T.val.points E)
        (μD : ∀ (T : S) (γ : (T.val.regularPoints ∩ T.val.normImage σ l : Set T.val.val)),
          Measure (sigmaCentralizer σ n (lift T γ).val))
        (ν : ∀ (T : S) (γ : (T.val.regularPoints ∩ T.val.normImage σ l : Set T.val.val)),
          Measure (LeftQuotient (sigmaCentralizer σ n (lift T γ).val))),
        (∀ (T : S) (γ : (T.val.regularPoints ∩ T.val.normImage σ l : Set T.val.val)),
          cyclicNorm σ l (lift T γ).val = baseChange F E n γ.val.val ∧
          ∃ (_ : (μD T γ).IsHaarMeasure) (_ : (μD T γ).IsMulRightInvariant),
            IsAssociatedMeasure σ l (lift T γ).val γ.val.val (μD T γ)
                (μC T ⟨γ.val, γ.property.1⟩) ∧
              IsCompatible (sigmaCentralizer σ n (lift T γ).val) μE (μD T γ) (ν T γ)) ∧
        ∀ φ : GeneralLinear n E → ℂ, Integrable φ μE →
          (∀ T : S, ∀ᵐ γ ∂μT T, ∀ h : γ ∈ T.val.regularPoints ∩ T.val.normImage σ l,
            Integrable (twistedOrbitFunction (entrywiseAut σ n) (lift T ⟨γ, h⟩).val φ)
              (ν T ⟨γ, h⟩)) ∧
          let integrand (T : S) (γ : T.val.val) : ℂ :=
            if h : γ ∈ T.val.regularPoints ∩ T.val.normImage σ l then
              (T.val.integrationWeight γ : ℂ) *
                sigmaOrbitalIntegral σ n (lift T ⟨γ, h⟩).val (ν T ⟨γ, h⟩) φ
            else 0
          (∀ T : S, Integrable (integrand T) (μT T)) ∧
          Summable (fun T : S => ∫ γ, ‖integrand T γ‖ ∂μT T) ∧
          (∫ g, φ g ∂μE) = ∑' T : S, ∫ γ, integrand T γ ∂μT T

end Langlands.BaseChange
