import Langlands.Representation.Plancherel.StandardInductionCanonicalScalar

/-! # Rescaling the quotient measures of a canonical standard-composite scalar -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV

/-- Multiplying the two quotient measures of the actual standard integrals by
nonzero constants `c` and `d` multiplies the canonical rational scalar of their
composite by `c d`. The auxiliary Haar measures, continuations and open subsets
of the full domains for the rescaled measures are arbitrary. -/
def StandardInductionCanonicalScalarMeasureScalingStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace U₀] [BorelSpace U₀]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₀)] [BorelSpace (U₁.subgroupOf U₀)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₀)]
  [BorelSpace (QuotientSpace (U := U₁) U₀)]
  (q₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (q₀₁ : Measure (QuotientSpace (U := U₁) U₀))
  (μU₀ : Measure U₀) (μU₁ : Measure U₁)
  (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₀₁ : Measure (U₁.subgroupOf U₀))
  [IsHaarMeasure μU₀] [μU₀.Regular] [IsMulRightInvariant μU₀]
  [IsHaarMeasure μU₁] [μU₁.Regular] [IsMulRightInvariant μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  [IsHaarMeasure μI₀₁] [μI₀₁.Regular] [IsMulRightInvariant μI₀₁]
  (hq₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ q₁₀)
  (hq₀₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₀) μU₀ μI₀₁ q₀₁)
  (c d : ℝ≥0) (_hc : c ≠ 0) (_hd : d ≠ 0)
  (μU₀' : Measure U₀) (μU₁' : Measure U₁)
  (μI₁₀' : Measure (U₀.subgroupOf U₁))
  (μI₀₁' : Measure (U₁.subgroupOf U₀))
  [IsHaarMeasure μU₀'] [μU₀'.Regular] [IsMulRightInvariant μU₀']
  [IsHaarMeasure μU₁'] [μU₁'.Regular] [IsMulRightInvariant μU₁']
  [IsHaarMeasure μI₁₀'] [μI₁₀'.Regular] [IsMulRightInvariant μI₁₀']
  [IsHaarMeasure μI₀₁'] [μI₀₁'.Regular] [IsMulRightInvariant μI₀₁']
  (hq₁₀' : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁' μI₁₀' (c • q₁₀))
  (hq₀₁' : QuotientIntegration.IsCompatible (U₁.subgroupOf U₀) μU₀' μI₀₁' (d • q₀₁))
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
  (hsq₀₁ : SquaredModulusCompatibility h₁ hU₁ h₀ hU₀)

  (p : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₀ hU₀ U₁ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ h₁ hU₁
          μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A) χ)))
  (q : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₁ hU₁ U₀ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ h₀ hU₀
          μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A) χ)))
  (p' : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) (c • q₁₀) A)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₀ hU₀ U₁ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) (c • q₁₀) h₁ hU₁
          μU₁' μI₁₀' hq₁₀' hM hsq₁₀ A) χ)))
  (q' : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) (d • q₀₁) A)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₁ hU₁ U₀ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) (d • q₀₁) h₀ hU₀
          μU₀' μI₀₁' hq₀₁' hM hsq₀₁ A) χ)))
  {D₁₀ D₀₁ D₁₀' D₀₁' :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hne₁₀ : D₁₀.Nonempty)
  (hD₁₀Ω : D₁₀ ⊆ (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A))
  (hne₀₁ : D₀₁.Nonempty)
  (hD₀₁Ω : D₀₁ ⊆ (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A))
  (_hD₁₀' : IsOpen D₁₀') (hne₁₀' : D₁₀'.Nonempty)
  (hD₁₀'Ω : D₁₀' ⊆ (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) (c • q₁₀) A))
  (_hD₀₁' : IsOpen D₀₁') (hne₀₁' : D₀₁'.Nonempty)
  (hD₀₁'Ω : D₀₁' ⊆ (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) (d • q₀₁) A))
  {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hne : D.Nonempty)
  (hi : ∀ χ ∈ D,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)
,
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      (c • q₁₀) (d • q₀₁) μU₀' μU₁' μI₁₀' μI₀₁' hq₁₀' hq₀₁' hM hsq₁₀ hsq₀₁
      p' q' hne₁₀' hD₁₀'Ω hne₀₁' hD₀₁'Ω hne hi =
    algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul))
        (rationalUnramifiedFunctionField L hp hL)
        (algebraMap ℂ
          (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul))
          (((c : ℝ) : ℂ) * ((d : ℝ) : ℂ))) *
      standardInductionCompositeCanonicalRationalScalar L hp hL
        h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
        q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
        p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne hi

end Langlands.Plancherel
