import Langlands.Representation.Plancherel.StandardInductionCanonicalScalar

/-! # Conditional compact-model independence of actual canonical scalars -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV

/-- With fixed actual inducing representation, subgroup and measure data, four
independent continuations of the actual standard integrals in two compact models
give the same canonical rational scalar. One irreducibility locus is open;
a second nonempty locus may independently select the other extraction. -/
def ConditionalStandardInductionScalarCompactModelStatement : Prop :=
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
  (K₀ K₁ : OpenSubgroup G)
  (hK₀ : IsCompact (K₀ : Set G)) (hK₁ : IsCompact (K₁ : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K₀ : ∀ g : G, ∃ p : P₀, ∃ k : K₀, g = (p : G) * (k : G))
  (hP₁K₀ : ∀ g : G, ∃ p : P₁, ∃ k : K₀, g = (p : G) * (k : G))
  (hP₀K₁ : ∀ g : G, ∃ p : P₀, ∃ k : K₁, g = (p : G) * (k : G))
  (hP₁K₁ : ∀ g : G, ∃ p : P₁, ∃ k : K₁, g = (p : G) * (k : G))
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
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
  (hsq₀₁ : SquaredModulusCompatibility h₁ hU₁ h₀ hU₀)
  (p₀ : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K₀ hP₀ hK₀ hP₀K₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K₀ hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₀ hU₀ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ h₁ hU₁
        μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
  (q₀ : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K₀ hP₁ hK₀ hP₁K₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K₀ hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₁ hU₁ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ h₀ hU₀
        μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
  (p₁ : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K₁ hP₀ hK₁ hP₀K₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K₁ hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₀ hU₀ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ h₁ hU₁
        μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
  (q₁ : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K₁ hP₁ hK₁ hP₁K₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K₁ hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₁ hU₁ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ h₀ hU₀
        μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
  {D₀₁₀ D₀₀₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (_hD₀₁₀ : IsOpen D₀₁₀) (hne₀₁₀ : D₀₁₀.Nonempty)
  (hD₀₁₀Ω : D₀₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
  (_hD₀₀₁ : IsOpen D₀₀₁) (hne₀₀₁ : D₀₀₁.Nonempty)
  (hD₀₀₁Ω : D₀₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)
  {D₁₁₀ D₁₀₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (_hD₁₁₀ : IsOpen D₁₁₀) (hne₁₁₀ : D₁₁₀.Nonempty)
  (hD₁₁₀Ω : D₁₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
  (_hD₁₀₁ : IsOpen D₁₀₁) (hne₁₀₁ : D₁₀₁.Nonempty)
  (hD₁₀₁Ω : D₁₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)

  [TopologicalSpace.SeparableSpace G]
  {D₀ D₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (_hD₀ : IsOpen D₀) (hne₀ : D₀.Nonempty)
  (hi₀ : ∀ χ ∈ D₀,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)
  (hne₁ : D₁.Nonempty)
  (hi₁ : ∀ χ ∈ D₁,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)
,
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K₀ hK₀ hP₀ hP₁ hP₀K₀ hP₁K₀ hr₀ hr₁ e hν A
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      p₀ q₀ hne₀₁₀ hD₀₁₀Ω hne₀₀₁ hD₀₀₁Ω hne₀ hi₀ =
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K₁ hK₁ hP₀ hP₁ hP₀K₁ hP₁K₁ hr₀ hr₁ e hν A
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      p₁ q₁ hne₁₁₀ hD₁₁₀Ω hne₁₀₁ hD₁₀₁Ω hne₁ hi₁

end Langlands.Plancherel
