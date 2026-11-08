import Langlands.Representation.Plancherel.StandardInductionCanonicalScalar

/-! # Conditional representative independence of actual canonical scalars -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV uW

/-- For equivalent canonical inducing representations with fixed subgroup,
compact-model and measure data, four independent continuations of the actual
standard integrals give the same canonical rational scalar. The first
representative has an open generic irreducibility locus; the second only
needs a nonempty irreducibility locus to define its canonical extraction. -/
def ConditionalStandardInductionScalarRepresentativeStatement : Prop :=
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
  (B : Langlands.SmoothRep.{0, uG, uW} ℂ M)
  (_φ : A.representation.Equiv B.representation)
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
  (pA : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₀ hU₀ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ h₁ hU₁
        μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A χ)))
  (qA : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) A
      (standardInductionIntertwinerFamily h₁ hU₁ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ h₀ hU₀
        μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A χ)))
  (pB : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ B)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) B
      (standardInductionIntertwinerFamily h₀ hU₀ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ h₁ hU₁
        μU₁ μI₁₀ hq₁₀ hM hsq₁₀ B χ)))
  (qB : RationalOperatorContinuationData
    (standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ B)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
        χ.val) B
      (standardInductionIntertwinerFamily h₁ hU₁ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ h₀ hU₀
        μU₀ μI₀₁ hq₀₁ hM hsq₀₁ B χ)))
  {DA₁₀ DA₀₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (_hDA₁₀ : IsOpen DA₁₀) (hneA₁₀ : DA₁₀.Nonempty)
  (hDA₁₀Ω : DA₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
  (_hDA₀₁ : IsOpen DA₀₁) (hneA₀₁ : DA₀₁.Nonempty)
  (hDA₀₁Ω : DA₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)
  {DB₁₀ DB₀₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (_hDB₁₀ : IsOpen DB₁₀) (hneB₁₀ : DB₁₀.Nonempty)
  (hDB₁₀Ω : DB₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ B)
  (_hDB₀₁ : IsOpen DB₀₁) (hneB₀₁ : DB₀₁.Nonempty)
  (hDB₀₁Ω : DB₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ B)

  [TopologicalSpace.SeparableSpace G]
  {DA DB : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (_hDA : IsOpen DA) (hneA : DA.Nonempty)
  (hiA : ∀ χ ∈ DA,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)
  (hneB : DB.Nonempty)
  (hiB : ∀ χ ∈ DB,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      B).IsIrreducible)
,
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      pA qA hneA₁₀ hDA₁₀Ω hneA₀₁ hDA₀₁Ω hneA hiA =
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν B
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      pB qB hneB₁₀ hDB₁₀Ω hneB₀₁ hDB₀₁Ω hneB hiB

end Langlands.Plancherel
