import Langlands.Representation.Plancherel.ContinuedParabolicCompositionScalar
import Langlands.Representation.Plancherel.StandardInductionCanonicalScalar

/-! # Equal canonical opposite scalars for two parabolics with one Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV

section Composition

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ P₂ M U₀ U₁ U₂ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (h₂ : IsSemidirectDecomposition P₂ M U₂) (hU₂ : IsClosed (U₂ : Set G))
  (hδ₂ : IsUnimodularModulus U₂ hU₂)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G))
  (hP₁ : IsClosed (P₁ : Set G))
  (hP₂ : IsClosed (P₂ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hP₂K : ∀ g : G, ∃ p : P₂, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection)
  (hr₁ : Continuous h₁.projection)
  (hr₂ : Continuous h₂.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  {Ω₁₀ Ω₂₁ Ω₂₀ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}

/-- The actual family `J₂₀` is the composite `J₂₁ ∘ J₁₀` on a nonempty open
set of parameters contained in the three regions. -/
def HasOpenInductionComposition
    (J₁₀ : ∀ χ : Ω₁₀,
        (UnramifiedLeviInduction h₀ hU₀
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₁ hU₁
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation)
    (J₂₁ : ∀ χ : Ω₂₁,
        (UnramifiedLeviInduction h₁ hU₁
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₂ hU₂
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation)
    (J₂₀ : ∀ χ : Ω₂₀,
        (UnramifiedLeviInduction h₀ hU₀
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₂ hU₂
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation) : Prop :=
  ∃ D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)),
    IsOpen D ∧ D.Nonempty ∧ ∃ (hD₁₀ : D ⊆ Ω₁₀) (hD₂₁ : D ⊆ Ω₂₁) (hD₂₀ : D ⊆ Ω₂₀),
      ∀ χ (hχ : χ ∈ D), J₂₀ ⟨χ, hD₂₀ hχ⟩ = (J₂₁ ⟨χ, hD₂₁ hχ⟩).comp (J₁₀ ⟨χ, hD₁₀ hχ⟩)

/-- An actual composition on an open set is a composition of the fixed
compact-picture conjugates on the same open set. -/
theorem HasOpenInductionComposition.compact
    {J₁₀ : ∀ χ : Ω₁₀,
        (UnramifiedLeviInduction h₀ hU₀
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₁ hU₁
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation}
    {J₂₁ : ∀ χ : Ω₂₁,
        (UnramifiedLeviInduction h₁ hU₁
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₂ hU₂
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation}
    {J₂₀ : ∀ χ : Ω₂₀,
        (UnramifiedLeviInduction h₀ hU₀
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₂ hU₂
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A).representation}
    (h : HasOpenInductionComposition L h₀ hU₀ h₁ hU₁ h₂ hU₂ e A J₁₀ J₂₁ J₂₀) :
    HasOpenComposition
      (fun χ : Ω₁₀ =>
        compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
          h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A (J₁₀ χ))
      (fun χ : Ω₂₁ =>
        compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
          h₂ hU₂ hδ₂ hP₂ hP₂K hr₂
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A (J₂₁ χ))
      (fun χ : Ω₂₀ =>
        compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
          (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
          (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
          h₂ hU₂ hδ₂ hP₂ hP₂K hr₂
          (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
          A (J₂₀ χ)) := by
  obtain ⟨D, hD, hne, hD₁₀, hD₂₁, hD₂₀, he⟩ := h
  refine ⟨D, hD, hne, hD₁₀, hD₂₁, hD₂₀, fun χ hχ => ?_⟩
  beta_reduce
  rw [he χ hχ]
  exact compactIntertwiningOperator_comp h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁
    hP₀K hP₁K hr₀ hr₁ _ (fun ψ => (hν ψ).comp e.symm.continuous) _ A
    h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ _ _

end Composition

section Canonical

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  [TopologicalSpace.SeparableSpace G]
  {P₀ P₁ P₂ P₃ M U₀ U₁ U₂ U₃ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (h₂ : IsSemidirectDecomposition P₂ M U₂) (hU₂ : IsClosed (U₂ : Set G))
  (hδ₂ : IsUnimodularModulus U₂ hU₂)
  (h₃ : IsSemidirectDecomposition P₃ M U₃) (hU₃ : IsClosed (U₃ : Set G))
  (hδ₃ : IsUnimodularModulus U₃ hU₃)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G))
  (hP₁ : IsClosed (P₁ : Set G))
  (hP₂ : IsClosed (P₂ : Set G))
  (hP₃ : IsClosed (P₃ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hP₂K : ∀ g : G, ∃ p : P₂, ∃ k : K, g = (p : G) * (k : G))
  (hP₃K : ∀ g : G, ∃ p : P₃, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection)
  (hr₁ : Continuous h₁.projection)
  (hr₂ : Continuous h₂.projection)
  (hr₃ : Continuous h₃.projection)
  (e : GroupScheme.rationalPoints L ≃ₜ* M)
  (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace U₀] [BorelSpace U₀]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace U₃] [BorelSpace U₃]
  [MeasurableSpace (U₀.subgroupOf U₃)] [BorelSpace (U₀.subgroupOf U₃)]
  [MeasurableSpace (U₃.subgroupOf U₀)] [BorelSpace (U₃.subgroupOf U₀)]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₂.subgroupOf U₁)] [BorelSpace (U₂.subgroupOf U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₃)]
  [BorelSpace (QuotientSpace (U := U₀) U₃)]
  [MeasurableSpace (QuotientSpace (U := U₃) U₀)]
  [BorelSpace (QuotientSpace (U := U₃) U₀)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [BorelSpace (QuotientSpace (U := U₁) U₂)]
  [MeasurableSpace (QuotientSpace (U := U₂) U₁)]
  [BorelSpace (QuotientSpace (U := U₂) U₁)]
  (q₃₀ : Measure (QuotientSpace (U := U₀) U₃))
  (q₀₃ : Measure (QuotientSpace (U := U₃) U₀))
  (q₂₁ : Measure (QuotientSpace (U := U₁) U₂))
  (q₁₂ : Measure (QuotientSpace (U := U₂) U₁))
  (μU₀ : Measure U₀)
  (μU₁ : Measure U₁)
  (μU₂ : Measure U₂)
  (μU₃ : Measure U₃)
  (μI₃₀ : Measure (U₀.subgroupOf U₃))
  (μI₀₃ : Measure (U₃.subgroupOf U₀))
  (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μI₁₂ : Measure (U₂.subgroupOf U₁))
  [IsHaarMeasure μU₀] [μU₀.Regular] [IsMulRightInvariant μU₀]
  [IsHaarMeasure μU₁] [μU₁.Regular] [IsMulRightInvariant μU₁]
  [IsHaarMeasure μU₂] [μU₂.Regular] [IsMulRightInvariant μU₂]
  [IsHaarMeasure μU₃] [μU₃.Regular] [IsMulRightInvariant μU₃]
  [IsHaarMeasure μI₃₀] [μI₃₀.Regular] [IsMulRightInvariant μI₃₀]
  [IsHaarMeasure μI₀₃] [μI₀₃.Regular] [IsMulRightInvariant μI₀₃]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁]
  [IsHaarMeasure μI₁₂] [μI₁₂.Regular] [IsMulRightInvariant μI₁₂]
  (hq₃₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₃)
    μU₃ μI₃₀ q₃₀)
  (hq₀₃ : QuotientIntegration.IsCompatible (U₃.subgroupOf U₀)
    μU₀ μI₀₃ q₀₃)
  (hq₂₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₂)
    μU₂ μI₂₁ q₂₁)
  (hq₁₂ : QuotientIntegration.IsCompatible (U₂.subgroupOf U₁)
    μU₁ μI₁₂ q₁₂)
  (hM : IsClosed (M : Set G))
  (hsq₃₀ : SquaredModulusCompatibility h₀ hU₀ h₃ hU₃)
  (hsq₀₃ : SquaredModulusCompatibility h₃ hU₃ h₀ hU₀)
  (hsq₂₁ : SquaredModulusCompatibility h₁ hU₁ h₂ hU₂)
  (hsq₁₂ : SquaredModulusCompatibility h₂ hU₂ h₁ hU₁)

variable
  (p₃₀ : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₀ hU₀ U₃ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₃₀ A)
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
        h₃ hU₃ hδ₃ hP₃ hP₃K hr₃
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₀ hU₀ U₃ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) q₃₀ h₃ hU₃
          μU₃ μI₃₀ hq₃₀ hM hsq₃₀ A) χ)))
  (p₀₃ : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₃ hU₃ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₃ A)
    (fun χ => compactIntertwiningOperator h₃ hU₃ hδ₃ K hP₃ hK hP₃K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₃
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₃ hU₃ U₀ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₃ h₀ hU₀
          μU₀ μI₀₃ hq₀₃ hM hsq₀₃ A) χ)))
  (p₂₁ : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₁ hU₁ U₂ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₂₁ A)
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
        h₂ hU₂ hδ₂ hP₂ hP₂K hr₂
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₁ hU₁ U₂ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) q₂₁ h₂ hU₂
          μU₂ μI₂₁ hq₂₁ hM hsq₂₁ A) χ)))
  (p₁₂ : RationalOperatorContinuationData (standardIntertwiningFullDomainRegion h₂ hU₂ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₂ A)
    (fun χ => compactIntertwiningOperator h₂ hU₂ hδ₂ K hP₂ hK hP₂K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₂
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A ((standardInductionIntertwinerFamily h₂ hU₂ U₁ e
          (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₂ h₁ hU₁
          μU₁ μI₁₂ hq₁₂ hM hsq₁₂ A) χ)))
  {D₃₀ D₀₃ D₂₁ D₁₂ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD₃₀ : IsOpen D₃₀) (hne₃₀ : D₃₀.Nonempty)
  (hD₃₀Ω : D₃₀ ⊆ (standardIntertwiningFullDomainRegion h₀ hU₀ U₃ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₃₀ A))
  (hD₀₃ : IsOpen D₀₃) (hne₀₃ : D₀₃.Nonempty)
  (hD₀₃Ω : D₀₃ ⊆ (standardIntertwiningFullDomainRegion h₃ hU₃ U₀ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₃ A))
  (hD₂₁ : IsOpen D₂₁) (hne₂₁ : D₂₁.Nonempty)
  (hD₂₁Ω : D₂₁ ⊆ (standardIntertwiningFullDomainRegion h₁ hU₁ U₂ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₂₁ A))
  (hD₁₂ : IsOpen D₁₂) (hne₁₂ : D₁₂.Nonempty)
  (hD₁₂Ω : D₁₂ ⊆ (standardIntertwiningFullDomainRegion h₂ hU₂ U₁ e
      (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₂ A))
  {D D' : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ χ ∈ D,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)
  (hD' : IsOpen D') (hne' : D'.Nonempty)
  (hi' : ∀ χ ∈ D',
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)
  {Ω₁₀ Ω₀₂ Ω₂₃ Ω₃₁ Ω₀₁ Ω₁₃ Ω₃₂ Ω₂₀ :
    Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (J₁₀ : ∀ χ : Ω₁₀,
      (UnramifiedLeviInduction h₀ hU₀
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (J₀₂ : ∀ χ : Ω₀₂,
      (UnramifiedLeviInduction h₂ hU₂
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (J₂₃ : ∀ χ : Ω₂₃,
      (UnramifiedLeviInduction h₃ hU₃
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₂ hU₂
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (J₃₁ : ∀ χ : Ω₃₁,
      (UnramifiedLeviInduction h₁ hU₁
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₃ hU₃
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (J₀₁ : ∀ χ : Ω₀₁,
      (UnramifiedLeviInduction h₁ hU₁
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (J₁₃ : ∀ χ : Ω₁₃,
      (UnramifiedLeviInduction h₃ hU₃
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (J₃₂ : ∀ χ : Ω₃₂,
      (UnramifiedLeviInduction h₂ hU₂
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₃ hU₃
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (J₂₀ : ∀ χ : Ω₂₀,
      (UnramifiedLeviInduction h₀ hU₀
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₂ hU₂
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A).representation)
  (p₁₀ : RationalOperatorContinuationData Ω₁₀
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₁₀ χ)))
  (p₀₂ : RationalOperatorContinuationData Ω₀₂
    (fun χ => compactIntertwiningOperator h₂ hU₂ hδ₂ K hP₂ hK hP₂K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₂
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₀₂ χ)))
  (p₂₃ : RationalOperatorContinuationData Ω₂₃
    (fun χ => compactIntertwiningOperator h₃ hU₃ hδ₃ K hP₃ hK hP₃K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₃
        h₂ hU₂ hδ₂ hP₂ hP₂K hr₂
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₂₃ χ)))
  (p₃₁ : RationalOperatorContinuationData Ω₃₁
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
        h₃ hU₃ hδ₃ hP₃ hP₃K hr₃
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₃₁ χ)))
  (p₀₁ : RationalOperatorContinuationData Ω₀₁
    (fun χ => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
        h₀ hU₀ hδ₀ hP₀ hP₀K hr₀
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₀₁ χ)))
  (p₁₃ : RationalOperatorContinuationData Ω₁₃
    (fun χ => compactIntertwiningOperator h₃ hU₃ hδ₃ K hP₃ hK hP₃K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₃
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₁₃ χ)))
  (p₃₂ : RationalOperatorContinuationData Ω₃₂
    (fun χ => compactIntertwiningOperator h₂ hU₂ hδ₂ K hP₂ hK hP₂K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₂
        h₃ hU₃ hδ₃ hP₃ hP₃K hr₃
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₃₂ χ)))
  (p₂₀ : RationalOperatorContinuationData Ω₂₀
    (fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
        (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
        (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
        h₂ hU₂ hδ₂ hP₂ hP₂K hr₂
        (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ.val)
        A (J₂₀ χ)))

include p₁₀ p₀₂ p₂₃ p₃₁ p₀₁ p₁₃ p₃₂ p₂₀ hD₃₀ hD₀₃ hD₂₁ hD₁₂ hD hD'

/-- The canonical scalar of the actual standard composite for the pair
`(P₁, P₂)` equals the one for `(P₀, P₃)`. Here `P₀, P₁, P₂, P₃` play the roles
of `P`, `P'`, `P̄'`, `P̄`, the opposite pairs carry their standard integral
families, and the eight cross families are arbitrary actual intertwiners with
continuations. The eight composition identities hold on open sets. -/
theorem standardInductionCompositeCanonicalRationalScalar_eq_of_parabolicComposition
    (h₁₂ : HasOpenInductionComposition L h₂ hU₂ h₀ hU₀ h₁ hU₁ e A
      J₀₂ J₁₀
      (standardInductionIntertwinerFamily h₂ hU₂ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₂ h₁ hU₁
        μU₁ μI₁₂ hq₁₂ hM hsq₁₂ A))
    (h₂₁ : HasOpenInductionComposition L h₁ hU₁ h₃ hU₃ h₂ hU₂ e A
      J₃₁ J₂₃
      (standardInductionIntertwinerFamily h₁ hU₁ U₂ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₂₁ h₂ hU₂
        μU₂ μI₂₁ hq₂₁ hM hsq₂₁ A))
    (h₀₃ : HasOpenInductionComposition L h₃ hU₃ h₂ hU₂ h₀ hU₀ e A
      J₂₃ J₀₂
      (standardInductionIntertwinerFamily h₃ hU₃ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₃ h₀ hU₀
        μU₀ μI₀₃ hq₀₃ hM hsq₀₃ A))
    (h₃₀ : HasOpenInductionComposition L h₀ hU₀ h₁ hU₁ h₃ hU₃ e A
      J₁₀ J₃₁
      (standardInductionIntertwinerFamily h₀ hU₀ U₃ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₃₀ h₃ hU₃
        μU₃ μI₃₀ hq₃₀ hM hsq₃₀ A))
    (h₀₃' : HasOpenInductionComposition L h₃ hU₃ h₁ hU₁ h₀ hU₀ e A
      J₁₃ J₀₁
      (standardInductionIntertwinerFamily h₃ hU₃ U₀ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₃ h₀ hU₀
        μU₀ μI₀₃ hq₀₃ hM hsq₀₃ A))
    (h₃₀' : HasOpenInductionComposition L h₀ hU₀ h₂ hU₂ h₃ hU₃ e A
      J₂₀ J₃₂
      (standardInductionIntertwinerFamily h₀ hU₀ U₃ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₃₀ h₃ hU₃
        μU₃ μI₃₀ hq₃₀ hM hsq₃₀ A))
    (h₁₂' : HasOpenInductionComposition L h₂ hU₂ h₃ hU₃ h₁ hU₁ e A
      J₃₂ J₁₃
      (standardInductionIntertwinerFamily h₂ hU₂ U₁ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₂ h₁ hU₁
        μU₁ μI₁₂ hq₁₂ hM hsq₁₂ A))
    (h₂₁' : HasOpenInductionComposition L h₁ hU₁ h₀ hU₀ h₂ hU₂ e A
      J₀₁ J₂₀
      (standardInductionIntertwinerFamily h₁ hU₁ U₂ e
        (fun ψ => (rationalNormCharacters L ψ).toMul) q₂₁ h₂ hU₂
        μU₂ μI₂₁ hq₂₁ hM hsq₂₁ A)) :
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₁ hU₁ hδ₁ h₂ hU₂ hδ₂ K hK hP₁ hP₂ hP₁K hP₂K hr₁ hr₂ e hν A
      q₂₁ q₁₂ μU₁ μU₂ μI₂₁ μI₁₂ hq₂₁ hq₁₂ hM hsq₂₁ hsq₁₂
      p₂₁ p₁₂ hne₂₁ hD₂₁Ω hne₁₂ hD₁₂Ω hne' hi' =
      standardInductionCompositeCanonicalRationalScalar L hp hL
        h₀ hU₀ hδ₀ h₃ hU₃ hδ₃ K hK hP₀ hP₃ hP₀K hP₃K hr₀ hr₃ e hν A
        q₃₀ q₀₃ μU₀ μU₃ μI₃₀ μI₀₃ hq₃₀ hq₀₃ hM hsq₃₀ hsq₀₃
        p₃₀ p₀₃ hne₃₀ hD₃₀Ω hne₀₃ hD₀₃Ω hne hi := by
  let s := compactInductionScalarExtraction h₀ hU₀ hδ₀ K hP₀ hK hP₀K
    (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
    (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A
    (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
      (Classical.choose hne))
    (hi _ (Classical.choose_spec hne))
  let s' := compactInductionScalarExtraction h₁ hU₁ hδ₁ K hP₁ hK hP₁K
    (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
    (fun ψ => (hν ψ).comp e.symm.continuous) hr₁ A
    (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul)
      (Classical.choose hne'))
    (hi' _ (Classical.choose_spec hne'))
  have ch₁₂ := h₁₂.compact L h₂ hU₂ hδ₂ h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
      hP₂ hP₀ hP₁ hP₂K hP₀K hP₁K hr₂ hr₀ hr₁ e hν A
  have ch₂₁ := h₂₁.compact L h₁ hU₁ hδ₁ h₃ hU₃ hδ₃ h₂ hU₂ hδ₂ K hK
      hP₁ hP₃ hP₂ hP₁K hP₃K hP₂K hr₁ hr₃ hr₂ e hν A
  have ch₀₃ := h₀₃.compact L h₃ hU₃ hδ₃ h₂ hU₂ hδ₂ h₀ hU₀ hδ₀ K hK
      hP₃ hP₂ hP₀ hP₃K hP₂K hP₀K hr₃ hr₂ hr₀ e hν A
  have ch₃₀ := h₃₀.compact L h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ h₃ hU₃ hδ₃ K hK
      hP₀ hP₁ hP₃ hP₀K hP₁K hP₃K hr₀ hr₁ hr₃ e hν A
  have ch₀₃' := h₀₃'.compact L h₃ hU₃ hδ₃ h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK
      hP₃ hP₁ hP₀ hP₃K hP₁K hP₀K hr₃ hr₁ hr₀ e hν A
  have ch₃₀' := h₃₀'.compact L h₀ hU₀ hδ₀ h₂ hU₂ hδ₂ h₃ hU₃ hδ₃ K hK
      hP₀ hP₂ hP₃ hP₀K hP₂K hP₃K hr₀ hr₂ hr₃ e hν A
  have ch₁₂' := h₁₂'.compact L h₂ hU₂ hδ₂ h₃ hU₃ hδ₃ h₁ hU₁ hδ₁ K hK
      hP₂ hP₃ hP₁ hP₂K hP₃K hP₁K hr₂ hr₃ hr₁ e hν A
  have ch₂₁' := h₂₁'.compact L h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ h₂ hU₂ hδ₂ K hK
      hP₁ hP₀ hP₂ hP₁K hP₀K hP₂K hr₁ hr₀ hr₂ e hν A
  exact continuedCompositeRationalScalar_eq_of_parabolicComposition_symm L hp hL
    p₁₀ p₀₂ p₂₃ p₃₁ p₁₂ p₂₁ p₀₃ p₃₀ ch₁₂ ch₂₁ ch₀₃ ch₃₀
    p₀₁ p₁₃ p₃₂ p₂₀ ch₀₃' ch₃₀' ch₁₂' ch₂₁'
    (hne₃₀.mono hD₃₀Ω) (hne₀₃.mono hD₀₃Ω) (hne₂₁.mono hD₂₁Ω) (hne₁₂.mono hD₁₂Ω)
    s.val.1 s.val.2 s.property s'.val.1 s'.val.2 s'.property
    (continuedInductionComposite_compact_eq_scalar L hp hL
      h₀ hU₀ hδ₀ h₃ hU₃ hδ₃ K hK hP₀ hP₃ hP₀K hP₃K hr₀ hr₃ e hν A
      _ _ p₃₀ p₀₃ hD₃₀ hne₃₀ hD₃₀Ω hD₀₃ hne₀₃ hD₀₃Ω hD hne hi
      s.val.1 s.val.2 s.property)
    (continuedInductionComposite_compact_eq_scalar L hp hL
      h₁ hU₁ hδ₁ h₂ hU₂ hδ₂ K hK hP₁ hP₂ hP₁K hP₂K hr₁ hr₂ e hν A
      _ _ p₂₁ p₁₂ hD₂₁ hne₂₁ hD₂₁Ω hD₁₂ hne₁₂ hD₁₂Ω hD' hne' hi'
      s'.val.1 s'.val.2 s'.property)

end Canonical

end Langlands.Plancherel
