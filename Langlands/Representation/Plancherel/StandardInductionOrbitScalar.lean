import Langlands.Representation.Plancherel.StandardInductionSelfComparison

/-! # Orbit scalars for the actual standard integral families -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints L)]
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
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
  (hsq₀₁ : SquaredModulusCompatibility h₁ hU₁ h₀ hU₀)

local notation "νL" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "νM" => (fun ψ => MonoidHom.comp
  (Additive.toMul (rationalNormCharacters L ψ)) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e νL
local notation "Ω₁₀" => standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e νL q₁₀ A
local notation "Ω₀₁" => standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e νL q₀₁ A
local notation "J₁₀" => standardInductionIntertwinerFamily
  h₀ hU₀ U₁ e νL q₁₀ h₁ hU₁ μU₁ μI₁₀ hq₁₀ hM hsq₁₀ A
local notation "J₀₁" => standardInductionIntertwinerFamily
  h₁ hU₁ U₀ e νL q₀₁ h₀ hU₀ μU₀ μI₀₁ hq₀₁ hM hsq₀₁ A

variable
  (p : RationalOperatorContinuationData
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
  (q : RationalOperatorContinuationData
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
  {D₁₀ D₀₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD₁₀ : IsOpen D₁₀) (hne₁₀ : D₁₀.Nonempty)
  (hD₁₀Ω : D₁₀ ⊆ standardIntertwiningFullDomainRegion h₀ hU₀ U₁ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₁₀ A)
  (hD₀₁ : IsOpen D₀₁) (hne₀₁ : D₀₁.Nonempty)
  (hD₀₁Ω : D₀₁ ⊆ standardIntertwiningFullDomainRegion h₁ hU₁ U₀ e
    (fun ψ => (rationalNormCharacters L ψ).toMul) q₀₁ A)

local notation "π" => SmoothRep.pullback e A
local notation "fC" => continuedCompositeRationalScalar L hp hL p q
  (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω)
local notation "C" => continuedInductionComposite L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω
local notation "hd" => standardInductionSelfBaseChangeData_stabilizer
  h₀ hU₀ h₁ hU₁ e νL A q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
  hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω

variable [TopologicalSpace.SeparableSpace G]
  {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ χ ∈ D,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => MonoidHom.comp (rationalNormCharacters L ψ).toMul
        e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)

include hD₁₀ hD₀₁ hD hne hi

/-- The fraction extracted from the actual standard-integral composite
is fixed by every genuine inducing self-twist. No comparison squares are inputs. -/
theorem standardInductionCompositeRationalScalar_stabilizer_fixed
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    ∀ τ : smoothRepUnramifiedTwistStabilizer νL π,
      rationalUnramifiedFunctionFieldTranslation L hp hL τ.val (fC v ℓ) = fC v ℓ :=
  continuedInductionCompositeRationalScalar_stabilizer_fixed L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi hd v ℓ hℓ

/-- Finite full stabilizer gives an invariant presentation for the actual
standard-integral composite fraction; the original squares have been proved. -/
def standardInductionCompositeOrbitScalarPresentation
    [Finite (smoothRepUnramifiedTwistStabilizer νL π)]
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) (fC v ℓ) :=
  continuedInductionCompositeOrbitScalarPresentation L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi hd v ℓ hℓ

/-- The continued actual standard-integral composite equals any invariant
presentation of its extracted scalar at every common regular parameter. -/
theorem standardInductionComposite_eq_orbitScalar
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) (fC v ℓ))
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (hχ : r.denominator.val χ.val ≠ 0) :
    C χ =
      r.orbitValue π ⟨unramifiedTwistOrbitMap νL π χ.val,
        (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ •
          Representation.IntertwiningMap.id
            (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation :=
  continuedInductionComposite_eq_orbitScalar L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi v ℓ hℓ r χ hχ

/-- On the intersection of the two original full domains, the actual
standard integrals themselves compose to the orbit scalar times identity. -/
theorem standardInductionOriginalComposite_eq_orbitScalar
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) (fC v ℓ))
    (χ : ↥(Ω₁₀ ∩ Ω₀₁))
    (hχ : r.denominator.val χ.val ≠ 0) :
    (J₀₁ ⟨χ.val, χ.property.2⟩).comp (J₁₀ ⟨χ.val, χ.property.1⟩) =
      r.orbitValue π ⟨unramifiedTwistOrbitMap νL π χ.val,
        (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ •
          Representation.IntertwiningMap.id
            (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation := by
  let χR : ↥(p.regularRegion ∩ q.regularRegion) :=
    ⟨χ.val, p.subset_regularRegion χ.property.1, q.subset_regularRegion χ.property.2⟩
  have he : C χR =
      (J₀₁ ⟨χ.val, χ.property.2⟩).comp (J₁₀ ⟨χ.val, χ.property.1⟩) := by
    exact congrArg₂ Representation.IntertwiningMap.comp
      (continuedInductionIntertwiner_agrees L hp hL
      h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e hν A
      J₀₁ q hD₀₁ hne₀₁ hD₀₁Ω ⟨χ.val, χ.property.2⟩)
      (continuedInductionIntertwiner_agrees L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      J₁₀ p hD₁₀ hne₁₀ hD₁₀Ω ⟨χ.val, χ.property.1⟩)
  exact he.symm.trans (standardInductionComposite_eq_orbitScalar L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi v ℓ hℓ r χR hχ)

end Langlands.Plancherel
