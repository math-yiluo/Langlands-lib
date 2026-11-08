import Langlands.Representation.Plancherel.StandardInductionScalarSymmetryStatement

/-! # Equality of scalars in the two standard composition orders -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uI uV uW

section LinearMaps

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Scalar composites of two maps have the same scalar when each carrier
has a normalized coefficient. The maps may both vanish. -/
theorem linearMap_compositeScalar_eq_reverse
    (f : V →ₗ[ℂ] W) (g : W →ₗ[ℂ] V)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : W) (m : W →ₗ[ℂ] ℂ) (hm : m w = 1)
    (a b : ℂ) (h₀ : g.comp f = a • LinearMap.id)
    (h₁ : f.comp g = b • LinearMap.id) : a = b := by
  by_cases hf : f = 0
  · have ha := congrArg (endomorphismScalarCoefficient v ℓ) h₀
    have hb := congrArg (endomorphismScalarCoefficient w m) h₁
    have ha0 : a = 0 := by
      simpa [hf, endomorphismScalarCoefficient_smul_id v ℓ hℓ] using ha.symm
    have hb0 : b = 0 := by
      simpa [hf, endomorphismScalarCoefficient_smul_id w m hm] using hb.symm
    exact ha0.trans hb0.symm
  · obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra! hz
      exact hf (LinearMap.ext hz)
    have h₀x : g (f x) = a • x := LinearMap.congr_fun h₀ x
    have h₁x : f (g (f x)) = b • f x := LinearMap.congr_fun h₁ (f x)
    apply (smul_left_injective ℂ hx)
    calc
      a • f x = f (a • x) := (map_smul f a x).symm
      _ = f (g (f x)) := congrArg f h₀x.symm
      _ = b • f x := h₁x

end LinearMaps

section RationalComposites

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω Λ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)
  (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
  (w : W) (m : W →ₗ[ℂ] ℂ) (hm : m w = 1)
  (hs₀ : ∀ χ : ↥(p.regularRegion ∩ q.regularRegion),
    p.continuedComposite q χ = p.continuedCompositeScalar q v ℓ χ • LinearMap.id)
  (hs₁ : ∀ χ : ↥(q.regularRegion ∩ p.regularRegion),
    q.continuedComposite p χ = q.continuedCompositeScalar p w m χ • LinearMap.id)

include hℓ hm hs₀ hs₁

omit hp hL in
/-- Once scalarity of each actual continued compact composite is proved,
the two extracted scalar values agree at every common regular parameter. -/
theorem continuedCompositeScalar_eq_reverse_of_scalar
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    p.continuedCompositeScalar q v ℓ χ =
      q.continuedCompositeScalar p w m ⟨χ.val, χ.property.2, χ.property.1⟩ :=
  linearMap_compositeScalar_eq_reverse
    (p.continuedOperator ⟨χ.val, χ.property.1⟩)
    (q.continuedOperator ⟨χ.val, χ.property.2⟩)
    v ℓ hℓ w m hm _ _ (hs₀ χ)
    (hs₁ ⟨χ.val, χ.property.2, χ.property.1⟩)

/-- Agreement of both scalar composition orders gives equality in the actual
unramified function field, without a nonvanishing hypothesis on either map. -/
theorem continuedCompositeRationalScalar_eq_reverse_of_scalar
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) :
    continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ =
      continuedCompositeRationalScalar L hp hL q p hΛ hΩ w m := by
  have hR := continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ
  have hR' := continuedCompositeRegion_nonempty L hp hL q p hΛ hΩ
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L hp hL
    _ _ hR hR' (p.regularRegion_isOpen.inter q.regularRegion_isOpen)
    hR (fun _ hχ => hχ) (fun _ hχ => ⟨hχ.2, hχ.1⟩)
  intro χ hχ
  exact continuedCompositeScalar_eq_reverse_of_scalar L p q v ℓ hℓ w m hm
    hs₀ hs₁ ⟨χ, hχ⟩

end RationalComposites

section StandardComposite

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
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

variable [TopologicalSpace.SeparableSpace G]
  {D₀ D₁ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD₀ : IsOpen D₀) (hne₀ : D₀.Nonempty)
  (hi₀ : ∀ χ ∈ D₀,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)
  (hD₁ : IsOpen D₁) (hne₁ : D₁.Nonempty)
  (hi₁ : ∀ χ ∈ D₁,
    (UnramifiedLeviInduction h₁ hU₁
      (fun ψ => (rationalNormCharacters L ψ).toMul.comp e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)

set_option quotPrecheck false in
local notation "SC₀" => continuedInductionComposite_compact_eq_scalar L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD₀ hne₀ hi₀
set_option quotPrecheck false in
local notation "SC₁" => continuedInductionComposite_compact_eq_scalar L hp hL
  h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e hν A
  J₀₁ J₁₀ q p hD₀₁ hne₀₁ hD₀₁Ω hD₁₀ hne₁₀ hD₁₀Ω hD₁ hne₁ hi₁

include hp hL hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD₀ hne₀ hi₀ hD₁ hne₁ hi₁

/-- Actual generic induced irreducibility in both orders gives equal scalar
values on the whole common regular region, including reducible parameters. -/
theorem standardInductionCompositeScalar_eq_reverse
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : CompactInductionPicture h₁ K A)
    (m : CompactInductionPicture h₁ K A →ₗ[ℂ] ℂ) (hm : m w = 1)
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    p.continuedCompositeScalar q v ℓ χ =
      q.continuedCompositeScalar p w m ⟨χ.val, χ.property.2, χ.property.1⟩ :=
  continuedCompositeScalar_eq_reverse_of_scalar L p q v ℓ hℓ w m hm
    (SC₀ v ℓ hℓ) (SC₁ w m hm) χ

/-- The exact rational fractions extracted from the two actual standard
composite orders agree; neither intertwiner is assumed nonzero. -/
theorem standardInductionCompositeRationalScalar_eq_reverse
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (w : CompactInductionPicture h₁ K A)
    (m : CompactInductionPicture h₁ K A →ₗ[ℂ] ℂ) (hm : m w = 1) :
    continuedCompositeRationalScalar L hp hL p q
        (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω) v ℓ =
      continuedCompositeRationalScalar L hp hL q p
        (hne₀₁.mono hD₀₁Ω) (hne₁₀.mono hD₁₀Ω) w m :=
  continuedCompositeRationalScalar_eq_reverse_of_scalar L hp hL p q v ℓ hℓ w m hm
    (SC₀ v ℓ hℓ) (SC₁ w m hm) (hne₁₀.mono hD₁₀Ω) (hne₀₁.mono hD₀₁Ω)

set_option quotPrecheck false in
local notation "s₀" => compactInductionScalarExtraction h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A
  (χM (Classical.choose hne₀)) (hi₀ _ (Classical.choose_spec hne₀))
set_option quotPrecheck false in
local notation "s₁" => compactInductionScalarExtraction h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₁ A
  (χM (Classical.choose hne₁)) (hi₁ _ (Classical.choose_spec hne₁))

/-- Reversing the two actual standard-integral composition orders preserves
the internally defined canonical rational scalar. The two generic
irreducibility loci are independent nonempty ambient open sets. -/
theorem standardInductionCompositeCanonicalRationalScalar_eq_reverse :
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne₀ hi₀ =
    standardInductionCompositeCanonicalRationalScalar L hp hL
      h₁ hU₁ hδ₁ h₀ hU₀ hδ₀ K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ e hν A
      q₀₁ q₁₀ μU₁ μU₀ μI₀₁ μI₁₀ hq₀₁ hq₁₀ hM hsq₀₁ hsq₁₀
      q p hne₀₁ hD₀₁Ω hne₁₀ hD₁₀Ω hne₁ hi₁ :=
  standardInductionCompositeRationalScalar_eq_reverse L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD₀ hne₀ hi₀ hD₁ hne₁ hi₁
    (s₀).val.1 (s₀).val.2 (s₀).property (s₁).val.1 (s₁).val.2 (s₁).property

end StandardComposite

/-- Exact universal target for symmetry of the canonical standard scalars. -/
theorem conditionalStandardInductionScalarSymmetry :
    ConditionalStandardInductionScalarSymmetryStatement.{u, uG, uV} := by
  intro F _ _ _ _ L _ hp hL G _ _ _ _ _ P₀ P₁ M U₀ U₁
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    _ _ _ _ _ _ _ _ _ _ _ _ q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁
    _ _ _ _ _ _ _ _ _ _ _ _ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁ p q
    D₁₀ D₀₁ hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω _
    D₀ D₁ hD₀ hne₀ hi₀ hD₁ hne₁ hi₁
  exact standardInductionCompositeCanonicalRationalScalar_eq_reverse L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD₀ hne₀ hi₀ hD₁ hne₁ hi₁

end Langlands.Plancherel
