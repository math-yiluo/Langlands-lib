import Langlands.Representation.Plancherel.StandardInductionOrbitScalar

/-! # Canonical rational scalars of actual standard integral composites -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily StandardIntertwining

universe u uG uI uV

section Extraction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (χ : unramifiedCharacters ν)
  (hi : (UnramifiedLeviInduction h hU ν χ A).IsIrreducible)

include hδ hP hK hPK hν hr hi

/-- One irreducible actual induction makes the fixed compact carrier nonzero.
No open irreducibility locus or scalarity assertion is used. -/
theorem compactInductionPicture_nontrivial_of_irreducible :
    Nontrivial (CompactInductionPicture h K A) := by
  let := hi
  let : Nontrivial (UnramifiedLeviInduction h hU ν χ A) :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G)
      (UnramifiedLeviInduction h hU ν χ A).representation.asModule
  exact (unramifiedCompactRepresentationEquiv
    h hU hδ K hP hK hPK ν hν hr A χ).toLinearEquiv.symm.toEquiv.nontrivial

/-- Select a normalized algebraic coefficient on the actual compact carrier.
The needed nontriviality follows from the displayed irreducible induction. -/
def compactInductionScalarExtraction :
    {z : CompactInductionPicture h K A ×
      (CompactInductionPicture h K A →ₗ[ℂ] ℂ) // z.2 z.1 = 1} :=
  Classical.choice (by
    let := compactInductionPicture_nontrivial_of_irreducible
      h hU hδ K hP hK hPK ν hν hr A χ hi
    obtain ⟨v, hv⟩ := exists_ne (0 : CompactInductionPicture h K A)
    obtain ⟨ℓ, hℓ⟩ := exists_normalized_scalar_functional v hv
    exact ⟨⟨(v, ℓ), hℓ⟩⟩)

end Extraction

section StandardComposite

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
variable
  {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ χ ∈ D,
    (UnramifiedLeviInduction h₀ hU₀
      (fun ψ => MonoidHom.comp (rationalNormCharacters L ψ).toMul
        e.symm.toMulEquiv.toMonoidHom)
      (unramifiedCharactersHomeomorph e (fun ψ => (rationalNormCharacters L ψ).toMul) χ)
      A).IsIrreducible)

set_option quotPrecheck false in
local notation "s" => compactInductionScalarExtraction h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A
  (χM (Classical.choose hne)) (hi _ (Classical.choose_spec hne))

/-- The scalar fraction of the actual standard-integral composite, using an
internally selected normalized coefficient from an irreducible induction. -/
def standardInductionCompositeCanonicalRationalScalar :
    rationalUnramifiedFunctionField L hp hL :=
  fC (s).val.1 (s).val.2

local notation "jC" => standardInductionCompositeCanonicalRationalScalar L hp hL
  h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
  q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
  p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne hi

set_option quotPrecheck false in
local notation "T₁₀" => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K
  νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀
  h₁ hU₁ hδ₁ hP₁ hP₁K hr₁
set_option quotPrecheck false in
local notation "T₀₁" => compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K
  νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₁
  h₀ hU₀ hδ₀ hP₀ hP₀K hr₀

include hD₁₀ hD₀₁

omit [NonarchimedeanGroup (GroupScheme.rationalPoints L)] in
/-- Changing both rational continuation choices preserves the internally
defined fraction, even when the original full domains do not intersect. -/
theorem standardInductionCompositeCanonicalRationalScalar_continuation_independent
    (p' : RationalOperatorContinuationData Ω₁₀
      (fun χ => T₁₀ (χM χ.val) A (J₁₀ χ)))
    (q' : RationalOperatorContinuationData Ω₀₁
      (fun χ => T₀₁ (χM χ.val) A (J₀₁ χ))) :
    jC = standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      p' q' hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne hi :=
  continuedCompositeRationalScalar_continuation_independent L hp hL
    p q p' q' hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω (s).val.1 (s).val.2

variable [TopologicalSpace.SeparableSpace G]

include hD

omit [NonarchimedeanGroup (GroupScheme.rationalPoints L)] in
/-- Every normalized compact coefficient yields exactly the internally
defined scalar fraction. -/
theorem standardInductionCompositeCanonicalRationalScalar_eq_extraction
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    jC = fC v ℓ :=
  continuedInductionCompositeRationalScalar_independent L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    J₁₀ J₀₁ p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
    (s).val.1 v (s).val.2 ℓ (s).property hℓ

omit [NonarchimedeanGroup (GroupScheme.rationalPoints L)] in
/-- A different nonempty irreducibility locus selects the same fraction.
Only the first locus needs to be open for the generic scalarity proof. -/
theorem standardInductionCompositeCanonicalRationalScalar_irreducibility_locus_independent
    {D' : Set (unramifiedCharacters νL)} (hne' : D'.Nonempty)
    (hi' : ∀ χ ∈ D', (UnramifiedLeviInduction h₀ hU₀ νM (χM χ) A).IsIrreducible) :
    jC = standardInductionCompositeCanonicalRationalScalar L hp hL
      h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
      q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
      p q hne₁₀ hD₁₀Ω hne₀₁ hD₀₁Ω hne' hi' := by
  let s' := compactInductionScalarExtraction h₀ hU₀ hδ₀ K hP₀ hK hP₀K
    νM (fun ψ => (hν ψ).comp e.symm.continuous) hr₀ A
    (χM (Classical.choose hne')) (hi' _ (Classical.choose_spec hne'))
  exact standardInductionCompositeCanonicalRationalScalar_eq_extraction L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
    s'.val.1 s'.val.2 s'.property

/-- The internally defined scalar is fixed by every actual inducing
self-twist, with original comparison squares supplied by proved naturality. -/
theorem standardInductionCompositeCanonicalRationalScalar_stabilizer_fixed :
    ∀ τ : smoothRepUnramifiedTwistStabilizer νL π,
      rationalUnramifiedFunctionFieldTranslation L hp hL τ.val jC = jC :=
  standardInductionCompositeRationalScalar_stabilizer_fixed L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
    (s).val.1 (s).val.2 (s).property

/-- A finite full stabilizer yields an invariant presentation of the
internally defined scalar of the actual standard-integral composite. -/
def standardInductionCompositeCanonicalOrbitScalarPresentation
    [Finite (smoothRepUnramifiedTwistStabilizer νL π)] :
    UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) jC :=
  standardInductionCompositeOrbitScalarPresentation L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
    (s).val.1 (s).val.2 (s).property

/-- The actual continued standard composite equals every invariant
presentation of the canonical scalar on their common regular region. -/
theorem standardInductionComposite_eq_canonicalOrbitScalar
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) jC)
    (χ : ↥(p.regularRegion ∩ q.regularRegion))
    (hχ : r.denominator.val χ.val ≠ 0) :
    C χ =
      r.orbitValue π ⟨unramifiedTwistOrbitMap νL π χ.val,
        (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ •
          Representation.IntertwiningMap.id
            (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation :=
  standardInductionComposite_eq_orbitScalar L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
    (s).val.1 (s).val.2 (s).property r χ hχ

/-- On the two original full domains, the actual standard integrals compose
to the canonical orbit scalar wherever its presentation denominator is nonzero. -/
theorem standardInductionOriginalComposite_eq_canonicalOrbitScalar
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) jC)
    (χ : ↥(Ω₁₀ ∩ Ω₀₁))
    (hχ : r.denominator.val χ.val ≠ 0) :
    (J₀₁ ⟨χ.val, χ.property.2⟩).comp (J₁₀ ⟨χ.val, χ.property.1⟩) =
      r.orbitValue π ⟨unramifiedTwistOrbitMap νL π χ.val,
        (r.orbitRegularRegion_map π χ.val).mpr hχ⟩ •
          Representation.IntertwiningMap.id
            (UnramifiedLeviInduction h₀ hU₀ νM (χM χ.val) A).representation :=
  standardInductionOriginalComposite_eq_orbitScalar L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ e hν A
    q₁₀ q₀₁ μU₀ μU₁ μI₁₀ μI₀₁ hq₁₀ hq₀₁ hM hsq₁₀ hsq₀₁
    p q hD₁₀ hne₁₀ hD₁₀Ω hD₀₁ hne₀₁ hD₀₁Ω hD hne hi
    (s).val.1 (s).val.2 (s).property r χ hχ

end StandardComposite

end Langlands.Plancherel
