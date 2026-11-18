import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationReductionStatement

/-! # Proof of the common-Levi presentation reduction -/

noncomputable section

set_option maxHeartbeats 400000

universe u uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviPresentationReduction

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open DynamicCommonLeviPresentationComparison DynamicCommonLeviStructuralComparison
open UnramifiedOperatorFamily

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

local instance reductionSubgroupMeasurable {H : Type u} [Group H] [TopologicalSpace H]
    (U : Subgroup H) : MeasurableSpace U := borel _
local instance reductionSubgroupBorel {H : Type u} [Group H] [TopologicalSpace H]
    (U : Subgroup H) : BorelSpace U := ⟨rfl⟩
local instance reductionIntersectionMeasurable {H : Type u} [Group H] [TopologicalSpace H]
    (U V : Subgroup H) : MeasurableSpace (U.subgroupOf V) := borel _
local instance reductionIntersectionBorel {H : Type u} [Group H] [TopologicalSpace H]
    (U V : Subgroup H) : BorelSpace (U.subgroupOf V) := ⟨rfl⟩
local instance reductionQuotientMeasurable {H : Type u} [Group H] [TopologicalSpace H]
    (U V : Subgroup H) : MeasurableSpace (QuotientSpace (U := U) V) := borel _
local instance reductionQuotientBorel {H : Type u} [Group H] [TopologicalSpace H]
    (U V : Subgroup H) : BorelSpace (QuotientSpace (U := U) V) := ⟨rfl⟩

section Generic

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]

omit [LocallyCompactSpace H] in
/-- Admissibility only depends on the ambient action. -/
theorem representationOfEq_isAdmissible' {M₀ M₁ : Subgroup H} (eM : M₀ = M₁)
    (B : SmoothRep.{0, u, uV} ℂ M₁) (hB : B.IsAdmissible) :
    (representationOfEq eM B).IsAdmissible := by
  subst eM
  exact hB

omit [LocallyCompactSpace H] in
/-- Finite length only depends on the ambient action. -/
theorem representationOfEq_hasFiniteLength' {M₀ M₁ : Subgroup H} (eM : M₀ = M₁)
    (B : SmoothRep.{0, u, uV} ℂ M₁) (hB : B.HasFiniteLength) :
    (representationOfEq eM B).HasFiniteLength := by
  subst eM
  exact hB

/-- The squared-modulus identity only depends on the literal subgroups. -/
theorem squaredModulusCompatibility_ofEq
    {P₀ M₀ U₀ P₀' U₀' P₁ M₁ U₁ P₁' U₁' : Subgroup H}
    (eP : P₀ = P₁) (eM : M₀ = M₁) (eU : U₀ = U₁) (eP' : P₀' = P₁') (eU' : U₀' = U₁')
    (h₀ : IsSemidirectDecomposition P₀ M₀ U₀) (hU₀ : IsClosed (U₀ : Set H))
    (h₀' : IsSemidirectDecomposition P₀' M₀ U₀') (hU₀' : IsClosed (U₀' : Set H))
    (h₁ : IsSemidirectDecomposition P₁ M₁ U₁) (hU₁ : IsClosed (U₁ : Set H))
    (h₁' : IsSemidirectDecomposition P₁' M₁ U₁') (hU₁' : IsClosed (U₁' : Set H))
    (hsq : SquaredModulusCompatibility h₀ hU₀ h₀' hU₀') :
    SquaredModulusCompatibility h₁ hU₁ h₁' hU₁' := by
  subst eP eM eU eP' eU'
  exact hsq

omit [LocallyCompactSpace H] [NonarchimedeanGroup H] in
theorem quotientMeasureOfEq_rfl {U V : Subgroup H}
    (ν : Measure (QuotientSpace (U := U) V)) :
    quotientMeasureOfEq (rfl : U = U) (rfl : V = V) ν = ν := by
  change Measure.map id ν = ν
  exact Measure.map_id

/-- Weak integrals agree on functions with the same ambient values. -/
theorem hasIntegral_ofEq_iff
    {P₀ M₀ U₀ U₀' P₁ M₁ U₁ U₁' : Subgroup H}
    (eP : P₀ = P₁) (eM : M₀ = M₁) (eU : U₀ = U₁) (eU' : U₀' = U₁')
    (h₀ : IsSemidirectDecomposition P₀ M₀ U₀) (hU₀ : IsClosed (U₀ : Set H))
    (h₁ : IsSemidirectDecomposition P₁ M₁ U₁) (hU₁ : IsClosed (U₁ : Set H))
    (B : SmoothRep.{0, u, uV} ℂ M₁) (ν : Measure (QuotientSpace (U := U₁) U₁'))
    (f₀ : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (representationOfEq eM B))
    (f₁ : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj B)
    (hf : ∀ x, eval _ _ f₀ x = eval _ _ f₁ x) (Jf : H → B) :
    HasIntegral h₀ hU₀ U₀' (representationOfEq eM B) (quotientMeasureOfEq eU eU' ν) f₀ Jf ↔
      HasIntegral h₁ hU₁ U₁' B ν f₁ Jf := by
  subst eP eM eU eU'
  rw [quotientMeasureOfEq_rfl]
  have hf' : (f₀ : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj B) = f₁ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hf x
  show HasIntegral h₁ hU₁ U₀' B ν f₀ Jf ↔ _
  rw [hf']

/-- The full-domain condition only depends on the literal subgroups. -/
theorem domain_ofEq_eq_top_iff
    {P₀ M₀ U₀ U₀' P₁ M₁ U₁ U₁' : Subgroup H}
    (eP : P₀ = P₁) (eM : M₀ = M₁) (eU : U₀ = U₁) (eU' : U₀' = U₁')
    (h₀ : IsSemidirectDecomposition P₀ M₀ U₀) (hU₀ : IsClosed (U₀ : Set H))
    (h₁ : IsSemidirectDecomposition P₁ M₁ U₁) (hU₁ : IsClosed (U₁ : Set H))
    (B : SmoothRep.{0, u, uV} ℂ M₁) (ν : Measure (QuotientSpace (U := U₁) U₁')) :
    domain h₀ hU₀ U₀' (representationOfEq eM B) (quotientMeasureOfEq eU eU' ν) = ⊤ ↔
      domain h₁ hU₁ U₁' B ν = ⊤ := by
  subst eP eM eU eU'
  rw [quotientMeasureOfEq_rfl]
  exact Iff.rfl

end Generic

section Core

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {M P U P' U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {a : T.toGrp ⟶ M} {n : U ⟶ P}
  {p' : P' ⟶ G} {l' : M ⟶ P'} {n' : U' ⟶ P'}
  (hG : IsConnectedReductive G)
  (χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (r : ParabolicRootPresentation p l a)
  (s : Realizes χ ψ p l n) (s' : Realizes χ ψ' p' l' n')
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))
  (h' : IsSemidirectDecomposition
    ((SubgroupFunctor.range p').carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))))
  (hU' : IsClosed (((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))
  (hP : IsClosed (((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))
  (hP' : IsClosed (((SubgroupFunctor.range p').carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))
  (K : OpenSubgroup (rationalPoints G))
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : ∀ g : rationalPoints G,
    ∃ p₀ : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)), ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G))
  (hP'K : ∀ g : rationalPoints G,
    ∃ p₀ : (SubgroupFunctor.range p').carrier (Over.mk (𝟙 _)), ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G))
  (hr : Continuous h.projection) (hr' : Continuous h'.projection)
  (hψK : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ, ∃ k : K,
    g = (p₀ : rationalPoints G) * (k : rationalPoints G))
  (hψ'K : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ', ∃ k : K,
    g = (p₀ : rationalPoints G) * (k : rationalPoints G))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (hδ : IsUnimodularModulus _ hU) (hδ' : IsUnimodularModulus _ hU')
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The ψ'-side identity of compact sections. -/
abbrev targetPictureComparison :=
  compactPictureComparisonOfEq (parabolicPoints_eq χ ψ' s') (leviPoints_eq χ ψ s)
    (radicalPoints_eq χ ψ' s') h' (commonDecomposition χ ψ' hψ') K A

include s s' h hU h' hU' hsq in
/-- The actual squared-modulus identity, transported from the presentation. -/
theorem commonSquaredModulus :
    SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (commonDecomposition χ ψ' hψ') (radical_isClosed ψ') :=
  squaredModulusCompatibility_ofEq (parabolicPoints_eq χ ψ s) (leviPoints_eq χ ψ s)
    (radicalPoints_eq χ ψ s) (parabolicPoints_eq χ ψ' s') (radicalPoints_eq χ ψ' s')
    h hU h' hU' (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ') hsq

/-- Source full convergence at the corresponding character is actual full convergence. -/
theorem mem_pairFullDomainRegion (z : unramifiedCharacters (normCharacters χ))
    (hz : domain h hU ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
      ((presentationRepresentation χ ψ s A).twist
        (characterComparison χ ψ r s z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r)
          (characterComparison χ ψ r s z)))
      (presentationQuotientMeasure χ ψ s K ψ' s' hK) = ⊤) :
    z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' A :=
  (domain_ofEq_eq_top_iff (parabolicPoints_eq χ ψ s) (leviPoints_eq χ ψ s)
    (radicalPoints_eq χ ψ s) (radicalPoints_eq χ ψ' s') h hU
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (A.twist (parameterTransport χ z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z)))
    (pairQuotientMeasure K hK ψ ψ')).mp hz

/-- The source standard compact operator at a presentation character, with the
source measures pulled back from the actual pair measures. -/
abbrev sourceOperator (w : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (hw : domain h hU ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
      ((presentationRepresentation χ ψ s A).twist w.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) w))
      (presentationQuotientMeasure χ ψ s K ψ' s' hK) = ⊤) :=
  standardCompactOperator h hU hδ K hP hK hPK (parabolicLeviRationalNormCharacters r)
    (continuous_parabolicLeviRationalNormCharacters r) hr h' hU' hδ' hP' hP'K hr'
    (presentationQuotientMeasure χ ψ s K ψ' s' hK) (presentationRadicalHaar χ K ψ' s' hK)
    (presentationIntersectionHaar χ ψ s K ψ' s' hK)
    (presentationQuotientMeasure_isCompatible χ ψ s K ψ' s' hK)
    (isClosed_parabolicLeviPointSubgroup r) hsq w (presentationRepresentation χ ψ s A) hw

/-- The compact operator square: conjugating the source standard compact operator at the
corresponding character by the identity comparisons of compact sections gives the actual
compact family. -/
def OperatorSquare : Prop :=
  ∀ (z : unramifiedCharacters (normCharacters χ))
    (hz : z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' A)
    (hw : domain h hU ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
      ((presentationRepresentation χ ψ s A).twist (characterComparison χ ψ r s z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r)
          (characterComparison χ ψ r s z)))
      (presentationQuotientMeasure χ ψ s K ψ' s' hK) = ⊤),
    (targetPictureComparison χ ψ ψ' hψ' s s' h' K A).toLinearEquiv.toLinearMap ∘ₗ
        (sourceOperator χ ψ ψ' r s s' h hU h' hU' hP hP' K hK hPK hP'K hr hr' A hδ hδ' hsq
            (characterComparison χ ψ r s z) hw ∘ₗ
          (compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm.toLinearMap) =
      compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
        (commonSquaredModulus χ ψ ψ' hψ hψ' s s' h hU h' hU' hsq) A ⟨z, hz⟩

/-- Core assembly: source full convergence and rationality on `D ⊇ S`, with `S` open and
nonempty, give the actual common-Levi continuation on the preimage of `S`. -/
theorem continuationExists_of_source
    {S D : Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))}
    (hSD : S ⊆ D) (hS : IsOpen S) (hSne : S.Nonempty)
    (hfull : ∀ w : D, domain h hU ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
      ((presentationRepresentation χ ψ s A).twist w.val.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) w.val))
      (presentationQuotientMeasure χ ψ s K ψ' s' hK) = ⊤)
    (hrat : StandardCompactRationalOn h hU hδ K hP hK hPK (parabolicLeviRationalNormCharacters r)
      (continuous_parabolicLeviRationalNormCharacters r) hr h' hU' hδ' hP' hP'K hr'
      (presentationQuotientMeasure χ ψ s K ψ' s' hK) (presentationRadicalHaar χ K ψ' s' hK)
      (presentationIntersectionHaar χ ψ s K ψ' s' hK)
      (presentationQuotientMeasure_isCompatible χ ψ s K ψ' s' hK)
      (isClosed_parabolicLeviPointSubgroup r) hsq D (presentationRepresentation χ ψ s A) hfull)
    (hop : OperatorSquare hG χ ψ ψ' hψ hψ' r s s' h hU h' hU' hP hP' K hK hPK hP'K hr hr'
      hψK hψ'K A hδ hδ' hsq) :
    CommonLeviContinuationExists χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A := by
  let cc := characterComparison χ ψ r s
  let Ω : Set (unramifiedCharacters (normCharacters χ)) := cc ⁻¹' S
  have hΩo : IsOpen Ω := hS.preimage cc.continuous
  have hΩne : Ω.Nonempty := by
    obtain ⟨w, hw⟩ := hSne
    refine ⟨cc.symm w, ?_⟩
    show cc (cc.symm w) ∈ S
    rw [cc.apply_symm_apply]
    exact hw
  have hΩ : Ω ⊆ pairFullDomainRegion χ K hK ψ hψ ψ' A := by
    intro z hz
    have hw := hfull ⟨cc z, hSD hz⟩
    exact mem_pairFullDomainRegion χ ψ ψ' hψ r s s' h hU K hK A z hw
  have h1 := (isRationalOperatorOn_comparison_iff χ ψ r s S _).mpr (hrat.restrict hSD)
  have h2 := (h1.precomp
      (compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm.toLinearMap).postcomp
    (targetPictureComparison χ ψ ψ' hψ' s s' h' K A).toLinearEquiv.toLinearMap
  have heq : restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
      (commonSquaredModulus χ ψ ψ' hψ hψ' s s' h hU h' hU' hsq) A Ω hΩ =
      fun z : Ω => (targetPictureComparison χ ψ ψ' hψ' s s' h' K A).toLinearEquiv.toLinearMap ∘ₗ
        (sourceOperator χ ψ ψ' r s s' h hU h' hU' hP hP' K hK hPK hP'K hr hr' A hδ hδ' hsq
            (cc z.val) (hfull ⟨cc z.val, hSD z.property⟩) ∘ₗ
          (compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm.toLinearMap) := by
    funext z
    exact (hop z.val (hΩ z.property) (hfull ⟨cc z.val, hSD z.property⟩)).symm
  have hJ : IsRationalOperatorOn Ω
      (restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
        (commonSquaredModulus χ ψ ψ' hψ hψ' s s' h hU h' hU' hsq) A Ω hΩ) := by
    rw [heq]
    exact h2
  exact ⟨commonSquaredModulus χ ψ ψ' hψ hψ' s s' h hU h' hU' hsq, Ω, hΩo, hΩne, hΩ, hJ,
    ⟨pairContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K _ A Ω hΩ hΩo hΩne subset_rfl hJ⟩⟩

/-- The compact operator square holds: at corresponding characters, the source standard
integral and the actual pair integral take the same ambient values. -/
theorem operatorSquare :
    OperatorSquare hG χ ψ ψ' hψ hψ' r s s' h hU h' hU' hP hP' K hK hPK hP'K hr hr'
      hψK hψ'K A hδ hδ' hsq := by
  intro z hz hw
  apply LinearMap.ext
  intro f
  have key : unramifiedInductionComparison χ ψ hψ r s h hU A z
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
        hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A)).symm
        ((compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm f)) =
      (compactEquiv χ hG K hK ψ hψ hψK z A).symm f := by
    have hc := compactRestriction_comparison χ ψ hψ r s h hU K A hδ hP hK hPK hr hG hψK z
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
        hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A)).symm
        ((compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm f))
    refine ((compactEquiv χ hG K hK ψ hψ hψK z A).eq_symm_apply).mpr (hc.symm.trans ?_)
    refine (congrArg (compactPictureComparison χ ψ hψ s h K A)
      (LinearEquiv.apply_symm_apply (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
        hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A))
        ((compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm f))).trans ?_
    exact (compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.apply_symm_apply f
  have hf : ∀ x, eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
        hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A)).symm
        ((compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm f)) x =
      eval _ _ ((compactEquiv χ hG K hK ψ hψ hψK z A).symm f) x := by
    intro x
    exact (unramifiedInductionComparison_eval χ ψ hψ r s h hU A z ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
          (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
          hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A)).symm
          ((compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm f)) x).symm.trans
      (congrArg (fun g : UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
        (leviNormCharacters χ) (parameterTransport χ z) A => eval _ _ g x) key)
  have hint := (hasIntegral_ofEq_iff (parabolicPoints_eq χ ψ s) (leviPoints_eq χ ψ s)
    (radicalPoints_eq χ ψ s) (radicalPoints_eq χ ψ' s') h hU (commonDecomposition χ ψ hψ)
    (radical_isClosed ψ)
    (A.twist (parameterTransport χ z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z)))
    (pairQuotientMeasure K hK ψ ψ') _ _ hf _).mpr
    (pairFamily_spec χ K hK ψ hψ ψ' hψ' (commonSquaredModulus χ ψ ψ' hψ hψ' s s' h hU h' hU' hsq)
      A ⟨z, hz⟩ ((compactEquiv χ hG K hK ψ hψ hψK z A).symm f))
  have hop := operator_eq h hU ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))
    ((presentationRepresentation χ ψ s A).twist (characterComparison χ ψ r s z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r)
        (characterComparison χ ψ r s z)))
    (presentationQuotientMeasure χ ψ s K ψ' s' hK) (isClosed_parabolicLeviPointSubgroup r)
    (sourceToDomain h hU _ _ hw ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
          (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
          hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A)).symm
          ((compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm f))) hint
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact (compactPictureComparisonOfEq_eval (parabolicPoints_eq χ ψ' s') (leviPoints_eq χ ψ s)
    (radicalPoints_eq χ ψ' s') h' (commonDecomposition χ ψ' hψ') K A
    (sourceOperator χ ψ ψ' r s s' h hU h' hU' hP hP' K hK hPK hP'K hr hr' A hδ hδ' hsq
      (characterComparison χ ψ r s z) hw
      ((compactPictureComparison χ ψ hψ s h K A).toLinearEquiv.symm f)) k).trans
    (congrFun hop k)

end Core

/-- **The common-Levi presentation reduction.** Waldspurger's IV.1.1, applied to the supplied
presentation with the actual pair measures pulled back to the presentation radicals and the
common-Levi representation transported to the presentation Levi, yields the actual common-Levi
continuation. -/
theorem dynamicCommonLeviPresentationReduction :
    DynamicCommonLeviContinuation.DynamicCommonLeviPresentationReductionStatement.{u, uV, uW} := by
  intro hIV F _ _ _ _ G _ _ hG χ ψ ψ' hψ hψ' T M P P' Q U U' V _ _ p l p' l' a n n' q v r r'
    hLevi hn hn' hQ hv s s' _ Ppt P'pt Mpt Upt U'pt h hU h' hU' hP hP' K hK hPK hP'K hr hr'
    hψK hψ'K A hA hfin
  have hA' := representationOfEq_isAdmissible' (leviPoints_eq χ ψ s) A hA
  have hfin' := representationOfEq_hasFiniteLength' (leviPoints_eq χ ψ s) A hfin
  obtain ⟨hδ, hδ', hsq, R, hCne, hCopen, -, hfull, hrat, -⟩ :=
    hIV F G hG T M P P' Q U U' V p l p' l' a n n' q v r r' hLevi hn hn' hQ hv h hU h' hU' hP hP'
      K hK hPK hP'K hr hr' (presentationQuotientMeasure χ ψ s K ψ' s' hK)
      (presentationRadicalHaar χ K ψ' s' hK) (presentationIntersectionHaar χ ψ s K ψ' s' hK)
      (presentationQuotientMeasure_isCompatible χ ψ s K ψ' s' hK)
      (presentationRepresentation χ ψ s A) hA' hfin'
  refine continuationExists_of_source hG χ ψ ψ' hψ hψ' r s s' h hU h' hU' hP hP' K hK hPK hP'K
    hr hr' hψK hψ'K A hδ hδ' hsq (subset_unramifiedTwistOrbitSaturation _ _ _) hCopen hCne
    hfull hrat (operatorSquare hG χ ψ ψ' hψ hψ' r s s' h hU h' hU' hP hP' K hK hPK hP'K hr hr'
      hψK hψ'K A hδ hδ' hsq)

end Langlands.Plancherel.DynamicCommonLeviPresentationReduction
