import Langlands.Representation.Plancherel.DynamicRepresentedIntegralComposition
import Langlands.Representation.Intertwining.PQIntegralIntertwiningOperatorProof
import Langlands.Representation.Aubert.General.RepresentedSameLeviGenericRegularity
import Langlands.Analysis.Local.SubgroupCompactOpenHaar

/-! # Integral-normalized operators on represented dynamic pairs -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic Haar
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviStructuralComparison

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  equalitySubgroupMeasurable equalitySubgroupBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ ψ₀ ψ₁ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (d₀ : ParabolicData χ ψ₀ T a) (d₁ : ParabolicData χ ψ₁ T a)
  (b₀ : ParabolicData χ (Dynamic.inverseCocharacter ψ₀) T a)
  (h₀ : Dynamic.centralizer ψ₀ = Dynamic.centralizer χ) (ha : IsSplitComponent a)

section Measure

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

/-- Fix the Haar scale on the represented complement using the input compact open. -/
def representedPairHaar : Measure (representedComplement b₀ d₁) :=
  subgroupCompactOpenHaar K hK _ (representedComplement_isClosed b₀ d₁)

instance representedPairHaar_isHaarMeasure : (representedPairHaar d₁ b₀ K hK).IsHaarMeasure :=
  subgroupCompactOpenHaar_isHaarMeasure K hK _ _

end Measure

section Operator

variable (measure : Measure (representedComplement b₀ d₁))
  (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))

set_option quotPrecheck false in
local notation "Maps" => (representedInduction hG d₀ σ).representation.IntertwiningMap
  (representedInduction hG d₁ σ).representation
local notation "Normalized" => representedIsIntegralIntertwiner hG d₀ d₁ b₀

include h₀ ha in
set_option maxHeartbeats 600000 in
/-- `PQ`-regularity gives a unique integral-normalized map between the represented vertices. -/
theorem existsUnique_representedIntegralOperator [measure.IsHaarMeasure]
    (hPQ : representedIsPQRegular hG d₀ d₁ σ) :
    ∃! J : Maps, Normalized measure σ J :=
  (pqIntegralIntertwiningOperator.{u, uV} F G hG
    d₀.P (parameterScheme χ) d₀.U d₁.P d₁.U b₀.P b₀.U
    d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.r.isCompatible.levi d₀.radical
    (multiplication_isIso hG d₀)
    d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi d₁.radical
    (multiplication_isIso hG d₁)
    b₀.p b₀.l b₀.n b₀.r.isCompatible.parabolic b₀.r.isCompatible.levi b₀.radical
    (multiplication_isIso hG b₀) (d₀.levi_comp.trans d₁.levi_comp.symm)
    (b₀.levi_comp.trans d₀.levi_comp.symm) (pointImage_inter_dynamicOpposite d₀ b₀ h₀) measure).2
      T a ha σ hPQ

/-- The unique represented map at the specified Haar measure and a `PQ`-regular parameter. -/
def representedIntegralOperator [measure.IsHaarMeasure]
    (hPQ : representedIsPQRegular hG d₀ d₁ σ) : Maps :=
  (existsUnique_representedIntegralOperator hG d₀ d₁ b₀ h₀ ha measure σ hPQ).exists.choose

/-- The chosen operator is integral-normalized. -/
theorem representedIntegralOperator_spec [measure.IsHaarMeasure]
    (hPQ : representedIsPQRegular hG d₀ d₁ σ) :
    Normalized measure σ (representedIntegralOperator hG d₀ d₁ b₀ h₀ ha measure σ hPQ) :=
  (existsUnique_representedIntegralOperator hG d₀ d₁ b₀ h₀ ha measure σ hPQ).exists.choose_spec

/-- Rescaling the measure multiplies the represented normalized map by the same scalar. -/
theorem representedIsIntegralIntertwiner_smul
    (c : ℝ≥0) (J : Maps) (hJ : Normalized measure σ J) :
    Normalized (c • measure) σ ((c : ℂ) • J) := by
  intro f hf ℓ
  obtain ⟨hi, he⟩ := hJ f hf ℓ
  refine ⟨hi.smul_measure_nnreal, ?_⟩
  change ℓ ((c : ℂ) • eval _ _ (J f) 1) = _
  exact (map_smul ℓ _ _).trans ((congrArg ((c : ℂ) • ·) he).trans
    (integral_smul_nnreal_measure _ _).symm)

include h₀ ha in
/-- Comparing two Haar measures gives a single strictly positive factor for
all `PQ`-regular representations and normalized maps on the same pair. -/
theorem exists_smul_representedIsIntegralIntertwiner_of_haar [measure.IsHaarMeasure]
    (measure' : Measure (representedComplement b₀ d₁)) [measure'.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (τ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
      (J J' : (representedInduction hG d₀ τ).representation.IntertwiningMap
        (representedInduction hG d₁ τ).representation),
      representedIsPQRegular hG d₀ d₁ τ → Normalized measure τ J → Normalized measure' τ J' →
      J' = (c : ℂ) • J := by
  have : LocallyCompactSpace (representedComplement b₀ d₁) :=
    (representedComplement_isClosed b₀ d₁).locallyCompactSpace
  have : SecondCountableTopology (representedComplement b₀ d₁) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let c := Measure.haarScalarFactor measure' measure
  have hmeasure : measure' = c • measure := Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨c, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  intro τ J J' hPQ hJ hJ'
  refine (existsUnique_representedIntegralOperator hG d₀ d₁ b₀ h₀ ha measure' τ hPQ).unique hJ' ?_
  exact hmeasure.symm ▸ representedIsIntegralIntertwiner_smul hG d₀ d₁ b₀ measure τ c J hJ

end Operator

include ha in
set_option maxHeartbeats 600000 in
/-- A nonzero principal open of the actual intrinsic twist parameters is
`PQ`-regular for an irreducible admissible inducing representation. -/
theorem exists_generic_representedIsPQRegular
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (hσ : σ.IsIrreducible) (hA : σ.IsAdmissible) :
    ∃ poly : MvPolynomial (Fin (rationalImageRank (parameterScheme χ))) ℂ, poly ≠ 0 ∧
      ∀ z ∈ rationalUnramifiedPrincipalOpen (parameterScheme χ)
        (parameterScheme_isConnectedReductive χ hG) poly,
        representedIsPQRegular hG d₀ d₁
          (σ.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) z)) :=
  exists_generic_isPQRegular.{u, uV} F G hG
    d₀.P (parameterScheme χ) d₀.U d₁.P d₁.U
    d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.r.isCompatible.levi d₀.radical
    (multiplication_isIso hG d₀)
    d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi d₁.radical
    (multiplication_isIso hG d₁) (d₀.levi_comp.trans d₁.levi_comp.symm) T a ha σ hσ hA

end Langlands.Plancherel.DynamicCommonLeviPresentations
