import Langlands.Representation.Plancherel.DynamicRepresentedGalleryProductLocus
import Langlands.Representation.Plancherel.DynamicOppositeGalleryComparison
import Langlands.Representation.Plancherel.DynamicOppositeCompositeProduct
import Langlands.Representation.Plancherel.DynamicOppositeSquareIntegrableForm

/-! # The represented gallery product for the canonical opposite scalar -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Induction Aubert.General UnramifiedOperatorFamily ValuationKernelCoordinates
open DynamicCommonLeviPresentations DynamicCommonLeviComposition
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (ha : IsSplitComponent a)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

set_option hygiene false in
local notation "Mχ" => parameterScheme χ
set_option hygiene false in
local notation "hMχ" => parameterScheme_isConnectedReductive χ hG
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi
set_option hygiene false in
local notation "first" => oppositeGallerySource χ
set_option hygiene false in
local notation "last" => oppositeGalleryTarget χ
set_option hygiene false in
local notation "coef" => SmoothRep.pullback (parameterHomeomorph χ) A

set_option maxHeartbeats 1000000 in
/-- The represented gallery's dense scalar identity gives the actual
continued composite with its original forward and reverse Haar scales. -/
theorem exists_denseContinuedCompositeRankOneProduct_of_gallery
    (hgallery : HasDenseRepresentedGalleryProduct (χ := χ) hG ha K hK first last coef) :
    ∃ charts : List (RankOneTranslationChart Mχ),
      HasDenseContinuedCompositeRankOneProduct χ hRefl hCST hG K hK hPK hOppK A p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ charts := by
  obtain ⟨charts, κ, S, factors, hS, hSo, hInv, hScalar⟩ := hgallery
  refine ⟨charts, κ, S, factors, hS, hSo, hInv, ?_⟩
  intro z hz
  let w : unramifiedCharacters (normCharacters χ) := Subtype.val z
  have h := hScalar w hz
  obtain ⟨hF, hR, hc⟩ := h
  have he := intrinsicGalleryCoefficient_twist χ A w
  exact actualComposite_eq_of_galleryScalar χ hRefl hCST hG ha K hK hPK hOppK A p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z
    (he.symm ▸ hF) (he.symm ▸ hR) _ (he.symm ▸ hc)

/-- Every permitted step of the represented common-Levi gallery has a
scalar factor invariant under the translations of a rank-one chart. -/
def HasGenericRankOneGalleryFactors
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))) : Prop :=
  ∀ x y : GalleryVertex χ,
    SameDynamicChamber x.val y.val ∨ Nonempty (DynamicRankOneWall χ x.val y.val) →
    HasGenericRankOneGalleryFactor (χ := χ) hG ha K hK σ x y

include hDForward hDReverse hD in
set_option maxHeartbeats 1400000 in
/-- Assemble the canonical pointwise product from rank-one factors for the
represented gallery's steps, using only the specified original continuation. -/
theorem hasDenseRankOneProduct_of_oppositeGallery
    (hA : A.IsAdmissible) (hj : jP ≠ 0)
    (hEdge : HasGenericRankOneGalleryFactors χ hG ha K hK coef) :
    ∃ charts : List (RankOneTranslationChart Mχ),
      HasDenseRankOneProduct Mχ hMχ charts jP := by
  have hA_irr := DynamicOppositeSquareIntegrableForm.irreducible_of_locus χ hG A hne hi
  have hCoefIrr : (coef).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation (parameterHomeomorph χ)).mpr hA_irr
  have hCoefAdm : (coef).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (parameterHomeomorph χ) hA
  obtain ⟨data⟩ := nonempty_representedGalleryProductData (χ := χ) hG ha K hK first last
  have hg := hasDenseRepresentedGalleryProduct (χ := χ) hG ha K hK first last coef data hCoefIrr
    hCoefAdm (fun e he => hEdge e.1 e.2 (data.edge_chamber_or_wall e he))
  obtain ⟨charts, hcharts⟩ := exists_denseContinuedCompositeRankOneProduct_of_gallery
    χ hRefl hCST hG ha K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hg
  exact ⟨charts, hasDenseRankOneProduct_of_continuedComposite χ hRefl hCST hG K hK hPK hOppK A p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi charts hj hcharts⟩

end Langlands.Plancherel
