import Langlands.Representation.Plancherel.DynamicContinuationOpenFullDomain
import Langlands.Representation.Plancherel.DynamicCommonLeviClearedOperator
import Langlands.Representation.Plancherel.DynamicCommonLeviPQDiscriminant
import Langlands.Representation.Plancherel.DynamicOppositeGalleryComparison
import Langlands.Representation.Plancherel.RationalOperatorPolesFromZeroFibers

/-! # Pole presentations for common-Levi integrals on open convergence regions -/

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviContinuation

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviPresentations
open DynamicOppositeCanonicalScalar ActualCommonLeviTensor UnramifiedOperatorFamily

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
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (x y : GalleryVertex χ)
  (hxK : ∀ g : rationalPoints G, ∃ p : parabolic x.val, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hyK : ∀ g : rationalPoints G, ∃ p : parabolic y.val, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hδ : SquaredModulusCompatibility (commonDecomposition χ x.val x.property) (radical_isClosed x.val)
    (commonDecomposition χ y.val y.property) (radical_isClosed y.val))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

include ha in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonempty open region of full convergence admits an actual compact continuation
and a pole presentation. The denominator of the continuation is nonzero on the whole region. -/
def pairContinuationWithPolesOfOpenSubset
    (hi : A.IsIrreducible) (hA : A.IsAdmissible)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hsub : D ⊆ pairFullDomainRegion χ K hK x.val x.property y.val A)
    (hD : IsOpen D) (hne : D.Nonempty) :
    Σ p : PairContinuation χ hG K hK x.val x.property hxK y.val y.property hyK hδ A D hsub,
      RationalOperatorPolePresentation (parameterScheme χ) p.denominator p.numerator := by
  let hL := parameterScheme_isConnectedReductive χ hG
  let σ := SmoothRep.pullback (parameterHomeomorph χ) A
  have hσ : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation (parameterHomeomorph χ)).mpr hi
  have hσadm : σ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (parameterHomeomorph χ) hA
  let P : ContinuedPair χ hG K hK x.val x.property hxK y.val y.property hyK A :=
    ⟨hδ, D, hD, hne, hsub, rationalOperatorContinuation (parameterScheme χ)
      (parameterProjection_continuous χ) hL hD hne subset_rfl _
      (pairCompactRationalOn_of_isOpen_subset hG χ x.val y.val x.property y.property a ha
        K hK hxK hyK hδ A hA (SmoothRep.hasFiniteLength_of_isIrreducible hi) hsub hD)⟩
  let b := galleryPQDiscriminant hG ha x y σ hσ hσadm
  refine ⟨P.presentation, RationalOperatorPolePresentation.ofClearedZeroFibers (parameterScheme χ)
    hL P.presentation hD hne b.scalar b.factors ?_⟩
  intro q z hz hzero
  have hTwist := intrinsicGalleryCoefficient_twist χ A z
  exact compactPairNumerator_eq_zero_of_PQRegular hG ha K hK x y hxK hyK A P q z
    (hTwist.symm ▸ b.regular z hz) hzero

end Langlands.Plancherel.DynamicCommonLeviContinuation
