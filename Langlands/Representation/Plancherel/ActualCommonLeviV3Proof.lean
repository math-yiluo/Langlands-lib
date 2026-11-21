import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericPoles
import Langlands.Representation.Plancherel.ActualCommonLeviV3ScalarProduct
import Langlands.Representation.Plancherel.ActualCommonLeviV3SquareIntegrableData
import Langlands.Representation.Plancherel.DynamicCommonLeviClearedOperator
import Langlands.Representation.Plancherel.DynamicCommonLeviPQDiscriminant
import Langlands.Representation.Plancherel.DynamicSquareIntegrableGalleryProduct
import Langlands.Representation.Plancherel.RationalOperatorPolesFromZeroFibers
import Langlands.Representation.Plancherel.RationalRankOneProductDifferences

/-! # The closed common-Levi V.3.1 proof -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open DynamicCommonLeviPresentations DynamicOppositeCanonicalScalar
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily
open ValuationKernelCoordinates

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
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

local notation "H" => parameterScheme χ
local notation "hp" => DynamicOppositeCanonicalScalar.parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
local notation "L" => rationalUnramifiedFunctionField H hp hL
local notation "Data" => GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A
local notation "Choices(" d ")" =>
  genericComparisonDataOfSquareIntegrable χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K hsq hi d
local notation "D[" d "]" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A (d).forward (d).reverse
local notation "J[" d "]" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A (d).forward (d).reverse
local notation "Pole[" p "]" => RationalOperatorPolePresentation H (p).denominator (p).numerator
include hsq hi in
set_option maxHeartbeats 2200000 in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actualInverseScalarProduct (d : Data)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ H} (ha : IsSplitComponent a) :
    ∃ charts : List (RankOneTranslationChart H),
      HasDenseRankOneProduct H hL charts
        (algebraMap R L d.scalarInverse.scalarDenominator / algebraMap R L d.scalarInverse.scalarNumerator) := by
  let B := A.contragredient
  let hcof := compactOpenCofinal_of_nonarchimedean (levi χ)
  have hB : B.IsIrreducible := (SmoothRep.isIrreducible_contragredient_iff hcof A hsq.1).mpr hi
  let : B.representation.IsIrreducible := hB
  let : Nontrivial B := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi χ)) B.representation.asModule
  have hsqB : IsSquareIntegrableModCentralSubgroup C hC B.representation qMeasure :=
    HarishChandraSchwartz.IsSquareIntegrableModCentralSubgroup.smoothContragredient C hC qMeasure hcof hsq
  let x : GalleryVertex χ := ⟨ψ, hψ⟩
  let y : GalleryVertex χ := ⟨ψ', hψ'⟩
  obtain ⟨charts, κ, O, factors, hOd, hOo, hInv, hScalar⟩ :=
    hasDenseRepresentedGalleryProduct_of_squareIntegrable hG ha B hB C hC qMeasure hsqB K hK x y
  let s := d.scalarInverse
  let scale := continuedCompositeGalleryScale hG ha K hK B x y hψK hψ'K s.forwardDual d.reverse
  have hscale : (scale.val : ℂ) ≠ 0 := by exact_mod_cast scale.property.1.ne'
  let u := Units.mk0 (scale.val : ℂ) hscale
  refine ⟨charts, hasDenseRankOneProduct_inverseScalar χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A d charts
    ⟨u * κ, O, factors, hOd, hOo, hInv, ?_⟩⟩
  intro z hz
  let w : ↥(s.forwardDual.regularRegion ∩ d.reverse.regularRegion) :=
    ⟨z.val⁻¹, s.forward_regular z, z.property.choose.2⟩
  obtain ⟨hF, hR, hJ⟩ := hScalar w.val hz
  have hTwist := intrinsicGalleryCoefficient_twist χ B w.val
  have hComposite := scale.property.2 w (hTwist.symm ▸ hF) (hTwist.symm ▸ hR)
    ((κ : ℂ) * (factors.map (fun g => g w.val)).prod) (hTwist.symm ▸ hJ)
  have hCoeff :
      (scale.val : ℂ) * ((κ : ℂ) * (factors.map (fun g => g w.val)).prod) =
        ((u * κ : ℂˣ) : ℂ) * (factors.map (fun g => g w.val)).prod :=
    (mul_assoc _ _ _).symm
  exact hComposite.trans (congrArg (fun c : ℂ => c • LinearMap.id) hCoeff)

local notation "first" => (⟨ψ, hψ⟩ : GalleryVertex χ)
local notation "last" => (⟨ψ', hψ'⟩ : GalleryVertex χ)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
private def actualPairPolePresentation
    (B : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K B)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ H} (ha : IsSplitComponent a)
    (hB : B.IsIrreducible) (hadm : B.IsAdmissible) : Pole[p.presentation] := by
  let σ := SmoothRep.pullback (parameterHomeomorph χ) B
  have hσ : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff B.representation (parameterHomeomorph χ)).mpr hB
  have hσadm : σ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv B.representation (parameterHomeomorph χ) hadm
  let b := galleryPQDiscriminant hG ha first last σ hσ hσadm
  refine RationalOperatorPolePresentation.ofClearedZeroFibers H hL p.presentation
    p.isOpen_region p.nonempty_region b.scalar b.factors ?_
  intro q z hz hzero
  have hTwist := intrinsicGalleryCoefficient_twist χ B z
  exact compactPairNumerator_eq_zero_of_PQRegular hG ha K hK first last hψK hψ'K B p q z
    (hTwist.symm ▸ b.regular z hz) hzero

set_option maxHeartbeats 2200000 in
/-- Waldspurger V.3.1 for the actual common-Levi comparison at every unitary parameter. -/
theorem closedV31 :
    ClosedV31Statement χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK ψ' hψ' hψ'K := by
  rintro ⟨T, a, ha, hcenter⟩
  let d : Data := Choices(⟨T, a, ha, hcenter⟩)
  let hcof := compactOpenCofinal_of_nonarchimedean (levi χ)
  have hiDual : A.contragredient.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff hcof A hsq.1).mpr hi
  have haDual : A.contragredient.IsAdmissible :=
    (SmoothRep.isAdmissible_contragredient_iff hcof A).mpr hsq.1
  let P := actualPairPolePresentation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A d.forward ha hi hsq.1
  let Q := actualPairPolePresentation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
    A.contragredient d.scalarInverse.forwardDual ha hiDual haDual
  obtain ⟨charts, hprod⟩ := actualInverseScalarProduct χ hG A C hC qMeasure hsq hi
    K hK ψ hψ hψK ψ' hψ' hψ'K d ha
  obtain ⟨O, hO, hne, hsub, _, _⟩ := d.hasDense.2.2.2
  let c : RationalOperatorContinuationData D[d] J[d] :=
    rationalOperatorContinuation H hp hL hO hne hsub J[d] d.rational
  obtain ⟨z, hz⟩ := d.hasDense.1
  have ha : d.scalarInverse.scalarDenominator ≠ 0 := by
    intro h
    exact d.scalarInverse.denominator_nonzero ⟨z, hz⟩ (by rw [h]; rfl)
  have hb : d.scalarInverse.scalarNumerator ≠ 0 := by
    intro h
    exact d.scalarInverse.numerator_nonzero ⟨z, hz⟩ (by rw [h]; rfl)
  let r := RankOneScalarPolePresentation.ofDenseRankOneProduct H hL charts
    d.scalarInverse.scalarDenominator d.scalarInverse.scalarNumerator ha hb hprod
  let S := compactComparisonPolePresentation χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K
    d.forward d.reverse d.scalarInverse c d.hasDense.2.1 P Q r.numerator r.denominator r.factors r.cross
  let T := comparisonFamilyOfGenericPoles χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K d c S hsq hi
  refine ⟨d.forward, d.reverse, ⟨d.scalarInverse⟩, d.hasDense, d.rational, T, ?_⟩
  exact comparisonFamilyOfGenericPoles_spec χ hG A C hC qMeasure K hK ψ hψ hψK ψ' hψ' hψ'K d c S hsq hi

end Langlands.Plancherel.ActualCommonLeviV3
