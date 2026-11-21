import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericData
import Langlands.Representation.Plancherel.RationalRankOneProductDifferences

/-! # The actual inverse scalar from a dual gallery product -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
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
  ambientMeasurable ambientBorel
  leviLocallyCompact parabolicLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (d : GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)

local notation "H" => parameterScheme χ
local notation "hH" => parameterScheme_isConnectedReductive χ hG
local notation "hp" => DynamicOppositeCanonicalScalar.parameterProjection_continuous χ
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
local notation "L" => rationalUnramifiedFunctionField H hp hH
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A d.forward d.reverse

/-- A dense gallery product for the two actual compact dual operators.
The constant absorbs their fixed Haar scales. -/
def HasDenseDualCompositeRankOneProduct (charts : List (RankOneTranslationChart H)) : Prop :=
  ∃ (κ : ℂˣ) (O : Set X) (factors : List (X → ℂ)),
    Dense O ∧ IsOpen O ∧ List.Forall₂ (fun chart g => chart.InvariantOn H O g) charts factors ∧
    ∀ z : D, z.val⁻¹ ∈ O →
      (d.reverse.presentation.continuedOperator ⟨z.val⁻¹, z.property.choose.2⟩).comp
        (d.scalarInverse.forwardDual.presentation.continuedOperator
          ⟨z.val⁻¹, d.scalarInverse.forward_regular z⟩) =
        ((κ : ℂ) * (factors.map (fun g => g z.val⁻¹)).prod) • LinearMap.id

omit hG K hK ψ hψ hψK ψ' hψ' hψ'K A d in
private theorem complementParameter_inv (chart : RankOneTranslationChart H)
    (c : Fin chart.complementRank → ℂˣ) :
    complementParameter chart.coordinates (fun i => (c i)⁻¹) =
      (complementParameter chart.coordinates c)⁻¹ := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro m
  change (complementParameter chart.coordinates (fun i => (c i)⁻¹)).val m =
    ((complementParameter chart.coordinates c).val m)⁻¹
  simp only [complementParameter_apply, inv_zpow, Finset.prod_inv_distrib]

/-- The dual composite product at the inverse parameter gives a dense
rank-one product for the exact reciprocal fraction of the comparison. -/
theorem hasDenseRankOneProduct_inverseScalar [Nontrivial A.contragredient]
    (charts : List (RankOneTranslationChart H))
    (hprod : HasDenseDualCompositeRankOneProduct χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A d charts) :
    HasDenseRankOneProduct H hH charts
      (algebraMap R L d.scalarInverse.scalarDenominator / algebraMap R L d.scalarInverse.scalarNumerator) := by
  obtain ⟨κ, O, factors, hOd, hOo, hinv, heq⟩ := hprod
  obtain ⟨S, hSo, _, hSD, hSd, _⟩ := d.hasDense.2.2.2
  let inversion : X ≃ₜ X := Homeomorph.inv X
  let T := S ∩ inversion ⁻¹' O
  have hTo : IsOpen T := hSo.inter (hOo.preimage inversion.continuous)
  have hTd : Dense T := hSd.inter_of_isOpen_right
    (inversion.isOpenQuotientMap.dense_preimage_iff.mpr hOd) (hOo.preimage inversion.continuous)
  let s := d.scalarInverse
  have hscaled : HasDenseRankOneProduct H hH charts
      (algebraMap R L s.scalarNumerator / algebraMap R L s.scalarDenominator) := by
    refine ⟨s.scalarNumerator, s.scalarDenominator, κ, T,
      factors.map (fun g z => g z⁻¹), rfl, hTd, hTo, ?_, ?_⟩
    · rw [List.forall₂_map_right_iff]
      refine hinv.imp (fun chart g hg c z hz ht => ?_)
      have htranslate : complementParameter chart.coordinates (fun i => (c i)⁻¹) * z⁻¹ =
          (complementParameter chart.coordinates c * z)⁻¹ := by
        rw [complementParameter_inv χ chart c, mul_inv]
      exact (congrArg g htranslate).symm.trans (hg _ z⁻¹ hz.2 (htranslate ▸ ht.2))
    · intro z hz
      let w : D := ⟨z, hSD hz.1⟩
      refine ⟨s.numerator_nonzero w, s.denominator_nonzero w, ?_⟩
      have h := (s.reverse_forward w).symm.trans (heq w hz.2)
      obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp
        (continuedPair_continuedOperator_ne_zero χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
          A.contragredient s.forwardDual ⟨z⁻¹, s.forward_regular w⟩)
      have hv0 : v ≠ 0 := by
        rintro rfl
        exact hv (LinearMap.map_zero _)
      have ht := smul_left_injective ℂ hv0 (LinearMap.congr_fun h v)
      simp only [List.map_map, Function.comp_def]
      exact ht
  simpa only [inv_div] using hscaled.inv H hH

end Langlands.Plancherel.ActualCommonLeviV3
