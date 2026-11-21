import Langlands.Representation.Plancherel.LeviRadicalCompactAverage
import Langlands.Representation.Plancherel.DynamicCommonLeviContinuation
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof

/-! # The common compact test average in the actual radical quotients -/

noncomputable section

set_option maxHeartbeats 350000
set_option quotPrecheck false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Plancherel.ActualCommonLeviIwasawa

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
  DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
  Langlands.Aubert.General Langlands.QuotientIntegration Langlands.Haar Langlands.HaarModulus
  LeviInvariantIwasawaExchange StandardIntertwining StandardIntertwining.OrderedSubgroupFactorization

/-- The two intersection carriers are identified by their ambient elements. -/
def intersectionSwap {X : Type u} [Group X] [TopologicalSpace X] (U V : Subgroup X) :
    (U.subgroupOf V) ≃ₜ* (V.subgroupOf U) where
  toFun v := ⟨⟨v.val.val, v.property⟩, v.val.property⟩
  invFun v := ⟨⟨v.val.val, v.property⟩, v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

section Swap

variable {X : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {U V M : Subgroup X}
  [MeasurableSpace (U.subgroupOf V)] [BorelSpace (U.subgroupOf V)]
  [MeasurableSpace (V.subgroupOf U)] [BorelSpace (V.subgroupOf U)]
  (K : OpenSubgroup X) (hK : IsCompact (K : Set X))
  (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X))

omit [MeasurableSpace X] [BorelSpace X] in
/-- Swapping the two intersection presentations preserves the original Haar normalization. -/
theorem intersectionSwap_measurePreserving :
    MeasurePreserving (intersectionSwap U V) (sourceIntersectionHaar K hK U V hU hV)
      (sourceIntersectionHaar K hK V U hV hU) :=
  measurePreserving_compactOpenHaarAlong K hK (intersectionAmbientHom U V)
    (intersectionAmbientHom_isClosedEmbedding U V hU hV)
    (intersectionAmbientHom V U) (intersectionAmbientHom_isClosedEmbedding V U hV hU)
    (intersectionSwap U V) (fun _ => rfl)

/-- The ambient test average is independent of the order in which the intersection is presented. -/
theorem compactTestAverage_swap [MeasurableSpace M] (Q : OpenSubgroup X)
    (μM : Measure M) (g : X) :
    compactLeviRadicalAverage (intersectionAmbientHom U V) Q μM
        (sourceIntersectionHaar K hK U V hU hV) g =
      compactLeviRadicalAverage (intersectionAmbientHom V U) Q μM
        (sourceIntersectionHaar K hK V U hV hU) g := by
  unfold compactLeviRadicalAverage
  refine lintegral_congr (fun m => ?_)
  let f (x : V.subgroupOf U) :=
    (Q : Set X).indicator (1 : X → ℝ≥0∞) ((m : X) * intersectionAmbientHom V U x * g)
  have hf : Measurable f := (measurable_one.indicator Q.isOpen.measurableSet).comp
    (((continuous_subtype_val.comp continuous_subtype_val).const_mul (m : X)).mul_const g).measurable
  let hswap := intersectionSwap_measurePreserving K hK hU hV
  change (∫⁻ x : U.subgroupOf V, f (intersectionSwap U V x)
    ∂sourceIntersectionHaar K hK U V hU hV) = ∫⁻ x, f x ∂sourceIntersectionHaar K hK V U hV hU
  rw [← lintegral_map hf hswap.measurable, hswap.map_eq]

end Swap

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  Langlands.HaarModulus.subgroupMeasurableSpace
  Langlands.HaarModulus.subgroupBorelSpace
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance testAverageAmbientMeasurable : MeasurableSpace (RationalPoint F G.X) := borel _
local instance testAverageAmbientBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance testAverageAmbientSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology F G
local instance testAverageSubgroupSecondCountable (S : Subgroup (RationalPoint F G.X)) : SecondCountableTopology S :=
  TopologicalSpace.Subtype.secondCountableTopology (S : Set (RationalPoint F G.X))
local instance testAverageRadicalLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (radical φ) := (radical_isClosed φ).locallyCompactSpace
local instance testAverageLeviLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (levi φ) := (levi_isClosed φ).locallyCompactSpace
local instance testAverageIntersectionLocallyCompact (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace ((radical ψ).subgroupOf (radical φ)) :=
  ((radical_isClosed ψ).preimage continuous_subtype_val).locallyCompactSpace
local instance testAverageIntersectionSecondCountable (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    SecondCountableTopology ((radical ψ).subgroupOf (radical φ)) :=
  TopologicalSpace.Subtype.secondCountableTopology
    ((radical ψ).subgroupOf (radical φ) : Set (radical φ))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (Q : OpenSubgroup (RationalPoint F G.X))
  (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "Γ" => RationalPoint F G.X
local notation "I" => (radical ψ).subgroupOf (radical ψ')
local notation "incl" => intersectionAmbientHom (radical ψ) (radical ψ')
local notation "lHaar" => subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)
local notation "iHaar" => pairIntersectionHaar K hK ψ ψ'

/-- Scale the common test average by the inverse of its identity value. -/
def normalizedTestAverage (g : Γ) : ℝ≥0∞ :=
  (compactLeviRadicalAverage incl Q lHaar iHaar 1)⁻¹ *
    compactLeviRadicalAverage incl Q lHaar iHaar g

variable (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)

local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hI" => ((hU₀).preimage (continuous_subtype_val : Continuous (Subtype.val : radical ψ' → Γ)))
local notation "cQ" => compactLeviRadicalAverage incl Q lHaar iHaar 1

include hψ' in
/-- The identity value of the compact test average is positive and finite. -/
theorem compactTestAverage_one_finite_positive (hQ : IsCompact (Q : Set Γ)) :
    cQ ≠ 0 ∧ cQ ≠ ⊤ := by
  rw [compactLeviRadicalAverage_one_eq_measure incl (continuous_subtype_val.comp continuous_subtype_val)]
  let B := (fun x : levi χ × I => (x.1 : Γ) * incl x.2) ⁻¹' (Q : Set Γ)
  have hBopen : IsOpen B := Q.isOpen.preimage
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))
  have hBnonempty : B.Nonempty := ⟨(1, 1), by
    change ((1 : levi χ) : Γ) * incl 1 ∈ (Q : Set Γ)
    simp only [Subgroup.coe_one, map_one, mul_one]
    exact Q.one_mem⟩
  have hBcomp : IsCompact B := by
    let e : levi χ × I → levi χ × radical ψ' := Prod.map id Subtype.val
    have he : Topology.IsClosedEmbedding e := Topology.IsClosedEmbedding.id.prodMap
      (hI).isClosedEmbedding_subtypeVal
    exact he.isCompact_preimage (isCompact_iwasawaCompactPreimage h₁ Q hP₁ hQ
      (commonProjection_continuous χ ψ' hψ'))
  exact ⟨hBopen.measure_ne_zero _ hBnonempty, hBcomp.measure_ne_top⟩

include hψ' in
/-- The compact test average is normalized to one at the identity. -/
theorem normalizedTestAverage_one (hQ : IsCompact (Q : Set Γ)) :
    normalizedTestAverage χ K hK Q ψ ψ' 1 = 1 := by
  have hc := compactTestAverage_one_finite_positive χ K hK Q ψ ψ' hψ' hQ
  exact ENNReal.inv_mul_cancel hc.1 hc.2

/-- The Levi conjugation on the forward operator's intersection carrier. -/
def intersectionConj (m : levi χ) : I ≃ₜ* I :=
  subgroupAutomorphism I (normalizerConj (radical ψ') ⟨m, (h₁).levi_le_normalizer m.property⟩)
    (intersection_conj_invariant h₀ (radical ψ') (h₁).levi_le_normalizer m)

/-- On a Levi, intersection, and compact factorization, the normalized test
average is exactly the intersection conjugation modulus. -/
theorem normalizedTestAverage_factor
    (hG : IsConnectedReductive G) (hQ : IsCompact (Q : Set Γ)) (m : levi χ) (x : I) (q : Q) :
    normalizedTestAverage χ K hK Q ψ ψ' ((m : Γ) * incl x * (q : Γ)) =
      (mulEquivHaarChar (intersectionConj χ ψ ψ' hψ hψ' m) : ℝ≥0∞) := by
  let φ := intersectionConj χ ψ ψ' hψ hψ' m
  have hφ (s : I) : incl (φ.symm s) = (m : Γ)⁻¹ * incl s * m := rfl
  have hc := compactTestAverage_one_finite_positive χ K hK Q ψ ψ' hψ' hQ
  have : (iHaar).IsMulRightInvariant := pairIntersectionHaar_rightInvariant K hK ψ ψ'
  have : (lHaar).IsMulRightInvariant := isMulRightInvariant_of_modularCharacter_eq_one
    (DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ hG) _
  unfold normalizedTestAverage
  rw [compactLeviRadicalAverage_mul_right incl Q lHaar iHaar q.property,
    compactLeviRadicalAverage_levi_mul incl
      (continuous_subtype_val.comp continuous_subtype_val) Q lHaar iHaar m φ hφ,
    ← mul_one (incl x), compactLeviRadicalAverage_radical_mul incl
      (continuous_subtype_val.comp continuous_subtype_val) Q lHaar iHaar x 1]
  change cQ⁻¹ * ((mulEquivHaarChar φ : ℝ≥0∞) * cQ) = _
  rw [mul_left_comm, ENNReal.inv_mul_cancel hc.1 hc.2, mul_one]

include hψ hψ' in
/-- The normalized test average vanishes outside the Levi-intersection-compact product. -/
theorem normalizedTestAverage_eq_zero {g : Γ}
    (hg : ¬∃ (m : levi χ) (x : I) (q : Q), g = (m : Γ) * incl x * (q : Γ)) :
    normalizedTestAverage χ K hK Q ψ ψ' g = 0 := by
  unfold normalizedTestAverage
  rw [compactLeviRadicalAverage_eq_zero incl Q lHaar iHaar (fun m x => ?_) hg, mul_zero]
  refine ⟨(intersectionConj χ ψ ψ' hψ hψ' m).symm x, ?_⟩
  change incl x * (m : Γ) = (m : Γ) * ((m : Γ)⁻¹ * incl x * m)
  group

end Langlands.Plancherel.ActualCommonLeviIwasawa
