import Langlands.Representation.Plancherel.ActualCommonLeviIwasawaScale
import Langlands.Representation.Plancherel.ActualCommonLeviTestAverage

/-! # The integral of the common test on either actual quotient -/

noncomputable section

set_option maxHeartbeats 1100000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Plancherel.ActualCommonLeviIwasawa

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
  DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
  Langlands.Aubert.General Langlands.QuotientIntegration Langlands.Haar
  LeviInvariantIwasawaExchange StandardIntertwining StandardIntertwining.OrderedSubgroupFactorization

private theorem lintegral_lintegral_const_mul {X Y : Type u} [MeasurableSpace X]
    [MeasurableSpace Y] (μX : Measure X) (μY : Measure Y) (f : X → Y → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    (∫⁻ x, ∫⁻ y, c * f x y ∂μY ∂μX) = c * (∫⁻ x, ∫⁻ y, f x y ∂μY ∂μX) := by
  calc
    _ = ∫⁻ x, c * (∫⁻ y, f x y ∂μY) ∂μX :=
      lintegral_congr fun x => lintegral_const_mul' c (f x) hc
    _ = _ := lintegral_const_mul' c _ hc

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

local instance testIntegralAmbientMeasurable : MeasurableSpace (RationalPoint F G.X) := borel _
local instance testIntegralAmbientBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance testIntegralAmbientSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology F G
local instance testIntegralSubgroupSecondCountable (S : Subgroup (RationalPoint F G.X)) : SecondCountableTopology S :=
  TopologicalSpace.Subtype.secondCountableTopology (S : Set (RationalPoint F G.X))
local instance testIntegralRadicalLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (radical φ) := (radical_isClosed φ).locallyCompactSpace
local instance testIntegralLeviLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (levi φ) := (levi_isClosed φ).locallyCompactSpace
local instance testIntegralIntersectionLocallyCompact (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace ((radical ψ).subgroupOf (radical φ)) :=
  ((radical_isClosed ψ).preimage continuous_subtype_val).locallyCompactSpace
local instance testIntegralIntersectionSecondCountable (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    SecondCountableTopology ((radical ψ).subgroupOf (radical φ)) :=
  TopologicalSpace.Subtype.secondCountableTopology
    ((radical ψ).subgroupOf (radical φ) : Set (radical φ))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (Q : OpenSubgroup (RationalPoint F G.X))
  (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "Γ" => RationalPoint F G.X
local notation "incl" => intersectionAmbientHom (radical ψ) (radical ψ')
local notation "lHaar" => subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)
local notation "iHaar" => pairIntersectionHaar K hK ψ ψ'

local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "ambientHaar" => RankinSelberg.normalizedCompactOpenHaar K hK
local notation "cQ" => compactLeviRadicalAverage incl Q lHaar iHaar 1
local notation "νQ" => pairQuotientMeasure K hK ψ ψ'
local notation "X" => QuotientSpace (U := radical ψ) (radical ψ')
local notation "I" => (radical ψ).subgroupOf (radical ψ')

/-- The normalized test evaluated on its actual radical quotient and the compact argument. -/
def normalizedQuotientTestAverage (k : Γ) (x : X) : ℝ≥0∞ :=
  cQ⁻¹ * compactLeviRadicalQuotientAverage Q lHaar I iHaar k x

/-- Evaluation on a representative recovers the normalized ambient test. -/
theorem normalizedQuotientTestAverage_mk (k : Γ) (u : radical ψ') :
    normalizedQuotientTestAverage χ K hK Q ψ ψ' k (leftQuotientMap _ u) =
      normalizedTestAverage χ K hK Q ψ ψ' ((u : Γ) * k) := rfl

/-- The exact extended nonnegative value of the normalized compact test integral. -/
def compactTestMass : ℝ≥0∞ :=
  cQ⁻¹ * (iwasawaCompactMass K lHaar (radicalHaar ψ' K hK) * ambientHaar (Q : Set Γ))

local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'

/-- The actual compatible quotient unfolds the test integral to its exact mass. -/
theorem lintegral_normalizedQuotientTestAverage
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (hQ : IsCompact (Q : Set Γ)) :
    ∫⁻ k in (K : Set Γ), ∫⁻ x, normalizedQuotientTestAverage χ K hK Q ψ ψ' k x
        ∂νQ ∂ambientHaar = compactTestMass χ K hK Q ψ ψ' := by
  have hscale : cQ⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (compactTestAverage_one_finite_positive χ K hK Q ψ ψ' hψ' hQ).1
  let h := commonDecomposition χ ψ' hψ'
  have hfac := OppositeIntertwiningHermitianAdjunction.exists_levi_unipotent_compact h K hψ'K
  have hclosed : IsClosed (I : Set (radical ψ')) := (hU₀).preimage continuous_subtype_val
  let f : Γ → X → ℝ≥0∞ := compactLeviRadicalQuotientAverage Q lHaar I iHaar
  have hbase : (∫⁻ k in (K : Set Γ), ∫⁻ x, f k x ∂νQ ∂ambientHaar) =
      iwasawaCompactMass K lHaar (radicalHaar ψ' K hK) * ambientHaar (Q : Set Γ) :=
    lintegral_compactLeviRadicalQuotientAverage Q lHaar h I hclosed K ambientHaar
      (radicalHaar ψ' K hK) iHaar νQ (pairQuotientMeasure_isCompatible K hK ψ ψ') hfac
  exact (lintegral_lintegral_const_mul ((ambientHaar).restrict K) νQ f cQ⁻¹ hscale).trans
    (congrArg (fun a : ℝ≥0∞ => cQ⁻¹ * a) hbase)

/-- The exact common test mass is positive and finite. -/
theorem compactTestMass_finite_positive
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ) (hQ : IsCompact (Q : Set Γ)) :
    compactTestMass χ K hK Q ψ ψ' ≠ 0 ∧ compactTestMass χ K hK Q ψ ψ' ≠ ⊤ := by
  have hc := compactTestAverage_one_finite_positive χ K hK Q ψ ψ' hψ' hQ
  have hQ0 : ambientHaar (Q : Set Γ) ≠ 0 := Q.isOpen.measure_ne_zero _ ⟨1, Q.one_mem⟩
  have hmass0 := iwasawaCompactMass_ne_zero K lHaar (radicalHaar ψ' K hK)
  have hmassT := iwasawaCompactMass_ne_top (commonDecomposition χ ψ' hψ') K lHaar
    (radicalHaar ψ' K hK) hP₁ hK (commonProjection_continuous χ ψ' hψ')
  exact ⟨mul_ne_zero (ENNReal.inv_ne_zero.mpr hc.2) (mul_ne_zero hmass0 hQ0),
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc.1) (ENNReal.mul_ne_top hmassT hQ.measure_ne_top)⟩

private theorem commonIwasawaCompactMass_eq (hG : IsConnectedReductive G)
    (hEq : Dynamic.centralizer ψ = Dynamic.centralizer ψ')
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    {M : Subgroup Γ} (hM : M = levi ψ) (μM : Measure M)
    [μM.IsHaarMeasure] [μM.IsMulRightInvariant] [SFinite μM] :
    iwasawaCompactMass K μM (radicalHaar ψ K hK) =
      iwasawaCompactMass K μM (radicalHaar ψ' K hK) := by
  subst M
  exact iwasawaCompactMass_eq K hK ψ ψ' hG hEq hψK hψ'K μM

/-- Both actual quotient integrals give the same test mass for the original K. -/
theorem compactTestMass_swap (hG : IsConnectedReductive G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ)) :
    compactTestMass χ K hK Q ψ ψ' = compactTestMass χ K hK Q ψ' ψ := by
  have hMc : levi χ = levi ψ := by simp only [levi, hψ]
  have : (lHaar).IsMulRightInvariant := isMulRightInvariant_of_modularCharacter_eq_one
    (DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ hG) _
  have hswap := compactTestAverage_swap K hK hU₀ hU₁ Q lHaar 1
  have hm := commonIwasawaCompactMass_eq K hK ψ ψ' hG (hψ.trans hψ'.symm) hψK hψ'K hMc lHaar
  exact congrArg₂ (fun a b : ℝ≥0∞ => a⁻¹ * (b * ambientHaar (Q : Set Γ))) hswap hm.symm

end Langlands.Plancherel.ActualCommonLeviIwasawa
