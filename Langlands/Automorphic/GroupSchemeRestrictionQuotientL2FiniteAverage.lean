import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2Continuity
import Langlands.Automorphic.GroupSchemeRestrictionCuspidalL2
import Langlands.Automorphic.GroupSchemeQuotientL2FiniteAverage

/-! # Compact open averaging on `L²` of the restriction split-centre quotient `[G]` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
variable {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

section Finite

variable (measureQ : Measure (Quotient F G S j))
variable (hInv : QuotientRightInvariant F G measureQ)

@[simp]
theorem rationalQuotientL2FiniteRightAction_apply (b : FiniteAdelicGroupPoints F G)
    (φ : Lp ℂ 2 measureQ) :
    rationalQuotientL2FiniteRightAction F G measureQ hInv b φ =
      rationalQuotientL2RightAction F G measureQ hInv (AdelicGroupPoints.ofFinite F G b) φ :=
  rfl

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G))

/-- The bounded right action restricted to an open subgroup of the finite adelic points. -/
def rationalQuotientL2CompactOpenAction : K →* (Lp ℂ 2 measureQ →L[ℂ] Lp ℂ 2 measureQ) :=
  (rationalQuotientL2BoundedRightAction F G measureQ hInv).comp
    ((AdelicGroupPoints.ofFinite F G).toMonoidHom.comp K.toSubgroup.subtype)

@[simp]
theorem rationalQuotientL2CompactOpenAction_apply (k : K) (φ : Lp ℂ 2 measureQ) :
    rationalQuotientL2CompactOpenAction F G measureQ hInv K k φ =
      rationalQuotientL2RightAction F G measureQ hInv (AdelicGroupPoints.ofFinite F G k) φ :=
  rfl

theorem norm_rationalQuotientL2CompactOpenAction (k : K) (φ : Lp ℂ 2 measureQ) :
    ‖rationalQuotientL2CompactOpenAction F G measureQ hInv K k φ‖ = ‖φ‖ :=
  norm_rationalQuotientL2BoundedRightAction F G measureQ hInv _ φ

end Finite

variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G))

local notation "μ" => quotientHaarMeasure F G S j
local notation "ρ" => rationalQuotientL2RightAction F G (quotientHaarMeasure F G S j) hInv'
local notation "πK" => rationalQuotientL2CompactOpenAction F G (quotientHaarMeasure F G S j) hInv' K

include h hi hc hT in
/-- Each orbit of the open subgroup is continuous for the subgroup topology. -/
theorem continuous_rationalQuotientL2CompactOpenOrbit (φ : Lp ℂ 2 μ) :
    Continuous (fun k : K => πK k φ) :=
  (rationalQuotientL2OrbitMap F G hInv' h hi hc hT φ).continuous.comp
    ((AdelicGroupPoints.ofFinite F G).continuous.comp continuous_subtype_val)

variable [CompactSpace K]

attribute [local instance] finiteAverageTopologicalGroup finiteAverageSecondCountable
  finiteAverageMeasurableSpace finiteAverageBorelSpace

local notation "μK" => compactProbabilityHaar K
local notation "hπKnorm" =>
  norm_rationalQuotientL2CompactOpenAction F G (quotientHaarMeasure F G S j) hInv' K
local notation "hπKcont" => continuous_rationalQuotientL2CompactOpenOrbit F G h hi hc hT hInv' K

/-- Averaging over the normalized Haar probability measure of a compact open subgroup `K`. -/
def rationalQuotientL2FiniteAverage : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  compactIsometricAverage K πK hπKnorm hπKcont

local notation "P" => rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K

@[simp]
theorem rationalQuotientL2FiniteAverage_apply (φ : Lp ℂ 2 μ) :
    P φ = ∫ k : K, ρ (AdelicGroupPoints.ofFinite F G k) φ ∂μK :=
  compactIsometricAverage_apply K πK hπKnorm hπKcont φ

include h hi hc hT in
/-- The orbit of `K` is Bochner integrable for every `L²` class. -/
theorem rationalQuotientL2FiniteAverage_integrable (φ : Lp ℂ 2 μ) :
    Integrable (fun k : K => ρ (AdelicGroupPoints.ofFinite F G k) φ) μK :=
  compactIsometricOrbit_integrable K πK hπKnorm hπKcont φ

theorem norm_rationalQuotientL2FiniteAverage_le : ‖P‖ ≤ 1 :=
  norm_compactIsometricAverage_le K πK hπKnorm hπKcont

/-- Every output is fixed by every element of `K`. -/
theorem rationalQuotientL2FiniteAverage_fixed (k : K) (φ : Lp ℂ 2 μ) :
    ρ (AdelicGroupPoints.ofFinite F G k) (P φ) = P φ :=
  compactIsometricAverage_fixed K πK hπKnorm hπKcont k φ

/-- The average fixes exactly the `K`-invariant vectors. -/
theorem rationalQuotientL2FiniteAverage_eq_self_iff (φ : Lp ℂ 2 μ) :
    P φ = φ ↔ ∀ k : K, ρ (AdelicGroupPoints.ofFinite F G k) φ = φ :=
  compactIsometricAverage_eq_self_iff K πK hπKnorm hπKcont φ

theorem rationalQuotientL2FiniteAverage_idempotent : (P).comp P = P :=
  compactIsometricAverage_idempotent K πK hπKnorm hπKcont

/-- Every output lies in the `K`-fixed vectors of the finite right action. -/
theorem rationalQuotientL2FiniteAverage_mem_fixedVectors (φ : Lp ℂ 2 μ) :
    P φ ∈ Langlands.fixedVectors (rationalQuotientL2FiniteRightAction F G μ hInv')
      K.toSubgroup :=
  fun k => rationalQuotientL2FiniteAverage_fixed F G h hi hc hT hInv' K k φ

/-- Every output is a smooth vector of the finite right action. -/
theorem rationalQuotientL2FiniteAverage_isSmoothVector (φ : Lp ℂ 2 μ) :
    Langlands.IsSmoothVector (rationalQuotientL2FiniteRightAction F G μ hInv') (P φ) :=
  ⟨K, rationalQuotientL2FiniteAverage_mem_fixedVectors F G h hi hc hT hInv' K φ⟩

/-- The average, with codomain the `K`-fixed vectors. -/
def rationalQuotientL2FiniteFixedRetraction :
    Lp ℂ 2 μ →L[ℂ]
      Langlands.fixedVectors (rationalQuotientL2FiniteRightAction F G μ hInv') K.toSubgroup :=
  (P).codRestrict _ (rationalQuotientL2FiniteAverage_mem_fixedVectors F G h hi hc hT hInv' K)

@[simp]
theorem rationalQuotientL2FiniteFixedRetraction_val (φ : Lp ℂ 2 μ) :
    (rationalQuotientL2FiniteFixedRetraction F G h hi hc hT hInv' K φ).val = P φ := rfl

@[simp]
theorem rationalQuotientL2FiniteFixedRetraction_inclusion
    (φ : Langlands.fixedVectors (rationalQuotientL2FiniteRightAction F G μ hInv')
      K.toSubgroup) :
    rationalQuotientL2FiniteFixedRetraction F G h hi hc hT hInv' K φ.val = φ := by
  apply Subtype.ext
  exact (rationalQuotientL2FiniteAverage_eq_self_iff F G h hi hc hT hInv' K φ.val).mpr
    φ.property

/-- `quotientL2Equiv` carries the published positive-torus finite average to the finite average
on `[G]`. -/
theorem quotientL2Equiv_finiteAverage (I : Type) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientL2Equiv F G h (haarQuotientL2FiniteAverage F G T i hi I e hc K φ) =
      P (quotientL2Equiv F G h φ) := by
  rw [haarQuotientL2FiniteAverage_apply, rationalQuotientL2FiniteAverage_apply]
  calc quotientL2Equiv F G h (∫ k : K, quotientL2RightAction F G T i _
        (haarQuotientMeasureRightInvariant F G T i hi I e hc)
          (AdelicGroupPoints.ofFinite F G k) φ ∂μK)
      = ∫ k : K, quotientL2Equiv F G h (quotientL2RightAction F G T i _
          (haarQuotientMeasureRightInvariant F G T i hi I e hc)
            (AdelicGroupPoints.ofFinite F G k) φ) ∂μK :=
        ((quotientL2Equiv F G h).toLinearIsometry.integral_comp_comm _).symm
    _ = ∫ k : K, ρ (AdelicGroupPoints.ofFinite F G k) (quotientL2Equiv F G h φ) ∂μK := by
        congr 1
        funext k
        exact quotientL2Equiv_rightAction F G h
          (haarQuotientMeasureRightInvariant F G T i hi I e hc) hInv' _ φ

section SplitComponents

variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)

local notation "hInvS" => quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs
local notation "hS" => subgroup_eq_of_splitComponents F G hj hs

/-- For split components, averaging over a compact open subgroup `K`. -/
def splitComponentL2FiniteAverage :
    Lp ℂ 2 (quotientHaarMeasure F G S j) →L[ℂ] Lp ℂ 2 (quotientHaarMeasure F G S j) :=
  rationalQuotientL2FiniteAverage F G hS hi hs.1.2 hs.1.1.1 hInvS K

theorem splitComponentL2FiniteAverage_apply (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    splitComponentL2FiniteAverage F G hi K hj hs φ =
      ∫ k : K, splitComponentL2RightAction F G hi hj hs (AdelicGroupPoints.ofFinite F G k) φ
        ∂(compactProbabilityHaar K) :=
  rationalQuotientL2FiniteAverage_apply F G hS hi hs.1.2 hs.1.1.1 hInvS K φ

theorem norm_splitComponentL2FiniteAverage_le :
    ‖splitComponentL2FiniteAverage F G hi K hj hs‖ ≤ 1 :=
  norm_rationalQuotientL2FiniteAverage_le F G hS hi hs.1.2 hs.1.1.1 hInvS K

/-- For split components, the average fixes exactly the `K`-invariant vectors. -/
theorem splitComponentL2FiniteAverage_eq_self_iff (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    splitComponentL2FiniteAverage F G hi K hj hs φ = φ ↔
      ∀ k : K, splitComponentL2RightAction F G hi hj hs (AdelicGroupPoints.ofFinite F G k) φ = φ :=
  rationalQuotientL2FiniteAverage_eq_self_iff F G hS hi hs.1.2 hs.1.1.1 hInvS K φ

/-- For split components, every output is a smooth vector of the finite right action. -/
theorem splitComponentL2FiniteAverage_isSmoothVector
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    Langlands.IsSmoothVector
      (rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInvS)
      (splitComponentL2FiniteAverage F G hi K hj hs φ) :=
  rationalQuotientL2FiniteAverage_isSmoothVector F G hS hi hs.1.2 hs.1.1.1 hInvS K φ

/-- For split components, `splitComponentL2Equiv` carries the published positive-torus finite
average, for any splitting coordinates of `T`, to `splitComponentL2FiniteAverage`. -/
theorem splitComponentL2Equiv_finiteAverage (I : Type) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    splitComponentL2Equiv F G hj hs (haarQuotientL2FiniteAverage F G T i hi I e hs.1.2 K φ) =
      splitComponentL2FiniteAverage F G hi K hj hs (splitComponentL2Equiv F G hj hs φ) :=
  quotientL2Equiv_finiteAverage F G hS hi hs.1.2 hs.1.1.1 hInvS K I e φ

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
