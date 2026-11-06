import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2Continuity
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2FiniteAverage
import Langlands.Automorphic.GroupSchemeFullAEL2FiniteAverage

/-! # Compact open averaging on the almost-everywhere cuspidal `L²` subspace of `[G]` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus
open Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)

section Canonical

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

local notation "μ" => quotientHaarMeasure F G S j
local notation "Sq" => quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT
local notation "ρc" => quotientFullAEL2CuspidalRightAction F G hPD hG h hi hc hT hInv'

/-- The cuspidal right action on `[G]`, restricted along the inclusion of the finite adelic
points. -/
def quotientFullAEL2CuspidalFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) Sq :=
  (ρc).comp (AdelicGroupPoints.ofFinite F G).toMonoidHom

@[simp]
theorem quotientFullAEL2CuspidalFiniteRightAction_apply (b : FiniteAdelicGroupPoints F G)
    (φ : Sq) :
    quotientFullAEL2CuspidalFiniteRightAction F G hPD hG h hi hc hT hInv' b φ =
      ρc (AdelicGroupPoints.ofFinite F G b) φ :=
  rfl

variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G))

/-- The bounded cuspidal action restricted to an open subgroup of the finite adelic points. -/
def quotientFullAEL2CuspidalCompactOpenAction : K →* (Sq →L[ℂ] Sq) :=
  (quotientFullAEL2CuspidalBoundedRightAction F G hPD hG h hi hc hT hInv').comp
    ((AdelicGroupPoints.ofFinite F G).toMonoidHom.comp K.toSubgroup.subtype)

local notation "πK" =>
  quotientFullAEL2CuspidalCompactOpenAction F G hPD hG h hi hc hT hInv' K

@[simp]
theorem quotientFullAEL2CuspidalCompactOpenAction_apply (k : K) (φ : Sq) :
    πK k φ = ρc (AdelicGroupPoints.ofFinite F G k) φ :=
  rfl

theorem norm_quotientFullAEL2CuspidalCompactOpenAction (k : K) (φ : Sq) :
    ‖πK k φ‖ = ‖φ‖ :=
  norm_quotientFullAEL2CuspidalBoundedRightAction F G hPD hG h hi hc hT hInv' _ φ

/-- Each cuspidal orbit of the open subgroup is continuous for the subgroup topology. -/
theorem continuous_quotientFullAEL2CuspidalCompactOpenOrbit (φ : Sq) :
    Continuous (fun k : K => πK k φ) :=
  (quotientFullAEL2CuspidalOrbitMap F G hPD hG h hi hc hT hInv' φ).continuous.comp
    ((AdelicGroupPoints.ofFinite F G).continuous.comp continuous_subtype_val)

variable [CompactSpace K]

attribute [local instance] finiteAverageTopologicalGroup finiteAverageSecondCountable
  finiteAverageMeasurableSpace finiteAverageBorelSpace

local notation "μK" => compactProbabilityHaar K
local notation "hπKnorm" =>
  norm_quotientFullAEL2CuspidalCompactOpenAction F G hPD hG h hi hc hT hInv' K
local notation "hπKcont" =>
  continuous_quotientFullAEL2CuspidalCompactOpenOrbit F G hPD hG h hi hc hT hInv' K

/-- Averaging cuspidal vectors over the normalized Haar probability measure of a compact open
subgroup `K`. -/
def quotientFullAEL2CuspidalFiniteAverage : Sq →L[ℂ] Sq :=
  compactIsometricAverage K πK hπKnorm hπKcont

local notation "P" => quotientFullAEL2CuspidalFiniteAverage F G hPD hG h hi hc hT hInv' K

@[simp]
theorem quotientFullAEL2CuspidalFiniteAverage_apply (φ : Sq) :
    P φ = ∫ k : K, ρc (AdelicGroupPoints.ofFinite F G k) φ ∂μK :=
  compactIsometricAverage_apply K πK hπKnorm hπKcont φ

/-- The orbit of `K` is Bochner integrable for every cuspidal vector. -/
theorem quotientFullAEL2CuspidalFiniteAverage_integrable (φ : Sq) :
    Integrable (fun k : K => ρc (AdelicGroupPoints.ofFinite F G k) φ) μK :=
  compactIsometricOrbit_integrable K πK hπKnorm hπKcont φ

theorem norm_quotientFullAEL2CuspidalFiniteAverage_le : ‖P‖ ≤ 1 :=
  norm_compactIsometricAverage_le K πK hπKnorm hπKcont

/-- Every output is fixed by every element of `K`. -/
theorem quotientFullAEL2CuspidalFiniteAverage_fixed (k : K) (φ : Sq) :
    ρc (AdelicGroupPoints.ofFinite F G k) (P φ) = P φ :=
  compactIsometricAverage_fixed K πK hπKnorm hπKcont k φ

/-- The average fixes exactly the `K`-invariant cuspidal vectors. -/
theorem quotientFullAEL2CuspidalFiniteAverage_eq_self_iff (φ : Sq) :
    P φ = φ ↔ ∀ k : K, ρc (AdelicGroupPoints.ofFinite F G k) φ = φ :=
  compactIsometricAverage_eq_self_iff K πK hπKnorm hπKcont φ

theorem quotientFullAEL2CuspidalFiniteAverage_idempotent : (P).comp P = P :=
  compactIsometricAverage_idempotent K πK hπKnorm hπKcont

/-- Every output lies in the `K`-fixed vectors of the finite cuspidal action. -/
theorem quotientFullAEL2CuspidalFiniteAverage_mem_fixedVectors (φ : Sq) :
    P φ ∈ Langlands.fixedVectors
      (quotientFullAEL2CuspidalFiniteRightAction F G hPD hG h hi hc hT hInv') K.toSubgroup :=
  fun k => quotientFullAEL2CuspidalFiniteAverage_fixed F G hPD hG h hi hc hT hInv' K k φ

/-- Every output is a smooth vector of the finite cuspidal action. -/
theorem quotientFullAEL2CuspidalFiniteAverage_isSmoothVector (φ : Sq) :
    Langlands.IsSmoothVector
      (quotientFullAEL2CuspidalFiniteRightAction F G hPD hG h hi hc hT hInv') (P φ) :=
  ⟨K, quotientFullAEL2CuspidalFiniteAverage_mem_fixedVectors F G hPD hG h hi hc hT hInv' K φ⟩

/-- The average, with codomain the `K`-fixed cuspidal vectors. -/
def quotientFullAEL2CuspidalFiniteFixedRetraction :
    Sq →L[ℂ] Langlands.fixedVectors
      (quotientFullAEL2CuspidalFiniteRightAction F G hPD hG h hi hc hT hInv') K.toSubgroup :=
  (P).codRestrict _
    (quotientFullAEL2CuspidalFiniteAverage_mem_fixedVectors F G hPD hG h hi hc hT hInv' K)

@[simp]
theorem quotientFullAEL2CuspidalFiniteFixedRetraction_val (φ : Sq) :
    (quotientFullAEL2CuspidalFiniteFixedRetraction F G hPD hG h hi hc hT hInv' K φ).val =
      P φ :=
  rfl

@[simp]
theorem quotientFullAEL2CuspidalFiniteFixedRetraction_inclusion
    (φ : Langlands.fixedVectors
      (quotientFullAEL2CuspidalFiniteRightAction F G hPD hG h hi hc hT hInv') K.toSubgroup) :
    quotientFullAEL2CuspidalFiniteFixedRetraction F G hPD hG h hi hc hT hInv' K φ.val = φ := by
  apply Subtype.ext
  exact (quotientFullAEL2CuspidalFiniteAverage_eq_self_iff F G hPD hG h hi hc hT hInv' K
    φ.val).mpr φ.property

local notation "A" => rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K
local notation "πA" =>
  rationalQuotientL2CompactOpenAction F G (quotientHaarMeasure F G S j) hInv' K
local notation "hπAnorm" =>
  norm_rationalQuotientL2CompactOpenAction F G (quotientHaarMeasure F G S j) hInv' K
local notation "hπAcont" => continuous_rationalQuotientL2CompactOpenOrbit F G h hi hc hT hInv' K

/-- The inclusion of the cuspidal subspace carries the cuspidal average to the average on
`L²([G])`. -/
theorem quotientFullAEL2CuspidalFiniteAverage_val (ψ : Sq) :
    (P ψ).val = A ψ.val :=
  compactIsometricAverage_intertwiner K πK hπKnorm hπKcont πA hπAnorm hπAcont
    (quotientFullAEL2CuspidalInclusionLI F G hPD hG h hi hc hT).toContinuousLinearMap
    (fun _ _ => rfl) ψ

/-- The average on `L²([G])` preserves the cuspidal subspace. -/
theorem rationalQuotientL2FiniteAverage_mem_quotientFullAEL2CuspidalSubmodule
    (φ : Lp ℂ 2 μ) (hφ : φ ∈ Sq) : A φ ∈ Sq := by
  rw [← quotientFullAEL2CuspidalFiniteAverage_val F G hPD hG h hi hc hT hInv' K ⟨φ, hφ⟩]
  exact (P ⟨φ, hφ⟩).property

/-- The orthogonal projection onto the cuspidal subspace intertwines the two averages. -/
theorem quotientFullAEL2CuspidalOrthogonalProjection_finiteAverage (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT (A φ) =
      P (quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT φ) :=
  compactIsometricAverage_intertwiner K πA hπAnorm hπAcont πK hπKnorm hπKcont
    (quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT)
    (fun k ψ => quotientFullAEL2CuspidalOrthogonalProjection_rightAction F G hPD hG h hi hc hT
      hInv' (AdelicGroupPoints.ofFinite F G k) ψ) φ

/-- The ambient orthogonal projection onto the cuspidal subspace commutes with the average on
`L²([G])`. -/
theorem quotientFullAEL2CuspidalAmbientProjection_finiteAverage (φ : Lp ℂ 2 μ) :
    quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT (A φ) =
      A (quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT φ) :=
  (congrArg Subtype.val
    (quotientFullAEL2CuspidalOrthogonalProjection_finiteAverage F G hPD hG h hi hc hT hInv' K
      φ)).trans
    (quotientFullAEL2CuspidalFiniteAverage_val F G hPD hG h hi hc hT hInv' K _)

end Canonical

section Comparison

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]

/-- The isometric isomorphism `fullAEL2CuspidalEquiv` carries the published positive-torus
cuspidal finite average to the cuspidal finite average on `[G]`. -/
theorem fullAEL2CuspidalEquiv_finiteAverage
    (φ : fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc) :
    fullAEL2CuspidalEquiv F G hPD hG h hi I e hc
        (fullAEL2CuspidalFiniteAverage F G hPD hG T i hi I e hc K φ) =
      quotientFullAEL2CuspidalFiniteAverage F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩ hInv' K
        (fullAEL2CuspidalEquiv F G hPD hG h hi I e hc φ) :=
  Subtype.ext ((congrArg (quotientL2Equiv F G h)
    (fullAEL2CuspidalFiniteAverage_val F G hPD hG T i hi I e hc K φ)).trans
      ((quotientL2Equiv_finiteAverage F G h hi hc ⟨I, inferInstance, ⟨e⟩⟩ hInv' K I e
        φ.val).trans
        (quotientFullAEL2CuspidalFiniteAverage_val F G hPD hG h hi hc ⟨I, inferInstance, ⟨e⟩⟩
          hInv' K (fullAEL2CuspidalEquiv F G hPD hG h hi I e hc φ)).symm))

end Comparison

section SplitComponents

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]

local notation "hInvS" => quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs
local notation "hS" => subgroup_eq_of_splitComponents F G hj hs
local notation "Ss" => splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs

/-- For split components, averaging cuspidal vectors over a compact open subgroup `K`. -/
def splitComponentFullAEL2CuspidalFiniteAverage : Ss →L[ℂ] Ss :=
  quotientFullAEL2CuspidalFiniteAverage F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS K

/-- Forgetting the subtype recovers the published split-component average on `L²([G])`. -/
theorem splitComponentFullAEL2CuspidalFiniteAverage_val (φ : Ss) :
    (splitComponentFullAEL2CuspidalFiniteAverage F G hPD hG hi hj hs K φ).val =
      splitComponentL2FiniteAverage F G hi K hj hs φ.val :=
  quotientFullAEL2CuspidalFiniteAverage_val F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS K φ

theorem norm_splitComponentFullAEL2CuspidalFiniteAverage_le :
    ‖splitComponentFullAEL2CuspidalFiniteAverage F G hPD hG hi hj hs K‖ ≤ 1 :=
  norm_quotientFullAEL2CuspidalFiniteAverage_le F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS K

/-- For split components, every output is a smooth vector of the finite cuspidal action. -/
theorem splitComponentFullAEL2CuspidalFiniteAverage_isSmoothVector (φ : Ss) :
    Langlands.IsSmoothVector
      (quotientFullAEL2CuspidalFiniteRightAction F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS)
      (splitComponentFullAEL2CuspidalFiniteAverage F G hPD hG hi hj hs K φ) :=
  quotientFullAEL2CuspidalFiniteAverage_isSmoothVector F G hPD hG hS hi hs.1.2 hs.1.1.1 hInvS K
    φ

/-- For split components, the orthogonal cuspidal projection intertwines the two averages. -/
theorem splitComponentFullAEL2CuspidalOrthogonalProjection_finiteAverage
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    splitComponentFullAEL2CuspidalOrthogonalProjection F G hPD hG hi hj hs
        (splitComponentL2FiniteAverage F G hi K hj hs φ) =
      splitComponentFullAEL2CuspidalFiniteAverage F G hPD hG hi hj hs K
        (splitComponentFullAEL2CuspidalOrthogonalProjection F G hPD hG hi hj hs φ) :=
  quotientFullAEL2CuspidalOrthogonalProjection_finiteAverage F G hPD hG hS hi hs.1.2 hs.1.1.1
    hInvS K φ

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
