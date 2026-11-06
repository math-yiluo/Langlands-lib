import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2

/-! # Joint continuity and Bochner integration of the restriction quotient L2 action -/

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

section Bounded

variable (measureQ : Measure (Quotient F G S j))
variable (hInv : QuotientRightInvariant F G measureQ)

/-- The right regular representation on `L²` of the restriction quotient, bundled by bounded
linear maps. -/
def rationalQuotientL2BoundedRightAction :
    AdelicGroupPoints F G →* (Lp ℂ 2 measureQ →L[ℂ] Lp ℂ 2 measureQ) where
  toFun g := (rationalQuotientL2RightTranslate F G measureQ hInv g).toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    exact rationalQuotientL2RightTranslate_one F G measureQ hInv
  map_mul' g g' := by
    apply ContinuousLinearMap.ext
    exact rationalQuotientL2RightTranslate_mul F G measureQ hInv g g'

@[simp]
theorem rationalQuotientL2BoundedRightAction_apply (g : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 measureQ) :
    rationalQuotientL2BoundedRightAction F G measureQ hInv g φ =
      rationalQuotientL2RightAction F G measureQ hInv g φ := rfl

theorem norm_rationalQuotientL2BoundedRightAction (g : AdelicGroupPoints F G)
    (φ : Lp ℂ 2 measureQ) :
    ‖rationalQuotientL2BoundedRightAction F G measureQ hInv g φ‖ = ‖φ‖ :=
  (rationalQuotientL2RightTranslate F G measureQ hInv g).norm_map φ

end Bounded

variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

local notation "μG" => quotientHaarMeasure F G S j
local notation "ρG" => rationalQuotientL2RightAction F G (quotientHaarMeasure F G S j) hInv'

section Transport

variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (I : Type) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc

/-- On the canonical restriction quotient measure, the right action is the conjugate of the
published positive-torus right action by `quotientL2Equiv`. -/
theorem rationalQuotientL2RightAction_eq_quotientL2Equiv
    (h : subgroup F G S j = imageSubgroup F T G i) (g : AdelicGroupPoints F G) (φ : Lp ℂ 2 μG) :
    ρG g φ = quotientL2Equiv F G h
      (quotientL2RightAction F G T i μQ hR g ((quotientL2Equiv F G h).symm φ)) := by
  rw [quotientL2Equiv_rightAction F G h hR hInv' g, LinearIsometryEquiv.apply_symm_apply]

include hi I e hc in
/-- The restriction quotient right action is jointly continuous in the adelic element and the
`L²` class, for explicit split-torus data. -/
theorem continuous_rationalQuotientL2RightAction_of_splitData
    (h : subgroup F G S j = imageSubgroup F T G i) :
    Continuous fun gφ : AdelicGroupPoints F G × Lp ℂ 2 μG => ρG gφ.1 gφ.2 := by
  have hfun : (fun gφ : AdelicGroupPoints F G × Lp ℂ 2 μG => ρG gφ.1 gφ.2) =
      fun gφ => quotientL2Equiv F G h (haarQuotientL2JointRightAction F G T i hi I e hc
        (gφ.1, (quotientL2Equiv F G h).symm gφ.2)) :=
    funext fun gφ =>
      rationalQuotientL2RightAction_eq_quotientL2Equiv F G hInv' hi I e hc h gφ.1 gφ.2
  rw [hfun]
  exact (quotientL2Equiv F G h).continuous.comp
    ((haarQuotientL2JointRightAction F G T i hi I e hc).continuous.comp
      (continuous_fst.prodMk ((quotientL2Equiv F G h).symm.continuous.comp continuous_snd)))

end Transport

variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)

include h hi hc hT in
/-- The restriction quotient right action is jointly continuous in the adelic element and the
`L²` class. -/
theorem continuous_rationalQuotientL2RightAction :
    Continuous fun gφ : AdelicGroupPoints F G × Lp ℂ 2 μG => ρG gφ.1 gφ.2 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  exact continuous_rationalQuotientL2RightAction_of_splitData F G hInv' hi I e hc h

/-- The restriction quotient `L²` action, continuous jointly in the adelic element and the
`L²` class. -/
def rationalQuotientL2JointRightAction :
    C(AdelicGroupPoints F G × Lp ℂ 2 μG, Lp ℂ 2 μG) where
  toFun gφ := ρG gφ.1 gφ.2
  continuous_toFun := continuous_rationalQuotientL2RightAction F G hInv' h hi hc hT

@[simp]
theorem rationalQuotientL2JointRightAction_apply (g : AdelicGroupPoints F G) (φ : Lp ℂ 2 μG) :
    rationalQuotientL2JointRightAction F G hInv' h hi hc hT (g, φ) = ρG g φ := rfl

/-- The continuous orbit map of an `L²` class on the restriction quotient. -/
def rationalQuotientL2OrbitMap (φ : Lp ℂ 2 μG) : C(AdelicGroupPoints F G, Lp ℂ 2 μG) :=
  (rationalQuotientL2JointRightAction F G hInv' h hi hc hT).comp
    ⟨fun g => (g, φ), continuous_id.prodMk continuous_const⟩

@[simp]
theorem rationalQuotientL2OrbitMap_apply (φ : Lp ℂ 2 μG) (g : AdelicGroupPoints F G) :
    rationalQuotientL2OrbitMap F G hInv' h hi hc hT φ g = ρG g φ := rfl

local notation "πG" => rationalQuotientL2BoundedRightAction F G (quotientHaarMeasure F G S j) hInv'
local notation "hπGnorm" =>
  norm_rationalQuotientL2BoundedRightAction F G (quotientHaarMeasure F G S j) hInv'

section Integrated

variable (ν : Measure (AdelicGroupPoints F G))

include h hi hc hT in
/-- Orbits on the restriction quotient are strongly measurable for every supplied group
measure. -/
theorem rationalQuotientL2Orbit_aestronglyMeasurable (φ : Lp ℂ 2 μG) :
    AEStronglyMeasurable (fun g => πG g φ) ν :=
  (rationalQuotientL2OrbitMap F G hInv' h hi hc hT φ).continuous.stronglyMeasurable
    |>.aestronglyMeasurable

local notation "hπGmeas" => rationalQuotientL2Orbit_aestronglyMeasurable F G hInv' h hi hc hT ν

variable (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)

include h hi hc hT hf in
/-- Absolute Bochner convergence of the weighted orbit on the restriction quotient. -/
theorem rationalQuotientL2ActionIntegrand_integrable (φ : Lp ℂ 2 μG) :
    Integrable (fun g => f g • ρG g φ) ν :=
  isometricActionIntegrand_integrable ν πG hπGnorm hπGmeas f hf φ

/-- The weighted right action `φ ↦ ∫ f(g) R(g) φ dν(g)` on `L²` of the restriction
quotient. -/
def rationalQuotientL2IntegratedAction : Lp ℂ 2 μG →L[ℂ] Lp ℂ 2 μG :=
  integratedIsometricAction ν πG hπGnorm hπGmeas f hf

@[simp]
theorem rationalQuotientL2IntegratedAction_apply (φ : Lp ℂ 2 μG) :
    rationalQuotientL2IntegratedAction F G hInv' h hi hc hT ν f hf φ =
      ∫ g, f g • ρG g φ ∂ν := rfl

theorem norm_rationalQuotientL2IntegratedAction_le :
    ‖rationalQuotientL2IntegratedAction F G hInv' h hi hc hT ν f hf‖ ≤ ∫ g, ‖f g‖ ∂ν :=
  integratedIsometricAction_norm_le ν πG hπGnorm hπGmeas f hf

/-- `quotientL2Equiv` intertwines the published integrated positive-torus action with the
integrated restriction quotient action. -/
theorem quotientL2Equiv_integratedAction (I : Type) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientL2Equiv F G h (haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf φ) =
      rationalQuotientL2IntegratedAction F G hInv' h hi hc hT ν f hf (quotientL2Equiv F G h φ) := by
  rw [haarQuotientL2IntegratedAction_apply, rationalQuotientL2IntegratedAction_apply]
  calc quotientL2Equiv F G h (∫ g, f g • quotientL2RightAction F G T i _
        (haarQuotientMeasureRightInvariant F G T i hi I e hc) g φ ∂ν)
      = ∫ g, quotientL2Equiv F G h (f g • quotientL2RightAction F G T i _
          (haarQuotientMeasureRightInvariant F G T i hi I e hc) g φ) ∂ν :=
        ((quotientL2Equiv F G h).toLinearIsometry.integral_comp_comm _).symm
    _ = ∫ g, f g • ρG g (quotientL2Equiv F G h φ) ∂ν := by
        congr 1
        funext g
        rw [LinearIsometryEquiv.map_smul, quotientL2Equiv_rightAction F G h
          (haarQuotientMeasureRightInvariant F G T i hi I e hc) hInv' g]

end Integrated

section SplitComponents

variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)

local notation "hInvS" => quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs
local notation "hS" => subgroup_eq_of_splitComponents F G hj hs

/-- For split components, `splitComponentL2RightAction` is jointly continuous in the adelic
element and the `L²` class. -/
theorem continuous_splitComponentL2RightAction :
    Continuous fun gφ : AdelicGroupPoints F G × Lp ℂ 2 μG =>
      splitComponentL2RightAction F G hi hj hs gφ.1 gφ.2 :=
  continuous_rationalQuotientL2RightAction F G hInvS hS hi hs.1.2 hs.1.1.1

/-- The split-component `L²` action as a jointly continuous map. -/
def splitComponentL2JointRightAction :
    C(AdelicGroupPoints F G × Lp ℂ 2 μG, Lp ℂ 2 μG) :=
  rationalQuotientL2JointRightAction F G hInvS hS hi hs.1.2 hs.1.1.1

@[simp]
theorem splitComponentL2JointRightAction_apply (g : AdelicGroupPoints F G) (φ : Lp ℂ 2 μG) :
    splitComponentL2JointRightAction F G hi hj hs (g, φ) =
      splitComponentL2RightAction F G hi hj hs g φ := rfl

/-- The split-component `L²` action bundled by bounded linear maps. -/
def splitComponentL2BoundedRightAction :
    AdelicGroupPoints F G →* (Lp ℂ 2 μG →L[ℂ] Lp ℂ 2 μG) :=
  rationalQuotientL2BoundedRightAction F G μG hInvS

@[simp]
theorem splitComponentL2BoundedRightAction_apply (g : AdelicGroupPoints F G) (φ : Lp ℂ 2 μG) :
    splitComponentL2BoundedRightAction F G hi hj hs g φ =
      splitComponentL2RightAction F G hi hj hs g φ := rfl

variable (ν : Measure (AdelicGroupPoints F G))
variable (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f ν)

/-- The weighted split-component action `φ ↦ ∫ f(g) R(g) φ dν(g)`. -/
def splitComponentL2IntegratedAction : Lp ℂ 2 μG →L[ℂ] Lp ℂ 2 μG :=
  rationalQuotientL2IntegratedAction F G hInvS hS hi hs.1.2 hs.1.1.1 ν f hf

@[simp]
theorem splitComponentL2IntegratedAction_apply (φ : Lp ℂ 2 μG) :
    splitComponentL2IntegratedAction F G hi hj hs ν f hf φ =
      ∫ g, f g • splitComponentL2RightAction F G hi hj hs g φ ∂ν := rfl

theorem norm_splitComponentL2IntegratedAction_le :
    ‖splitComponentL2IntegratedAction F G hi hj hs ν f hf‖ ≤ ∫ g, ‖f g‖ ∂ν :=
  norm_rationalQuotientL2IntegratedAction_le F G hInvS hS hi hs.1.2 hs.1.1.1 ν f hf

/-- For split components, `splitComponentL2Equiv` intertwines the published integrated
positive-torus action with `splitComponentL2IntegratedAction`. -/
theorem splitComponentL2Equiv_integratedAction (I : Type) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (φ : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    splitComponentL2Equiv F G hj hs
        (haarQuotientL2IntegratedAction F G T i hi I e hs.1.2 ν f hf φ) =
      splitComponentL2IntegratedAction F G hi hj hs ν f hf (splitComponentL2Equiv F G hj hs φ) :=
  quotientL2Equiv_integratedAction F G hInvS hS hi hs.1.2 hs.1.1.1 ν f hf I e φ

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
