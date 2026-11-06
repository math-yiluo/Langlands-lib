import Langlands.Automorphic.GroupSchemeTensorCuspidalL2
import Langlands.Automorphic.GroupSchemeRestrictionCuspidalL2

/-! # Tensor-smooth cusp forms in `L²` of the restriction split-centre quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
variable (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)

local instance restrictionTensorCuspFiniteSmoothAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

section Tensor

/-- Continuous quotient functions whose pullback is tensor smooth. -/
def quotientTensorSubrepresentation :
    Subrepresentation (continuousQuotientFiniteRightAction F G S j) where
  toSubmodule := (tensorSmoothSubrepresentation F G).toSubmodule.comap
    (quotientContinuousPullback F G S j)
  apply_mem_toSubmodule c f hf := by
    change quotientContinuousPullback F G S j
      (continuousQuotientRightAction F G S j (AdelicGroupPoints.ofFinite F G c) f) ∈
        (tensorSmoothSubrepresentation F G).toSubmodule
    rw [quotientContinuousPullback_rightAction]
    exact (tensorSmoothSubrepresentation F G).apply_mem_toSubmodule
      (AdelicGroupPoints.ofFinite F G c) hf

theorem mem_quotientTensorSubrepresentation (f : C(Quotient F G S j, ℂ)) :
    f ∈ quotientTensorSubrepresentation F G S j ↔
      quotientContinuousPullback F G S j f ∈ tensorSmoothSubrepresentation F G :=
  Iff.rfl

end Tensor

section TensorCuspForms

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)

variable {S j}
variable (measureQ : Measure (Quotient F G S j)) (hInv : QuotientRightInvariant F G measureQ)

/-- Continuous square-integrable `AdelicCuspidalForms` quotient functions whose pullback is
tensor smooth. -/
def quotientTensorCuspidalFormL2Subrepresentation :
    Subrepresentation (continuousQuotientFiniteRightAction F G S j) :=
  quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv ⊓
    quotientTensorSubrepresentation F G S j

abbrev QuotientTensorCuspidalFormL2Functions :=
  (quotientTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv).toSubmodule

def quotientTensorCuspidalFormL2FiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv) :=
  (quotientTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv).toRepresentation

/-- The pullback is the continuous function of a `TensorAdelicCuspidalForms` element and the
function is square integrable. -/
theorem mem_quotientTensorCuspidalFormL2Subrepresentation (f : C(Quotient F G S j, ℂ)) :
    f ∈ quotientTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK
        hN measureQ hInv ↔
      (∃ phi : TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN,
        tensorAdelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi =
          quotientContinuousPullback F G S j f) ∧ MemLp f 2 measureQ := by
  constructor
  · rintro ⟨⟨⟨phi, hphi⟩, hlp⟩, htensor⟩
    have ht : phi.val.val ∈ tensorSmoothSubrepresentation F G := by
      change quotientContinuousPullback F G S j f ∈ tensorSmoothSubrepresentation F G at htensor
      rw [← hphi] at htensor
      exact htensor
    let psi : TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN :=
      ⟨phi.val, ⟨⟨phi.property.1, ht⟩, phi.property.2⟩⟩
    exact ⟨⟨psi, hphi⟩, hlp⟩
  · rintro ⟨⟨phi, hphi⟩, hlp⟩
    refine ⟨⟨⟨tensorAdelicCuspidalToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi,
      hphi⟩, hlp⟩, ?_⟩
    change quotientContinuousPullback F G S j f ∈ tensorSmoothSubrepresentation F G
    rw [← hphi]
    exact phi.property.1.2

/-- Forgetting tensor smoothness keeps the same continuous function. -/
def quotientTensorCuspidalFormL2ToCuspidal :
    (quotientTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv).IntertwiningMap
      (quotientCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv) where
  toLinearMap :=
    (quotientTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv).toSubmodule.inclusion (fun _ hf => hf.1)
  isIntertwining' _ := by ext; rfl

/-- Pass square-integrable continuous tensor cusp-form functions to their `L²` classes. -/
def quotientTensorCuspidalFormL2ToLp :
    (quotientTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv).IntertwiningMap (rationalQuotientL2FiniteRightAction F G measureQ hInv) :=
  (quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv).comp
    (quotientTensorCuspidalFormL2ToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv)

theorem coeFn_quotientTensorCuspidalFormL2ToLp
    (f : QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv) :
    quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f
      =ᵐ[measureQ] (f.val : Quotient F G S j → ℂ) :=
  coeFn_quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv
    (quotientTensorCuspidalFormL2ToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv f)

theorem quotientTensorCuspidalFormL2ToLp_injective [measureQ.IsOpenPosMeasure] :
    Function.Injective
      (quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv) := by
  intro f f' h
  have he := quotientCuspidalFormL2ToLp_injective F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv h
  exact Subtype.ext (congrArg
    (fun z : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv => z.val) he)

/-- The algebraic image of square-integrable continuous tensor cusp-form functions.
No closure is asserted. -/
def quotientTensorCuspidalFormL2Image :
    Subrepresentation (rationalQuotientL2FiniteRightAction F G measureQ hInv) :=
  (quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv).range

theorem mem_quotientTensorCuspidalFormL2Image (φ : Lp ℂ 2 measureQ) :
    φ ∈ quotientTensorCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv ↔
      ∃ f : QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
          measureQ hInv,
        quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
          measureQ hInv f = φ :=
  Iff.rfl

/-- The tensor image lies in the `AdelicCuspidalForms` image. -/
theorem quotientTensorCuspidalFormL2Image_le :
    (quotientTensorCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv).toSubmodule ≤
      (quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv).toSubmodule := by
  rintro φ ⟨f, rfl⟩
  exact ⟨quotientTensorCuspidalFormL2ToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv f, rfl⟩

end TensorCuspForms

section Comparison

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)

theorem continuousQuotientEquiv_mem_tensor_iff (f : C(PositiveRationalQuotient F G T i, ℂ)) :
    continuousQuotientEquiv F G h f ∈ quotientTensorSubrepresentation F G S j ↔
      f ∈ tensorPositiveQuotientSubrepresentation F G T i := by
  change quotientContinuousPullback F G S j (continuousQuotientEquiv F G h f) ∈
      tensorSmoothSubrepresentation F G ↔
    positiveQuotientContinuousPullback F G T i f ∈ tensorSmoothSubrepresentation F G
  rw [quotientContinuousPullback_continuousQuotientEquiv]

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)
variable (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
  (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

theorem continuousQuotientEquiv_mem_tensorCuspidalFormL2_iff
    (f : C(PositiveRationalQuotient F G T i, ℂ)) :
    continuousQuotientEquiv F G h f ∈ quotientTensorCuspidalFormL2Subrepresentation F G Kinf rho
        hsmooth hcalc hPD hG hrho hK hN (quotientHaarMeasure F G S j) hInv' ↔
      f ∈ positiveTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK
        hN T i (positiveRationalQuotientHaarMeasure F G T i) hInv :=
  and_congr
    (continuousQuotientEquiv_mem_cuspidalFormL2_iff F G h Kinf rho hsmooth hcalc hPD hG hrho hK
      hN hInv hInv' f)
    (continuousQuotientEquiv_mem_tensor_iff F G h f)

/-- The continuous square-integrable tensor cusp-form functions on the two quotients
correspond. -/
def tensorCuspidalFormL2FunctionsEquiv :
    PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        (positiveRationalQuotientHaarMeasure F G T i) hInv ≃ₗ[ℂ]
      QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (quotientHaarMeasure F G S j) hInv' where
  toFun f := ⟨continuousQuotientEquiv F G h f.val,
    (continuousQuotientEquiv_mem_tensorCuspidalFormL2_iff F G h Kinf rho hsmooth hcalc hPD hG
      hrho hK hN hInv hInv' f.val).mpr f.property⟩
  invFun f := ⟨(continuousQuotientEquiv F G h).symm f.val,
    (continuousQuotientEquiv_mem_tensorCuspidalFormL2_iff F G h Kinf rho hsmooth hcalc hPD hG
      hrho hK hN hInv hInv' _).mp (by rw [LinearEquiv.apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((continuousQuotientEquiv F G h).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousQuotientEquiv F G h).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousQuotientEquiv F G h) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousQuotientEquiv F G h) _ _)

theorem tensorCuspidalFormL2FunctionsEquiv_finiteRightAction (c : FiniteAdelicGroupPoints F G)
    (f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      (positiveRationalQuotientHaarMeasure F G T i) hInv) :
    tensorCuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv hInv'
        (positiveTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK
          hN T i _ hInv c f) =
      quotientTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        _ hInv' c
        (tensorCuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
          hInv' f) :=
  Subtype.ext (continuousQuotientEquiv_rightAction F G h (AdelicGroupPoints.ofFinite F G c) f.val)

/-- The tensor cusp-form correspondence is `quotientL2Equiv` on `L²` classes. -/
theorem quotientTensorCuspidalFormL2ToLp_tensorCuspidalFormL2FunctionsEquiv
    (f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      (positiveRationalQuotientHaarMeasure F G T i) hInv) :
    quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv'
        (tensorCuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
          hInv' f) =
      quotientL2Equiv F G h
        (positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _
          hInv f) :=
  quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG
    hrho hK hN hInv hInv'
    (positiveTensorCuspidalFormL2ToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _
      hInv f)

/-- `quotientL2Equiv` carries the positive-torus tensor cusp-form image onto the
restriction-quotient image. -/
theorem mem_quotientTensorCuspidalFormL2Image_iff (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ quotientTensorCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv' ↔
      (quotientL2Equiv F G h).symm φ ∈
        tensorCuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _
          hInv := by
  have hR : (quotientL2Equiv F G h).symm φ ∈
      tensorCuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _
        hInv ↔
        ∃ f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
            T i (positiveRationalQuotientHaarMeasure F G T i) hInv,
          positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _
            hInv f = (quotientL2Equiv F G h).symm φ :=
    Iff.rfl
  refine (mem_quotientTensorCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _
    hInv' φ).trans (Iff.trans ?_ hR.symm)
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨(tensorCuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN
      hInv hInv').symm f, ?_⟩
    apply (quotientL2Equiv F G h).injective
    rw [LinearIsometryEquiv.apply_symm_apply,
      ← quotientTensorCuspidalFormL2ToLp_tensorCuspidalFormL2FunctionsEquiv]
    exact congrArg
      (fun z => quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _
        hInv' z)
      ((tensorCuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
        hInv').apply_symm_apply f)
  · rintro ⟨f, hf⟩
    refine ⟨tensorCuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN
      hInv hInv' f, ?_⟩
    rw [quotientTensorCuspidalFormL2ToLp_tensorCuspidalFormL2FunctionsEquiv, hf,
      LinearIsometryEquiv.apply_symm_apply]

end Comparison

section SplitComponents

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)

/-- For split components, the image of square-integrable continuous tensor cusp-form functions
in `L²` of the restriction quotient with its canonical measure. -/
def splitComponentTensorCuspidalFormL2Image :
    Subrepresentation (rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j)
      (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)) :=
  quotientTensorCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _
    (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)

/-- For split components, distinct continuous tensor cusp-form functions give distinct `L²`
classes. -/
theorem quotientTensorCuspidalFormL2ToLp_injective_of_splitComponents :
    Function.Injective (quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho
      hK hN (quotientHaarMeasure F G S j)
      (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)) := by
  let := quotientHaarMeasure_isOpenPosMeasure_of_splitComponents F G hi hj hs
  exact quotientTensorCuspidalFormL2ToLp_injective F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    _ _

/-- For split components, `splitComponentL2Equiv` carries the positive-torus tensor cusp-form
image onto `splitComponentTensorCuspidalFormL2Image`. -/
theorem mem_splitComponentTensorCuspidalFormL2Image_iff
    (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ splitComponentTensorCuspidalFormL2Image F G hi hj hs Kinf rho hsmooth hcalc hPD hG hrho
        hK hN ↔
      (splitComponentL2Equiv F G hj hs).symm φ ∈
        tensorCuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _
          hInv :=
  mem_quotientTensorCuspidalFormL2Image_iff F G _ Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv _
    φ

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
