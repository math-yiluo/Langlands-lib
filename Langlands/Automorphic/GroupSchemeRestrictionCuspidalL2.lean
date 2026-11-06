import Langlands.Automorphic.GroupSchemeCuspidalFormL2
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2

/-! # Parabolic vanishing and `AdelicCuspidalForms` in `L²` of the restriction split-centre
quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
variable (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)

section Continuous

/-- Positive right pullback on continuous functions on the restriction quotient. -/
def continuousQuotientRightAction :
    Representation ℂ (AdelicGroupPoints F G) C(Quotient F G S j, ℂ) where
  toFun g :=
    { toFun f := f.comp ⟨LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g,
        LeftCosetSpace.continuous_rightTranslate (rationalSubgroup F G S j) g⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro q
    exact congrArg f (LeftCosetSpace.rightTranslate_one (rationalSubgroup F G S j) q)
  map_mul' g g' := by
    apply LinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro q
    exact congrArg f (LeftCosetSpace.rightTranslate_mul (rationalSubgroup F G S j) g g' q).symm

@[simp] theorem continuousQuotientRightAction_apply (g : AdelicGroupPoints F G)
    (f : C(Quotient F G S j, ℂ)) (q : Quotient F G S j) :
    continuousQuotientRightAction F G S j g f q =
      f (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g q) := rfl

/-- Pullback to actual adelic points gives a continuous rational-invariant function. -/
def quotientContinuousPullback :
    C(Quotient F G S j, ℂ) →ₗ[ℂ] ContinuousRationalFunctions F G where
  toFun f :=
    ⟨⟨fun x => f (LeftCosetSpace.mk (rationalSubgroup F G S j) x), by
      intro q x
      exact congrArg f (LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G S j)
        ⟨AdelicGroupPoints.rational F G q, principal_le_rationalSubgroup F G S j ⟨q, rfl⟩⟩ x)⟩,
      f.continuous.comp (LeftCosetSpace.continuous_mk (rationalSubgroup F G S j))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem quotientContinuousPullback_apply (f : C(Quotient F G S j, ℂ))
    (x : AdelicGroupPoints F G) :
    (quotientContinuousPullback F G S j f).val.val x =
      f (LeftCosetSpace.mk (rationalSubgroup F G S j) x) := rfl

theorem quotientContinuousPullback_injective :
    Function.Injective (quotientContinuousPullback F G S j) := by
  intro f f' h
  apply ContinuousMap.ext
  intro q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F G S j) q
  exact congrArg (fun f : ContinuousRationalFunctions F G => f.val.val x) h

/-- The pullback intertwines the quotient action with positive right translation upstairs. -/
theorem quotientContinuousPullback_rightAction (g : AdelicGroupPoints F G)
    (f : C(Quotient F G S j, ℂ)) :
    quotientContinuousPullback F G S j (continuousQuotientRightAction F G S j g f) =
      continuousRightAction F G g (quotientContinuousPullback F G S j f) :=
  rfl

end Continuous

section Parabolic

variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))

/-- Pull back actual all-parabolic vanishing along the restriction quotient projection. -/
def quotientParabolicCuspidalSubrepresentation :
    Subrepresentation (continuousQuotientRightAction F G S j) where
  toSubmodule := (parabolicCuspidalSubrepresentation F G hPD hG measuresU).toSubmodule.comap
    (quotientContinuousPullback F G S j)
  apply_mem_toSubmodule g f hf := by
    change quotientContinuousPullback F G S j (continuousQuotientRightAction F G S j g f) ∈
      (parabolicCuspidalSubrepresentation F G hPD hG measuresU).toSubmodule
    rw [quotientContinuousPullback_rightAction]
    exact (parabolicCuspidalSubrepresentation F G hPD hG measuresU).apply_mem_toSubmodule g hf

@[simp]
theorem mem_quotientParabolicCuspidalSubrepresentation (f : C(Quotient F G S j, ℂ)) :
    f ∈ quotientParabolicCuspidalSubrepresentation F G S j hPD hG measuresU ↔
      quotientContinuousPullback F G S j f ∈
        parabolicCuspidalSubrepresentation F G hPD hG measuresU := Iff.rfl

end Parabolic

section L2

variable {S j}
variable (measureQ : Measure (Quotient F G S j))

/-- Continuous square-integrable functions on the restriction quotient. -/
def quotientContinuousL2Submodule : Submodule ℂ C(Quotient F G S j, ℂ) where
  carrier := {f | MemLp f 2 measureQ}
  zero_mem' := MemLp.zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

@[simp] theorem mem_quotientContinuousL2Submodule (f : C(Quotient F G S j, ℂ)) :
    f ∈ quotientContinuousL2Submodule F G measureQ ↔ MemLp f 2 measureQ := Iff.rfl

/-- The complex-linear map to almost-everywhere classes. -/
def quotientContinuousL2ToLp :
    quotientContinuousL2Submodule F G measureQ →ₗ[ℂ] Lp ℂ 2 measureQ where
  toFun f := f.property.toLp f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeFn_quotientContinuousL2ToLp (f : quotientContinuousL2Submodule F G measureQ) :
    quotientContinuousL2ToLp F G measureQ f =ᵐ[measureQ] (f.val : Quotient F G S j → ℂ) :=
  MemLp.coeFn_toLp f.property

/-- Positivity on nonempty open sets makes the continuous realization faithful. -/
theorem quotientContinuousL2ToLp_injective [measureQ.IsOpenPosMeasure] :
    Function.Injective (quotientContinuousL2ToLp F G measureQ) := by
  intro f f' h
  apply Subtype.ext
  apply ContinuousMap.coe_injective
  exact Measure.eq_of_ae_eq ((MemLp.toLp_eq_toLp_iff f.property f'.property).mp h)
    f.val.continuous f'.val.continuous

variable (hInv : QuotientRightInvariant F G measureQ)

/-- Square integrability is stable under positive right translation. -/
def quotientContinuousL2Subrepresentation :
    Subrepresentation (continuousQuotientRightAction F G S j) where
  toSubmodule := quotientContinuousL2Submodule F G measureQ
  apply_mem_toSubmodule g _f hf := hf.comp_measurePreserving (hInv g)

/-- Positive right translation on continuous square-integrable functions. -/
def quotientContinuousL2RightAction :
    Representation ℂ (AdelicGroupPoints F G) (quotientContinuousL2Submodule F G measureQ) :=
  (quotientContinuousL2Subrepresentation F G measureQ hInv).toRepresentation

/-- Passing to classes intertwines continuous translation with the `L²` right action. -/
theorem quotientContinuousL2ToLp_rightAction (g : AdelicGroupPoints F G)
    (f : quotientContinuousL2Submodule F G measureQ) :
    quotientContinuousL2ToLp F G measureQ (quotientContinuousL2RightAction F G measureQ hInv g f) =
      rationalQuotientL2RightAction F G measureQ hInv g (quotientContinuousL2ToLp F G measureQ f) :=
  (Lp.toLp_compMeasurePreserving f.property (hInv g)).symm

end L2

section ParabolicL2

variable {S j}
variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))
variable (measureQ : Measure (Quotient F G S j)) (hInv : QuotientRightInvariant F G measureQ)

/-- Continuous square-integrable functions on the quotient with all-parabolic vanishing. -/
def quotientParabolicCuspidalL2Subrepresentation :
    Subrepresentation (continuousQuotientRightAction F G S j) :=
  quotientParabolicCuspidalSubrepresentation F G S j hPD hG measuresU ⊓
    quotientContinuousL2Subrepresentation F G measureQ hInv

abbrev QuotientParabolicCuspidalL2Functions :=
  (quotientParabolicCuspidalL2Subrepresentation F G hPD hG measuresU measureQ hInv).toSubmodule

def quotientParabolicCuspidalL2RightAction :
    Representation ℂ (AdelicGroupPoints F G)
      (QuotientParabolicCuspidalL2Functions F G hPD hG measuresU measureQ hInv) :=
  (quotientParabolicCuspidalL2Subrepresentation F G hPD hG measuresU measureQ hInv).toRepresentation

theorem mem_quotientParabolicCuspidalL2Subrepresentation (f : C(Quotient F G S j, ℂ)) :
    f ∈ quotientParabolicCuspidalL2Subrepresentation F G hPD hG measuresU measureQ hInv ↔
      (quotientContinuousPullback F G S j f ∈
        parabolicCuspidalSubrepresentation F G hPD hG measuresU) ∧
      MemLp f 2 measureQ := Iff.rfl

/-- Forgetting vanishing keeps the same continuous square-integrable function. -/
def quotientParabolicCuspidalL2ToContinuousL2 :
    QuotientParabolicCuspidalL2Functions F G hPD hG measuresU measureQ hInv →ₗ[ℂ]
      quotientContinuousL2Submodule F G measureQ :=
  (quotientParabolicCuspidalL2Subrepresentation F G hPD hG measuresU measureQ hInv).toSubmodule.inclusion
    (fun _ hf => hf.2)

/-- Passing to `L²` classes intertwines the right actions. -/
def quotientParabolicCuspidalL2ToLp :
    (quotientParabolicCuspidalL2RightAction F G hPD hG measuresU measureQ hInv).IntertwiningMap
      (rationalQuotientL2RightAction F G measureQ hInv) where
  toLinearMap := (quotientContinuousL2ToLp F G measureQ).comp
    (quotientParabolicCuspidalL2ToContinuousL2 F G hPD hG measuresU measureQ hInv)
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact quotientContinuousL2ToLp_rightAction F G measureQ hInv g
      (quotientParabolicCuspidalL2ToContinuousL2 F G hPD hG measuresU measureQ hInv f)

theorem coeFn_quotientParabolicCuspidalL2ToLp
    (f : QuotientParabolicCuspidalL2Functions F G hPD hG measuresU measureQ hInv) :
    quotientParabolicCuspidalL2ToLp F G hPD hG measuresU measureQ hInv f
      =ᵐ[measureQ] (f.val : Quotient F G S j → ℂ) :=
  coeFn_quotientContinuousL2ToLp F G measureQ
    (quotientParabolicCuspidalL2ToContinuousL2 F G hPD hG measuresU measureQ hInv f)

theorem quotientParabolicCuspidalL2ToLp_injective [measureQ.IsOpenPosMeasure] :
    Function.Injective (quotientParabolicCuspidalL2ToLp F G hPD hG measuresU measureQ hInv) := by
  intro f f' h
  have he := quotientContinuousL2ToLp_injective F G measureQ h
  apply Subtype.ext
  exact congrArg (fun z : quotientContinuousL2Submodule F G measureQ => z.val) he

/-- The algebraic image of continuous square-integrable all-parabolic-vanishing functions.
No closure or equality with an almost-everywhere cuspidal subspace is asserted. -/
def quotientContinuousParabolicCuspidalL2Image :
    Subrepresentation (rationalQuotientL2RightAction F G measureQ hInv) :=
  (quotientParabolicCuspidalL2ToLp F G hPD hG measuresU measureQ hInv).range

theorem mem_quotientContinuousParabolicCuspidalL2Image (φ : Lp ℂ 2 measureQ) :
    φ ∈ quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU measureQ hInv ↔
      ∃ f : QuotientParabolicCuspidalL2Functions F G hPD hG measuresU measureQ hInv,
        quotientParabolicCuspidalL2ToLp F G hPD hG measuresU measureQ hInv f = φ :=
  Iff.rfl

end ParabolicL2

section CuspForms

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)

/-- Restrict the quotient action to the finite adelic factor. -/
def continuousQuotientFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) C(Quotient F G S j, ℂ) :=
  (continuousQuotientRightAction F G S j).comp (AdelicGroupPoints.ofFinite F G).toMonoidHom

/-- The quotient pullback intertwines the finite actions. -/
def quotientFinitePullback :
    (continuousQuotientFiniteRightAction F G S j).IntertwiningMap (finiteRightAction F G) where
  toLinearMap := quotientContinuousPullback F G S j
  isIntertwining' _ := by ext; rfl

/-- Continuous quotient functions whose pullback is the continuous function of an element of
`AdelicCuspidalForms`. -/
def quotientCuspidalFormSubrepresentation :
    Subrepresentation (continuousQuotientFiniteRightAction F G S j) where
  toSubmodule := (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule.comap (quotientContinuousPullback F G S j)
  apply_mem_toSubmodule c f hf := by
    change quotientContinuousPullback F G S j
      (continuousQuotientRightAction F G S j (AdelicGroupPoints.ofFinite F G c) f) ∈
        (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule
    rw [quotientContinuousPullback_rightAction]
    exact (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).apply_mem_toSubmodule c hf

theorem mem_quotientCuspidalFormSubrepresentation (f : C(Quotient F G S j, ℂ)) :
    f ∈ quotientCuspidalFormSubrepresentation F G S j Kinf rho hsmooth hcalc hPD hG hrho hK hN ↔
      ∃ phi : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN,
        adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi =
          quotientContinuousPullback F G S j f := Iff.rfl

variable {S j}
variable (measureQ : Measure (Quotient F G S j)) (hInv : QuotientRightInvariant F G measureQ)

/-- Square integrability, restricted to the finite adelic action. -/
def quotientContinuousFiniteL2Subrepresentation :
    Subrepresentation (continuousQuotientFiniteRightAction F G S j) where
  toSubmodule := quotientContinuousL2Submodule F G measureQ
  apply_mem_toSubmodule c _f hf :=
    hf.comp_measurePreserving (hInv (AdelicGroupPoints.ofFinite F G c))

/-- Continuous square-integrable quotient functions represented by `AdelicCuspidalForms`. -/
def quotientCuspidalFormL2Subrepresentation :
    Subrepresentation (continuousQuotientFiniteRightAction F G S j) :=
  quotientCuspidalFormSubrepresentation F G S j Kinf rho hsmooth hcalc hPD hG hrho hK hN ⊓
    quotientContinuousFiniteL2Subrepresentation F G measureQ hInv

abbrev QuotientCuspidalFormL2Functions :=
  (quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv).toSubmodule

def quotientCuspidalFormL2FiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv) :=
  (quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv).toRepresentation

theorem mem_quotientCuspidalFormL2Subrepresentation (f : C(Quotient F G S j, ℂ)) :
    f ∈ quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv ↔
      (∃ phi : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN,
        adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi =
          quotientContinuousPullback F G S j f) ∧ MemLp f 2 measureQ := Iff.rfl

/-- Forgetting the form condition keeps the same continuous function. -/
def quotientCuspidalFormL2ToContinuousL2 :
    QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv
      →ₗ[ℂ] quotientContinuousL2Submodule F G measureQ :=
  (quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    measureQ hInv).toSubmodule.inclusion (fun _ hf => hf.2)

/-- The `L²` right action on the restriction quotient restricted to the finite factor. -/
def rationalQuotientL2FiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) (Lp ℂ 2 measureQ) :=
  (rationalQuotientL2RightAction F G measureQ hInv).comp
    (AdelicGroupPoints.ofFinite F G).toMonoidHom

/-- Pass square-integrable continuous `AdelicCuspidalForms` functions to their `L²` classes. -/
def quotientCuspidalFormL2ToLp :
    (quotientCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv).IntertwiningMap (rationalQuotientL2FiniteRightAction F G measureQ hInv) where
  toLinearMap := (quotientContinuousL2ToLp F G measureQ).comp
    (quotientCuspidalFormL2ToContinuousL2 F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv)
  isIntertwining' c := by
    apply LinearMap.ext
    intro f
    exact quotientContinuousL2ToLp_rightAction F G measureQ hInv
      (AdelicGroupPoints.ofFinite F G c)
      (quotientCuspidalFormL2ToContinuousL2 F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        measureQ hInv f)

theorem coeFn_quotientCuspidalFormL2ToLp
    (f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv) :
    quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f
      =ᵐ[measureQ] (f.val : Quotient F G S j → ℂ) :=
  coeFn_quotientContinuousL2ToLp F G measureQ
    (quotientCuspidalFormL2ToContinuousL2 F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv f)

theorem quotientCuspidalFormL2ToLp_injective [measureQ.IsOpenPosMeasure] :
    Function.Injective
      (quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv) := by
  intro f f' h
  have he := quotientContinuousL2ToLp_injective F G measureQ h
  apply Subtype.ext
  exact congrArg (fun z : quotientContinuousL2Submodule F G measureQ => z.val) he

/-- The algebraic image of square-integrable continuous `AdelicCuspidalForms` functions.
No closure or equality with an almost-everywhere cuspidal subspace is asserted. -/
def quotientCuspidalFormL2Image :
    Subrepresentation (rationalQuotientL2FiniteRightAction F G measureQ hInv) :=
  (quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv).range

theorem mem_quotientCuspidalFormL2Image (φ : Lp ℂ 2 measureQ) :
    φ ∈ quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv ↔
      ∃ f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
          measureQ hInv,
        quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f =
          φ :=
  Iff.rfl

/-- `AdelicCuspidalForms` functions are continuous all-parabolic-vanishing functions for the
mass-one radical quotient measures. -/
def quotientCuspidalFormL2ToContinuousParabolic :
    QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv
      →ₗ[ℂ] QuotientParabolicCuspidalL2Functions F G hPD hG
        (properParabolicQuotientMeasure F G hPD hG) measureQ hInv where
  toFun f := ⟨f.val, by
    refine ⟨?_, f.property.2⟩
    obtain ⟨phi, hphi⟩ := f.property.1
    change quotientContinuousPullback F G S j f.val ∈
      normalizedParabolicCuspidalSubrepresentation F G hPD hG
    rw [← hphi]
    exact phi.property.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Both realizations give the same `L²` class. -/
theorem quotientCuspidalFormL2ToContinuousParabolic_toLp
    (f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      measureQ hInv) :
    quotientParabolicCuspidalL2ToLp F G hPD hG (properParabolicQuotientMeasure F G hPD hG)
        measureQ hInv
        (quotientCuspidalFormL2ToContinuousParabolic F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
          measureQ hInv f) =
      quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f :=
  rfl

end CuspForms

section Comparison

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)

/-- Continuous functions on the positive-torus quotient and on the restriction quotient,
identified by composition with the identity on representatives. -/
def continuousQuotientEquiv :
    C(PositiveRationalQuotient F G T i, ℂ) ≃ₗ[ℂ] C(Quotient F G S j, ℂ) where
  toFun f := f.comp ⟨(quotientHomeomorph F G h).symm, (quotientHomeomorph F G h).symm.continuous⟩
  invFun f := f.comp ⟨quotientHomeomorph F G h, (quotientHomeomorph F G h).continuous⟩
  left_inv f := by
    apply ContinuousMap.ext
    intro p
    exact congrArg f ((quotientHomeomorph F G h).symm_apply_apply p)
  right_inv f := by
    apply ContinuousMap.ext
    intro q
    exact congrArg f ((quotientHomeomorph F G h).apply_symm_apply q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem continuousQuotientEquiv_apply (f : C(PositiveRationalQuotient F G T i, ℂ))
    (q : Quotient F G S j) :
    continuousQuotientEquiv F G h f q = f ((quotientHomeomorph F G h).symm q) := rfl

@[simp] theorem continuousQuotientEquiv_symm_apply (f : C(Quotient F G S j, ℂ))
    (p : PositiveRationalQuotient F G T i) :
    (continuousQuotientEquiv F G h).symm f p = f (quotientHomeomorph F G h p) := rfl

/-- The two quotient pullbacks agree under the identification. -/
theorem quotientContinuousPullback_continuousQuotientEquiv
    (f : C(PositiveRationalQuotient F G T i, ℂ)) :
    quotientContinuousPullback F G S j (continuousQuotientEquiv F G h f) =
      positiveQuotientContinuousPullback F G T i f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx : (quotientHomeomorph F G h).symm (LeftCosetSpace.mk (rationalSubgroup F G S j) x) =
      LeftCosetSpace.mk (positiveRationalSubgroup F G T i) x := by
    rw [Homeomorph.symm_apply_eq, quotientHomeomorph_mk]
  exact congrArg f hx

/-- The identification intertwines the two continuous right actions. -/
theorem continuousQuotientEquiv_rightAction (g : AdelicGroupPoints F G)
    (f : C(PositiveRationalQuotient F G T i, ℂ)) :
    continuousQuotientEquiv F G h (continuousPositiveQuotientRightAction F G T i g f) =
      continuousQuotientRightAction F G S j g (continuousQuotientEquiv F G h f) := by
  apply ContinuousMap.ext
  intro q
  change f (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) g
      ((quotientHomeomorph F G h).symm q)) =
    f ((quotientHomeomorph F G h).symm
      (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g q))
  congr 1
  rw [Homeomorph.eq_symm_apply, quotientHomeomorph_rightTranslate,
    Homeomorph.apply_symm_apply]

/-- Square integrability for the two quotient measures corresponds. -/
theorem memLp_continuousQuotientEquiv_iff (f : C(PositiveRationalQuotient F G T i, ℂ)) :
    MemLp (continuousQuotientEquiv F G h f) 2 (quotientHaarMeasure F G S j) ↔
      MemLp f 2 (positiveRationalQuotientHaarMeasure F G T i) := by
  have hm := measurePreserving_quotientMeasurableEquiv F G h
  constructor
  · intro hf
    have hcomp := hf.comp_measurePreserving hm
    have heq : (continuousQuotientEquiv F G h f : Quotient F G S j → ℂ) ∘
        quotientMeasurableEquiv F G h = f := by
      funext p
      exact congrArg f ((quotientHomeomorph F G h).symm_apply_apply p)
    rwa [heq] at hcomp
  · intro hf
    exact hf.comp_measurePreserving (MeasurePreserving.symm _ hm)

/-- On `L²` classes, the continuous identification is `quotientL2Equiv`. -/
theorem quotientContinuousL2ToLp_continuousQuotientEquiv
    (f : continuousL2Submodule F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    quotientContinuousL2ToLp F G (quotientHaarMeasure F G S j)
        ⟨continuousQuotientEquiv F G h f.val,
          (memLp_continuousQuotientEquiv_iff F G h f.val).mpr f.property⟩ =
      quotientL2Equiv F G h (continuousL2ToLp F G T i _ f) :=
  rfl

section ParabolicComparison

variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))
variable (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
  (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

theorem continuousQuotientEquiv_mem_parabolicCuspidalL2_iff
    (f : C(PositiveRationalQuotient F G T i, ℂ)) :
    continuousQuotientEquiv F G h f ∈ quotientParabolicCuspidalL2Subrepresentation F G hPD hG
        measuresU (quotientHaarMeasure F G S j) hInv' ↔
      f ∈ positiveParabolicCuspidalL2Subrepresentation F G T i hPD hG measuresU
        (positiveRationalQuotientHaarMeasure F G T i) hInv := by
  rw [mem_quotientParabolicCuspidalL2Subrepresentation,
    mem_positiveParabolicCuspidalL2Subrepresentation,
    quotientContinuousPullback_continuousQuotientEquiv, memLp_continuousQuotientEquiv_iff]

/-- The continuous parabolic-vanishing `L²` functions on the two quotients correspond. -/
def parabolicCuspidalL2FunctionsEquiv :
    PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU
        (positiveRationalQuotientHaarMeasure F G T i) hInv ≃ₗ[ℂ]
      QuotientParabolicCuspidalL2Functions F G hPD hG measuresU
        (quotientHaarMeasure F G S j) hInv' where
  toFun f := ⟨continuousQuotientEquiv F G h f.val,
    (continuousQuotientEquiv_mem_parabolicCuspidalL2_iff F G h hPD hG measuresU hInv hInv'
      f.val).mpr f.property⟩
  invFun f := ⟨(continuousQuotientEquiv F G h).symm f.val,
    (continuousQuotientEquiv_mem_parabolicCuspidalL2_iff F G h hPD hG measuresU hInv hInv'
      _).mp (by rw [LinearEquiv.apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((continuousQuotientEquiv F G h).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousQuotientEquiv F G h).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousQuotientEquiv F G h) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousQuotientEquiv F G h) _ _)

theorem parabolicCuspidalL2FunctionsEquiv_rightAction (g : AdelicGroupPoints F G)
    (f : PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU
      (positiveRationalQuotientHaarMeasure F G T i) hInv) :
    parabolicCuspidalL2FunctionsEquiv F G h hPD hG measuresU hInv hInv'
        (positiveParabolicCuspidalL2RightAction F G T i hPD hG measuresU _ hInv g f) =
      quotientParabolicCuspidalL2RightAction F G hPD hG measuresU _ hInv' g
        (parabolicCuspidalL2FunctionsEquiv F G h hPD hG measuresU hInv hInv' f) :=
  Subtype.ext (continuousQuotientEquiv_rightAction F G h g f.val)

/-- The function correspondence is `quotientL2Equiv` on `L²` classes. -/
theorem quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsEquiv
    (f : PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU
      (positiveRationalQuotientHaarMeasure F G T i) hInv) :
    quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv'
        (parabolicCuspidalL2FunctionsEquiv F G h hPD hG measuresU hInv hInv' f) =
      quotientL2Equiv F G h (positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU _ hInv f) :=
  rfl

/-- `quotientL2Equiv` carries the positive-torus continuous parabolic-vanishing image onto the
restriction-quotient image. -/
theorem mem_quotientContinuousParabolicCuspidalL2Image_iff
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU _ hInv' ↔
      (quotientL2Equiv F G h).symm φ ∈
        continuousParabolicCuspidalL2Image F G T i hPD hG measuresU _ hInv := by
  rw [mem_quotientContinuousParabolicCuspidalL2Image, mem_continuousParabolicCuspidalL2Image]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨(parabolicCuspidalL2FunctionsEquiv F G h hPD hG measuresU hInv hInv').symm f, ?_⟩
    apply (quotientL2Equiv F G h).injective
    rw [LinearIsometryEquiv.apply_symm_apply,
      ← quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsEquiv]
    exact congrArg (fun z => quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv' z)
      ((parabolicCuspidalL2FunctionsEquiv F G h hPD hG measuresU hInv hInv').apply_symm_apply f)
  · rintro ⟨f, hf⟩
    refine ⟨parabolicCuspidalL2FunctionsEquiv F G h hPD hG measuresU hInv hInv' f, ?_⟩
    rw [quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsEquiv, hf,
      LinearIsometryEquiv.apply_symm_apply]

end ParabolicComparison

section CuspFormComparison

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)
variable (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
  (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

theorem continuousQuotientEquiv_mem_cuspidalFormL2_iff
    (f : C(PositiveRationalQuotient F G T i, ℂ)) :
    continuousQuotientEquiv F G h f ∈ quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth
        hcalc hPD hG hrho hK hN (quotientHaarMeasure F G S j) hInv' ↔
      f ∈ positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        T i (positiveRationalQuotientHaarMeasure F G T i) hInv := by
  rw [mem_quotientCuspidalFormL2Subrepresentation, mem_positiveCuspidalFormL2Subrepresentation,
    quotientContinuousPullback_continuousQuotientEquiv, memLp_continuousQuotientEquiv_iff]

/-- The continuous square-integrable `AdelicCuspidalForms` functions on the two quotients
correspond. -/
def cuspidalFormL2FunctionsEquiv :
    PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        (positiveRationalQuotientHaarMeasure F G T i) hInv ≃ₗ[ℂ]
      QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (quotientHaarMeasure F G S j) hInv' where
  toFun f := ⟨continuousQuotientEquiv F G h f.val,
    (continuousQuotientEquiv_mem_cuspidalFormL2_iff F G h Kinf rho hsmooth hcalc hPD hG hrho hK
      hN hInv hInv' f.val).mpr f.property⟩
  invFun f := ⟨(continuousQuotientEquiv F G h).symm f.val,
    (continuousQuotientEquiv_mem_cuspidalFormL2_iff F G h Kinf rho hsmooth hcalc hPD hG hrho hK
      hN hInv hInv' _).mp (by rw [LinearEquiv.apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((continuousQuotientEquiv F G h).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousQuotientEquiv F G h).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousQuotientEquiv F G h) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousQuotientEquiv F G h) _ _)

theorem cuspidalFormL2FunctionsEquiv_finiteRightAction (c : FiniteAdelicGroupPoints F G)
    (f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      (positiveRationalQuotientHaarMeasure F G T i) hInv) :
    cuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv hInv'
        (positiveCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
          T i _ hInv c f) =
      quotientCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv'
        c (cuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv hInv'
          f) :=
  Subtype.ext (continuousQuotientEquiv_rightAction F G h (AdelicGroupPoints.ofFinite F G c) f.val)

/-- The `AdelicCuspidalForms` correspondence is `quotientL2Equiv` on `L²` classes. -/
theorem quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsEquiv
    (f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      (positiveRationalQuotientHaarMeasure F G T i) hInv) :
    quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv'
        (cuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv hInv'
          f) =
      quotientL2Equiv F G h
        (positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _ hInv f) :=
  rfl

/-- `quotientL2Equiv` carries the positive-torus `AdelicCuspidalForms` image onto the
restriction-quotient image. -/
theorem mem_quotientCuspidalFormL2Image_iff (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv' ↔
      (quotientL2Equiv F G h).symm φ ∈
        cuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _ hInv := by
  have hR : (quotientL2Equiv F G h).symm φ ∈
      cuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _ hInv ↔
        ∃ f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
            (positiveRationalQuotientHaarMeasure F G T i) hInv,
          positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _ hInv f =
            (quotientL2Equiv F G h).symm φ :=
    Iff.rfl
  refine (mem_quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv'
    φ).trans (Iff.trans ?_ hR.symm)
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨(cuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
      hInv').symm f, ?_⟩
    apply (quotientL2Equiv F G h).injective
    rw [LinearIsometryEquiv.apply_symm_apply,
      ← quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsEquiv]
    exact congrArg
      (fun z => quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv' z)
      ((cuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
        hInv').apply_symm_apply f)
  · rintro ⟨f, hf⟩
    refine ⟨cuspidalFormL2FunctionsEquiv F G h Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
      hInv' f, ?_⟩
    rw [quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsEquiv, hf,
      LinearIsometryEquiv.apply_symm_apply]

end CuspFormComparison

end Comparison

section SplitComponents

variable {S j} {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]

section ParabolicSplit

variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))

/-- For split components, the continuous parabolic-vanishing image in `L²` of the restriction
quotient with its canonical measure. -/
def splitComponentParabolicCuspidalL2Image :
    Subrepresentation (splitComponentL2RightAction F G hi hj hs) :=
  quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU _
    (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)

/-- For split components, distinct continuous functions give distinct `L²` classes. -/
theorem quotientParabolicCuspidalL2ToLp_injective_of_splitComponents :
    Function.Injective (quotientParabolicCuspidalL2ToLp F G hPD hG measuresU
      (quotientHaarMeasure F G S j)
      (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)) := by
  let := quotientHaarMeasure_isOpenPosMeasure_of_splitComponents F G hi hj hs
  exact quotientParabolicCuspidalL2ToLp_injective F G hPD hG measuresU _ _

/-- For split components, `splitComponentL2Equiv` carries the positive-torus continuous
parabolic-vanishing image onto `splitComponentParabolicCuspidalL2Image`. -/
theorem mem_splitComponentParabolicCuspidalL2Image_iff
    (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ splitComponentParabolicCuspidalL2Image F G hi hj hs hPD hG measuresU ↔
      (splitComponentL2Equiv F G hj hs).symm φ ∈
        continuousParabolicCuspidalL2Image F G T i hPD hG measuresU _ hInv :=
  mem_quotientContinuousParabolicCuspidalL2Image_iff F G _ hPD hG measuresU hInv _ φ

end ParabolicSplit

section CuspFormSplit

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)

/-- For split components, the image of square-integrable continuous `AdelicCuspidalForms`
functions in `L²` of the restriction quotient with its canonical measure. -/
def splitComponentCuspidalFormL2Image :
    Subrepresentation (rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j)
      (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)) :=
  quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _
    (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)

/-- For split components, distinct continuous `AdelicCuspidalForms` functions give distinct
`L²` classes. -/
theorem quotientCuspidalFormL2ToLp_injective_of_splitComponents :
    Function.Injective (quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      (quotientHaarMeasure F G S j)
      (quotientHaarMeasure_rightInvariant_of_splitComponents F G hi hj hs)) := by
  let := quotientHaarMeasure_isOpenPosMeasure_of_splitComponents F G hi hj hs
  exact quotientCuspidalFormL2ToLp_injective F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ _

/-- For split components, `splitComponentL2Equiv` carries the positive-torus
`AdelicCuspidalForms` image onto `splitComponentCuspidalFormL2Image`. -/
theorem mem_splitComponentCuspidalFormL2Image_iff
    (hInv : QuotientMeasureRightInvariant F G T i (positiveRationalQuotientHaarMeasure F G T i))
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    φ ∈ splitComponentCuspidalFormL2Image F G hi hj hs Kinf rho hsmooth hcalc hPD hG hrho hK hN ↔
      (splitComponentL2Equiv F G hj hs).symm φ ∈
        cuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _ hInv :=
  mem_quotientCuspidalFormL2Image_iff F G _ Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv _ φ

end CuspFormSplit

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
