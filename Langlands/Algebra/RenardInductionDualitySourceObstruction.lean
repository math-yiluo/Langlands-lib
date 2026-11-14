import Langlands.Algebra.RenardDualitySourceObstruction

/-!
Actual induction and right coinduction values for the remaining bare-additive
coefficient question in Renard I.4.2. The source algebras and actions are
the published nonsurjective-embedding construction. Their actual values at
the regular source object are not isomorphic, so no natural comparison exists
under the bare additive convention.
-/

noncomputable section

open CategoryTheory MulOpposite

namespace Langlands.Algebra.RenardInductionDualitySourceObstruction

open ComplexEmbeddingDualityObstruction
open RenardDualitySourceObstruction

variable (σ : ℂ →+* ℂ)

local instance : NonUnitalModule (A σ) ℂ := leftAction σ
local instance : NonUnitalModule (A σ)ᵐᵒᵖ ℂ := rightAction σ
local instance : NonUnitalModule ℂ ℂ := NonUnitalModule.regular ℂ
local instance : NonUnitalModule ℂᵐᵒᵖ ℂ := NonUnitalModule.rightRegular ℂ
local instance : NonUnitalModule (A σ) (A σ) := NonUnitalModule.regular (A σ)

/-- The actual regular source object, with its ordinary original action. -/
def sourceRegularObject : NondegenerateModuleCat (A σ) :=
  ⟨NonUnitalModuleCat.of (A σ) (A σ),
    NondegenerateTensorFunctor.regular_isNondegenerate (IsIdempotented.of_ring (A σ))⟩

/-- The actual `B ⊗_A A` value of the published induction functor. -/
def inducedObject : NondegenerateModuleCat ℂ :=
  (NondegenerateTensorFunctor.regularP (IsIdempotented.of_ring ℂ)
    (regular_right_commute σ) (right_nondegenerate σ)).obj (sourceRegularObject σ)

abbrev PCarrier := (inducedObject σ).obj.carrier

local instance : NonUnitalModule ℂ (PCarrier σ) := (inducedObject σ).obj.isModule

def inductionPairing : ℂ →+ (sourceRegularObject σ).obj →+ ℂ where
  toFun b :=
    { toFun := fun a => b * σ (aRingEquiv σ a)
      map_zero' := by
        change b * σ (aRingEquiv σ (0 : A σ)) = 0
        simp
      map_add' := by
        intro a a'
        change b * σ (aRingEquiv σ ((show A σ from a) + (show A σ from a'))) =
          b * σ (aRingEquiv σ a) + b * σ (aRingEquiv σ a')
        rw [(aRingEquiv σ).map_add (show A σ from a) (show A σ from a'),
          σ.map_add, mul_add] }
  map_zero' := by ext a; exact zero_mul _
  map_add' := by intro b b'; ext a; exact add_mul _ _ _

theorem inductionPairing_balanced :
    NonUnitalModuleTensor.IsBalanced (A σ) (inductionPairing σ) := by
  intro a b a'
  change (b * σ (aRingEquiv σ a)) * σ (aRingEquiv σ a') =
    b * σ (aRingEquiv σ (a * (show A σ from a')))
  rw [(aRingEquiv σ).map_mul a (show A σ from a'), σ.map_mul, mul_assoc]

def inducedContraction : PCarrier σ →+ ℂ :=
  NonUnitalModuleTensor.lift (A σ) (inductionPairing σ) (inductionPairing_balanced σ)

def inducedInsertion : ℂ →+ PCarrier σ where
  toFun b := NonUnitalModuleTensor.tmul (A σ) ℂ (sourceRegularObject σ).obj b
    (show (sourceRegularObject σ).obj from (1 : A σ))
  map_zero' := NonUnitalModuleTensor.zero_tmul _ _ _ _
  map_add' b c := NonUnitalModuleTensor.add_tmul _ _ _ b c _

@[simp] theorem contraction_insertion (b : ℂ) :
    inducedContraction σ (inducedInsertion σ b) = b := by
  change b * σ (aRingEquiv σ 1) = b
  simp

theorem insertion_contraction (t : PCarrier σ) :
    inducedInsertion σ (inducedContraction σ t) = t := by
  have h : (inducedInsertion σ).comp (inducedContraction σ) =
      AddMonoidHom.id (PCarrier σ) := by
    apply NonUnitalModuleTensor.hom_ext (A σ)
    intro b a
    change NonUnitalModuleTensor.tmul (A σ) ℂ (sourceRegularObject σ).obj
      (b * σ (aRingEquiv σ a)) (show (sourceRegularObject σ).obj from (1 : A σ)) =
      NonUnitalModuleTensor.tmul (A σ) ℂ (sourceRegularObject σ).obj b a
    have ha : (show A σ from a) •
        (show (sourceRegularObject σ).obj from (1 : A σ)) = a := by
      change (show A σ from a) * 1 = (show A σ from a)
      exact mul_one _
    exact (NonUnitalModuleTensor.tmul_balanced (A σ) ℂ
      (sourceRegularObject σ).obj (show A σ from a) b
        (show (sourceRegularObject σ).obj from (1 : A σ))).trans
          (congrArg (NonUnitalModuleTensor.tmul (A σ) ℂ
            (sourceRegularObject σ).obj b) ha)
  exact DFunLike.congr_fun h t

theorem inducedContraction_injective : Function.Injective (inducedContraction σ) :=
  Function.LeftInverse.injective (insertion_contraction σ)

theorem inducedContraction_action (b : ℂ) (t : PCarrier σ) :
    inducedContraction σ (b • t) = b * inducedContraction σ t := by
  have h : (inducedContraction σ).comp
        (NonUnitalModule.toEndHom (inducedObject σ).obj.isModule b) =
      (AddMonoidHom.mulLeft b).comp (inducedContraction σ) := by
    apply NonUnitalModuleTensor.hom_ext (A σ)
    intro c a
    change (b * c) * σ (aRingEquiv σ a) = b * (c * σ (aRingEquiv σ a))
    exact mul_assoc _ _ _
  exact DFunLike.congr_fun h t

theorem induced_unital (t : PCarrier σ) : (1 : ℂ) • t = t := by
  apply inducedContraction_injective σ
  rw [inducedContraction_action, one_mul]

theorem inducedContraction_smul (c : ℂ) (t : PCarrier σ) :
    inducedContraction σ (NondegenerateScalars.scalarMul ℂ
      (M := PCarrier σ) (inducedObject σ).property c t) =
        c * inducedContraction σ t := by
  rw [NondegenerateScalars.scalarMul_eq ℂ (IsIdempotented.of_ring ℂ)
    (inducedObject σ).property c t ⟨1, IsIdempotentElem.one⟩ (induced_unital σ t)]
  rw [inducedContraction_action]
  change (c * 1) * inducedContraction σ t = c * inducedContraction σ t
  rw [mul_one]

/-- The recovered coefficient module of the actual induced object is ordinary `ℂ`. -/
def inducedEquiv :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
      (inducedObject σ).property
    PCarrier σ ≃ₗ[ℂ] ℂ := by
  letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
    (inducedObject σ).property
  exact
    { toFun := inducedContraction σ
      invFun := inducedInsertion σ
      left_inv := insertion_contraction σ
      right_inv := contraction_insertion σ
      map_add' := (inducedContraction σ).map_add
      map_smul' := inducedContraction_smul σ }

theorem sourceRegular_unital (a : (sourceRegularObject σ).obj) :
    (1 : A σ) • a = a :=
  one_mul (show A σ from a)

theorem sourceRegular_scalarMul (c : ℂ) (a : (sourceRegularObject σ).obj) :
    aRingEquiv σ (show A σ from NondegenerateScalars.scalarMul ℂ
      (M := (sourceRegularObject σ).obj) (sourceRegularObject σ).property c a) =
        c * aRingEquiv σ a := by
  rw [NondegenerateScalars.scalarMul_eq ℂ (IsIdempotented.of_ring (A σ))
    (sourceRegularObject σ).property c a ⟨1, IsIdempotentElem.one⟩
      (sourceRegular_unital σ a)]
  change (c * 1) * aRingEquiv σ a = c * aRingEquiv σ a
  rw [mul_one]

abbrev sourceDualObject : NondegenerateModuleCat (A σ)ᵐᵒᵖ :=
  NonUnitalModuleDual.dualObject (IsIdempotented.of_ring (A σ)) (sourceRegularObject σ)

theorem sourceDual_apply (φ : (sourceDualObject σ).obj) (a : A σ) :
    φ.val (show (sourceRegularObject σ).obj from a) =
      aRingEquiv σ a * φ.val (show (sourceRegularObject σ).obj from (1 : A σ)) := by
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
    (sourceRegularObject σ).property
  let : SMul ℂ (sourceRegularObject σ).obj :=
    (NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
      (sourceRegularObject σ).property).toDistribMulAction.toDistribSMul.toSMul
  have hs : aRingEquiv σ a • (show (sourceRegularObject σ).obj from (1 : A σ)) =
      (show (sourceRegularObject σ).obj from a) := by
    apply (aRingEquiv σ).injective
    exact (sourceRegular_scalarMul σ _ _).trans (by simp)
  exact (congrArg φ.val hs.symm).trans (φ.val.map_smul _ _)

def sourceFunctional (t : ℂ) : (sourceDualObject σ).obj :=
  (unitalDualEquiv (sourceRegularObject σ) (sourceRegular_unital σ)).symm
    (letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
      (sourceRegularObject σ).property
     { toFun := fun a => t * aRingEquiv σ a
       map_add' := by
         intro a a'
         change t * aRingEquiv σ ((show A σ from a) + (show A σ from a')) =
           t * aRingEquiv σ a + t * aRingEquiv σ a'
         rw [(aRingEquiv σ).map_add, mul_add]
       map_smul' := by
         intro c a
         change t * aRingEquiv σ (show A σ from NondegenerateScalars.scalarMul ℂ
           (M := (sourceRegularObject σ).obj) (sourceRegularObject σ).property c a) =
             c * (t * aRingEquiv σ a)
         rw [sourceRegular_scalarMul]
         exact mul_left_comm _ _ _ })

@[simp] theorem sourceFunctional_apply (t : ℂ) (a : A σ) :
    (sourceFunctional σ t).val (show (sourceRegularObject σ).obj from a) =
      t * aRingEquiv σ a := rfl

/-- The actual right-induction value `Hom_(A.op)(B,D_A(A))_B`. -/
def coinducedObject : NondegenerateModuleCat ℂᵐᵒᵖ :=
  (RenardRightHomFunctors.rightI (regular_right_commute σ)
    (IsIdempotented.of_ring ℂ)).obj (sourceDualObject σ)

abbrev HCarrier := (coinducedObject σ).obj.carrier

local instance : NonUnitalModule ℂᵐᵒᵖ (HCarrier σ) := (coinducedObject σ).obj.isModule

def coinducedEvaluation (h : HCarrier σ) (b : ℂ) : ℂ :=
  ((show NonUnitalModuleHom (A σ)ᵐᵒᵖ ℂ (sourceDualObject σ).obj from h.val) b).val
    (show (sourceRegularObject σ).obj from (1 : A σ))

theorem coinducedEvaluation_smul (h : HCarrier σ) (c b : ℂ) :
    coinducedEvaluation σ h (σ c * b) = c * coinducedEvaluation σ h b := by
  let f : NonUnitalModuleHom (A σ)ᵐᵒᵖ ℂ (sourceDualObject σ).obj := h.val
  have hh := f.map_smul (op ((aRingEquiv σ).symm c)) b
  have he := congrArg (fun φ : (sourceDualObject σ).obj =>
    φ.val (show (sourceRegularObject σ).obj from (1 : A σ))) hh
  change (f (b * σ (aRingEquiv σ ((aRingEquiv σ).symm c)))).val
      (show (sourceRegularObject σ).obj from (1 : A σ)) =
    (f b).val (show (sourceRegularObject σ).obj from ((aRingEquiv σ).symm c * 1)) at he
  rw [RingEquiv.apply_symm_apply] at he
  change (f (σ c * b)).val _ = _
  exact (congrArg (fun z : ℂ => (f z).val
      (show (sourceRegularObject σ).obj from (1 : A σ))) (mul_comm (σ c) b)).trans
    (he.trans ((congrArg (fun a : A σ => (f b).val
      (show (sourceRegularObject σ).obj from a)) (mul_one _)).trans
        ((sourceDual_apply σ (f b) ((aRingEquiv σ).symm c)).trans
          (congrArg (fun z : ℂ => z * (f b).val
            (show (sourceRegularObject σ).obj from (1 : A σ)))
              ((aRingEquiv σ).apply_symm_apply c)))))

/-- Evaluation identifies the Hom value with functionals on the restriction module. -/
def coinducedForm (h : HCarrier σ) : Module.Dual ℂ (Carrier σ) where
  toFun z := coinducedEvaluation σ h (carrierRingEquiv σ z)
  map_add' z w := by
    rw [(carrierRingEquiv σ).map_add]
    exact congrArg (fun φ : (sourceDualObject σ).obj =>
      φ.val (show (sourceRegularObject σ).obj from (1 : A σ)))
        ((show NonUnitalModuleHom (A σ)ᵐᵒᵖ ℂ (sourceDualObject σ).obj from h.val).map_add _ _)
  map_smul' c z := coinducedEvaluation_smul σ h c (carrierRingEquiv σ z)

def coinducedParameterHom (φ : Module.Dual ℂ (Carrier σ)) :
    NonUnitalModuleHom (A σ)ᵐᵒᵖ ℂ (sourceDualObject σ).obj where
  toFun b := sourceFunctional σ (φ ((carrierRingEquiv σ).symm b))
  map_zero' := by
    let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
      (sourceRegularObject σ).property
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change φ ((carrierRingEquiv σ).symm 0) * aRingEquiv σ a = 0
    rw [map_zero, map_zero, zero_mul]
  map_add' b d := by
    let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
      (sourceRegularObject σ).property
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change φ ((carrierRingEquiv σ).symm (b + d)) * aRingEquiv σ a =
      φ ((carrierRingEquiv σ).symm b) * aRingEquiv σ a +
        φ ((carrierRingEquiv σ).symm d) * aRingEquiv σ a
    rw [map_add, map_add, add_mul]
  map_smul' a b := by
    let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
      (sourceRegularObject σ).property
    apply Subtype.ext
    apply LinearMap.ext
    intro a'
    change φ ((carrierRingEquiv σ).symm (b * σ (aRingEquiv σ a.unop))) *
        aRingEquiv σ a' =
      φ ((carrierRingEquiv σ).symm b) *
        aRingEquiv σ (a.unop * (show A σ from a'))
    have hs : (carrierRingEquiv σ).symm (b * σ (aRingEquiv σ a.unop)) =
        aRingEquiv σ a.unop • (carrierRingEquiv σ).symm b := by
      apply (carrierRingEquiv σ).injective
      change b * σ (aRingEquiv σ a.unop) =
        σ (aRingEquiv σ a.unop) * b
      exact mul_comm _ _
    rw [hs, φ.map_smul, (aRingEquiv σ).map_mul]
    change (aRingEquiv σ a.unop * φ ((carrierRingEquiv σ).symm b)) *
      aRingEquiv σ a' = _
    ring

def coinducedParameter (φ : Module.Dual ℂ (Carrier σ)) : HCarrier σ :=
  ⟨coinducedParameterHom σ φ,
    (RenardRightHomFunctors.mem_rightInductionPart (regular_right_commute σ)
      (IsIdempotented.of_ring ℂ) _).mpr
        ⟨⟨1, IsIdempotentElem.one⟩,
          fun b => congrArg (coinducedParameterHom σ φ) (one_mul b)⟩⟩

@[simp] theorem coinducedForm_parameter (φ : Module.Dual ℂ (Carrier σ)) :
    coinducedForm σ (coinducedParameter σ φ) = φ := by
  apply LinearMap.ext
  intro z
  change φ ((carrierRingEquiv σ).symm (carrierRingEquiv σ z)) *
    aRingEquiv σ 1 = φ z
  rw [RingEquiv.symm_apply_apply, map_one, mul_one]

theorem coinducedParameter_form (h : HCarrier σ) :
    coinducedParameter σ (coinducedForm σ h) = h := by
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
    (sourceRegularObject σ).property
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro b
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  change coinducedEvaluation σ h
      (carrierRingEquiv σ ((carrierRingEquiv σ).symm b)) * aRingEquiv σ a =
    ((show NonUnitalModuleHom (A σ)ᵐᵒᵖ ℂ (sourceDualObject σ).obj from h.val) b).val a
  rw [RingEquiv.apply_symm_apply]
  exact (mul_comm _ _).trans (sourceDual_apply σ
    ((show NonUnitalModuleHom (A σ)ᵐᵒᵖ ℂ (sourceDualObject σ).obj from h.val) b)
      (show A σ from a)).symm

def coinducedAddEquiv : HCarrier σ ≃+ Module.Dual ℂ (Carrier σ) where
  toFun := coinducedForm σ
  invFun := coinducedParameter σ
  left_inv := coinducedParameter_form σ
  right_inv := coinducedForm_parameter σ
  map_add' h k := by
    apply LinearMap.ext
    intro z
    rfl

theorem coinducedForm_action_sigma (c : ℂ) (h : HCarrier σ) :
    coinducedForm σ (op (σ c) • h) = c • coinducedForm σ h := by
  apply LinearMap.ext
  intro z
  change coinducedEvaluation σ h (σ c * carrierRingEquiv σ z) =
    c * coinducedEvaluation σ h (carrierRingEquiv σ z)
  exact coinducedEvaluation_smul σ h c _

/-- The actual dual of the induced regular source object. -/
def dualInducedObject : NondegenerateModuleCat ℂᵐᵒᵖ :=
  NonUnitalModuleDual.dualObject (IsIdempotented.of_ring ℂ) (inducedObject σ)

abbrev DPCarrier := (dualInducedObject σ).obj.carrier

local instance : NonUnitalModule ℂᵐᵒᵖ (DPCarrier σ) :=
  (dualInducedObject σ).obj.isModule

/-- Dualizing the actual contraction identifies this dual value with `ℂ`. -/
def dualInducedEquiv :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ).op
      (dualInducedObject σ).property
    DPCarrier σ ≃ₗ[ℂ] ℂ := by
  letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
    (inducedObject σ).property
  exact ((unitalDualEquiv (inducedObject σ) (induced_unital σ)).trans
    (inducedEquiv σ).symm.dualMap).trans (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ)

theorem dualInducedEquiv_apply (φ : DPCarrier σ) :
    dualInducedEquiv σ φ = φ.val (inducedInsertion σ 1) := rfl

theorem dualInducedEquiv_action (b : ℂ) (φ : DPCarrier σ) :
    dualInducedEquiv σ (op b • φ) = b * dualInducedEquiv σ φ := by
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
    (inducedObject σ).property
  let : SMul ℂ (PCarrier σ) :=
    (NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
      (inducedObject σ).property).toDistribMulAction.toDistribSMul.toSMul
  have hs :
      (NonUnitalModule.toEndHom (inducedObject σ).obj.isModule b)
        (inducedInsertion σ 1) =
      NondegenerateScalars.scalarMul ℂ (M := PCarrier σ)
        (inducedObject σ).property b (inducedInsertion σ 1) := by
    apply inducedContraction_injective σ
    exact (inducedContraction_action σ b (inducedInsertion σ 1)).trans
      (inducedContraction_smul σ b (inducedInsertion σ 1)).symm
  change φ.val
    ((NonUnitalModule.toEndHom (inducedObject σ).obj.isModule b)
      (inducedInsertion σ 1)) = b * φ.val (inducedInsertion σ 1)
  exact (congrArg φ.val hs).trans (φ.val.map_smul b _)

theorem dualInducedEquiv_symm_mul (b t : ℂ) :
    (dualInducedEquiv σ).symm (b * t) =
      op b • (dualInducedEquiv σ).symm t := by
  apply (dualInducedEquiv σ).injective
  rw [LinearEquiv.apply_symm_apply, dualInducedEquiv_action,
    LinearEquiv.apply_symm_apply]

/-- Restricting an actual `B`-intertwiner along `σ` gives an ordinary linear map. -/
def restrictionLinearMap
    (f : NonUnitalModuleHom ℂᵐᵒᵖ (DPCarrier σ) (HCarrier σ)) :
    Carrier σ →ₗ[ℂ] Module.Dual ℂ (Carrier σ) where
  toFun z := coinducedForm σ (f ((dualInducedEquiv σ).symm (carrierRingEquiv σ z)))
  map_add' z w := by
    exact ((coinducedAddEquiv σ).toAddMonoidHom.comp
      (f.toAddMonoidHom.comp ((dualInducedEquiv σ).symm.toAddMonoidHom.comp
        (carrierRingEquiv σ).toAddMonoidHom))).map_add z w
  map_smul' c z := by
    change coinducedForm σ
      (f ((dualInducedEquiv σ).symm (σ c * carrierRingEquiv σ z))) =
        c • coinducedForm σ
          (f ((dualInducedEquiv σ).symm (carrierRingEquiv σ z)))
    exact (congrArg (fun t : DPCarrier σ => coinducedForm σ (f t))
      (dualInducedEquiv_symm_mul σ (σ c) (carrierRingEquiv σ z))).trans
        ((congrArg (coinducedForm σ) (f.map_smul (op (σ c)) _)).trans
          (coinducedForm_action_sigma σ c _))

/-- No bijective original-action intertwiner exists between the actual values. -/
theorem no_bijective_intertwiner (hσ : ¬ Function.Surjective σ)
    (f : NonUnitalModuleHom ℂᵐᵒᵖ (DPCarrier σ) (HCarrier σ)) :
    ¬ Function.Bijective f := by
  intro hf
  have hg : Function.Bijective (restrictionLinearMap σ f) :=
    (coinducedAddEquiv σ).bijective.comp
      (hf.comp ((dualInducedEquiv σ).symm.bijective.comp (carrierRingEquiv σ).bijective))
  exact (no_linearEquiv_dual σ hσ).false
    (LinearEquiv.ofBijective (restrictionLinearMap σ f) hg)

/-- The source comparison fails already at the regular source object. -/
theorem no_objectIso (hσ : ¬ Function.Surjective σ) :
    IsEmpty (coinducedObject σ ≅ dualInducedObject σ) := by
  refine ⟨fun e => no_bijective_intertwiner σ hσ e.inv.hom ?_⟩
  let f : NonUnitalModuleHom ℂᵐᵒᵖ (DPCarrier σ) (HCarrier σ) := e.inv.hom
  let g : NonUnitalModuleHom ℂᵐᵒᵖ (HCarrier σ) (DPCarrier σ) := e.hom.hom
  have hl : Function.LeftInverse g f := by
    intro h
    exact congrArg (fun k : dualInducedObject σ ⟶ dualInducedObject σ =>
      (show NonUnitalModuleHom ℂᵐᵒᵖ (DPCarrier σ) (DPCarrier σ) from k.hom) h)
        e.inv_hom_id
  have hr : Function.RightInverse g f := by
    intro h
    exact congrArg (fun k : coinducedObject σ ⟶ coinducedObject σ =>
      (show NonUnitalModuleHom ℂᵐᵒᵖ (HCarrier σ) (HCarrier σ) from k.hom) h)
        e.hom_inv_id
  exact ⟨hl.injective, hr.surjective⟩

/-- The actual right-induction after source-duality composite. -/
def coinducedDualFunctor :
    (NondegenerateModuleCat.{0, 0} (A σ))ᵒᵖ ⥤ NondegenerateModuleCat.{0, 0} ℂᵐᵒᵖ :=
  NonUnitalModuleDual.leftToRightFunctor (IsIdempotented.of_ring (A σ)) ⋙
    RenardRightHomFunctors.rightI (regular_right_commute σ) (IsIdempotented.of_ring ℂ)

/-- The actual target-duality after induction composite. -/
def dualInducedFunctor :
    (NondegenerateModuleCat.{0, 0} (A σ))ᵒᵖ ⥤ NondegenerateModuleCat.{0, 0} ℂᵐᵒᵖ :=
  (NondegenerateTensorFunctor.regularP (IsIdempotented.of_ring ℂ)
    (regular_right_commute σ) (right_nondegenerate σ)).op ⋙
      NonUnitalModuleDual.leftToRightFunctor (IsIdempotented.of_ring ℂ)

/-- A proper self-embedding rules out every natural comparison of these functors. -/
theorem no_naturalIso (hσ : ¬ Function.Surjective σ) :
    IsEmpty (coinducedDualFunctor σ ≅ dualInducedFunctor σ) :=
  ⟨fun e => (no_objectIso σ hσ).false (e.app (Opposite.op (sourceRegularObject σ)))⟩

/-- The published proper self-embedding supplies an unconditional counterexample. -/
theorem exists_counterexample :
    ∃ σ : ℂ →+* ℂ, ¬ Function.Surjective σ ∧
      IsEmpty (coinducedDualFunctor σ ≅ dualInducedFunctor σ) := by
  obtain ⟨σ, hσ⟩ := exists_nonsurjective_endomorphism
  exact ⟨σ, hσ, no_naturalIso σ hσ⟩

end Langlands.Algebra.RenardInductionDualitySourceObstruction
