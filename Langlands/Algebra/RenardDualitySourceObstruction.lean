import Langlands.Algebra.ComplexEmbeddingDualityObstruction
import Langlands.Algebra.DualityForgetfulInductionStatements
import Langlands.Algebra.RegularTensorContraction

/-!
Actual original-action tensor, Hom and dual functors for the bare-additive
coefficient obstruction to Renard I.4.2. This internal construction identifies
their recovered complex modules and excludes every natural isomorphism in
this example. The common-coefficient theorem is a separate statement.
-/

noncomputable section

open CategoryTheory MulOpposite

namespace Langlands.Algebra.RenardDualitySourceObstruction

open ComplexEmbeddingDualityObstruction

/-- The source algebra has ordinary complex coefficients on a distinct carrier. -/
def A (_σ : ℂ →+* ℂ) := ULift.{0} ℂ

instance (σ : ℂ →+* ℂ) : Field (A σ) := inferInstanceAs (Field (ULift.{0} ℂ))

def aRingEquiv (σ : ℂ →+* ℂ) : A σ ≃+* ℂ := ULift.ringEquiv

instance (σ : ℂ →+* ℂ) : Algebra ℂ (A σ) := (aRingEquiv σ).symm.toRingHom.toAlgebra

@[instance_reducible]
def leftAction (σ : ℂ →+* ℂ) : NonUnitalModule (A σ) ℂ :=
  letI : Module (A σ) ℂ := Module.compHom ℂ (σ.comp (aRingEquiv σ).toRingHom)
  NonUnitalModule.ofModule (A σ) ℂ

@[instance_reducible]
def rightAction (σ : ℂ →+* ℂ) : NonUnitalModule (A σ)ᵐᵒᵖ ℂ where
  smul a z := z * σ (aRingEquiv σ a.unop)
  smul_zero _ := zero_mul _
  smul_add _ _ _ := add_mul _ _ _
  mul_smul a b z := by
    change z * σ (aRingEquiv σ (b.unop * a.unop)) =
      (z * σ (aRingEquiv σ b.unop)) * σ (aRingEquiv σ a.unop)
    simp only [map_mul, mul_assoc]
  add_smul a b z := by
    change z * σ (aRingEquiv σ (a.unop + b.unop)) =
      z * σ (aRingEquiv σ a.unop) + z * σ (aRingEquiv σ b.unop)
    simp only [map_add, mul_add]
  zero_smul z := by
    change z * σ (aRingEquiv σ 0) = 0
    simp

/-- A globally fixing unit makes the actual nondegenerate dual the full dual.
The source coefficients in this equivalence are recovered from its right action. -/
def unitalDualEquiv {R : Type} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (M : NondegenerateModuleCat R) (h1 : ∀ m : M.obj, (1 : R) • m = m) :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring R).op
      (NonUnitalModuleDual.dualObject (IsIdempotented.of_ring R) M).property
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring R) M.property
    (NonUnitalModuleDual.dualObject (IsIdempotented.of_ring R) M).obj ≃ₗ[ℂ]
      Module.Dual ℂ M.obj := by
  letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring R).op
    (NonUnitalModuleDual.dualObject (IsIdempotented.of_ring R) M).property
  letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring R) M.property
  exact
    { toFun := fun φ => φ.val
      invFun := fun φ => ⟨φ, by
        apply (NonUnitalModuleDual.mem_dual_iff
          (IsIdempotented.of_ring R) M.property φ).mpr
        exact ⟨⟨1, IsIdempotentElem.one⟩, fun m => congrArg φ (h1 m)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c φ => NonUnitalModuleDual.canonical_smul_val
        (IsIdempotented.of_ring R) M.property c φ }

section Actions

variable (σ : ℂ →+* ℂ)

local instance : NonUnitalModule (A σ) ℂ := leftAction σ
local instance : NonUnitalModule (A σ)ᵐᵒᵖ ℂ := rightAction σ
local instance : NonUnitalModule ℂ ℂ := NonUnitalModule.regular ℂ
local instance : NonUnitalModule ℂᵐᵒᵖ ℂ := NonUnitalModule.rightRegular ℂ

@[simp] theorem leftAction_apply (a : A σ) (z : ℂ) :
    a • z = σ (aRingEquiv σ a) * z := rfl

@[simp] theorem rightAction_apply (a : A σ) (z : ℂ) :
    op a • z = z * σ (aRingEquiv σ a) := rfl

theorem left_unital (z : ℂ) : (1 : A σ) • z = z := by
  change σ (aRingEquiv σ 1) * z = z
  simp

theorem right_unital (z : ℂ) : op (1 : A σ) • z = z := by
  change z * σ (aRingEquiv σ 1) = z
  simp

theorem left_nondegenerate : IsNondegenerate (A σ) ℂ :=
  fun z => ⟨⟨1, IsIdempotentElem.one⟩, left_unital σ z⟩

theorem right_nondegenerate : IsRightNondegenerate (A σ) ℂ :=
  fun z => ⟨⟨op 1, IsIdempotentElem.one⟩, right_unital σ z⟩

theorem left_right_commute : ActionsCommute (A σ) (A σ) ℂ := by
  intro a b z
  change σ (aRingEquiv σ a) * (z * σ (aRingEquiv σ b)) =
    (σ (aRingEquiv σ a) * z) * σ (aRingEquiv σ b)
  exact (mul_assoc _ _ _).symm

theorem left_regular_commute : ActionsCommute (A σ) ℂ ℂ := by
  intro a b z
  exact (mul_assoc _ _ _).symm

theorem regular_right_commute : ActionsCommute ℂ (A σ) ℂ := by
  intro b a z
  exact (mul_assoc _ _ _).symm

def regularObject : NondegenerateModuleCat ℂ :=
  ⟨NonUnitalModuleCat.of ℂ ℂ,
    NondegenerateTensorFunctor.regular_isNondegenerate (IsIdempotented.of_ring ℂ)⟩

def forgetfulObject : NondegenerateModuleCat (A σ) :=
  (NondegenerateTensorFunctor.regularF (IsIdempotented.of_ring (A σ))
    (IsIdempotented.of_ring ℂ) (left_regular_commute σ) (left_nondegenerate σ)).obj
    regularObject

abbrev FCarrier := (forgetfulObject σ).obj.carrier

local instance : NonUnitalModule (A σ) (FCarrier σ) := (forgetfulObject σ).obj.isModule

/-- The comparison uses the actual published regular balanced tensor quotient. -/
def tensorContraction : FCarrier σ →+ ℂ :=
  RegularTensorContraction.contraction ℂ ℂ

theorem tensorContraction_injective : Function.Injective (tensorContraction σ) :=
  RegularTensorContraction.contraction_injective ℂ ℂ (IsIdempotented.of_ring ℂ)

theorem tensorContraction_action (a : A σ) (t : FCarrier σ) :
    tensorContraction σ (a • t) = σ (aRingEquiv σ a) * tensorContraction σ t := by
  have h : (tensorContraction σ).comp
        (NonUnitalModule.toEndHom (forgetfulObject σ).obj.isModule a) =
      (NonUnitalModule.toEndHom (leftAction σ) a).comp (tensorContraction σ) := by
    apply NonUnitalModuleTensor.hom_ext ℂ
    intro b n
    change (σ (aRingEquiv σ a) * b) * (show ℂ from n) =
      σ (aRingEquiv σ a) * (b * (show ℂ from n))
    exact mul_assoc _ _ _
  exact DFunLike.congr_fun h t

theorem tensor_unital (t : FCarrier σ) : (1 : A σ) • t = t := by
  apply tensorContraction_injective σ
  rw [tensorContraction_action]
  simp

/-- The coefficients are recovered from the original action, rather than supplied. -/
theorem tensorContraction_smul (c : ℂ) (t : FCarrier σ) :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
      (forgetfulObject σ).property
    tensorContraction σ (c • t) = σ c * tensorContraction σ t := by
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
    (forgetfulObject σ).property
  rw [NondegenerateScalars.complex_smul_eq (IsIdempotented.of_ring (A σ))
    (forgetfulObject σ).property c t ⟨1, IsIdempotentElem.one⟩ (tensor_unital σ t)]
  rw [tensorContraction_action]
  change σ (c * 1) * tensorContraction σ t = σ c * tensorContraction σ t
  rw [mul_one]

/-- The actual tensor functor at the regular object is the restriction module. -/
def tensorEquiv :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
      (forgetfulObject σ).property
    FCarrier σ ≃ₗ[ℂ] Carrier σ := by
  letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
    (forgetfulObject σ).property
  exact
    { toFun := fun t => (carrierRingEquiv σ).symm (tensorContraction σ t)
      invFun := fun z => NonUnitalModuleTensor.tmul ℂ ℂ ℂ 1 (carrierRingEquiv σ z)
      left_inv := by
        intro t
        apply tensorContraction_injective σ
        change 1 * tensorContraction σ t = tensorContraction σ t
        exact one_mul _
      right_inv := by
        intro z
        apply (carrierRingEquiv σ).injective
        change 1 * carrierRingEquiv σ z = carrierRingEquiv σ z
        exact one_mul _
      map_add' := by
        intro s t
        exact map_add ((carrierRingEquiv σ).symm.toAddMonoidHom.comp
          (tensorContraction σ)) s t
      map_smul' := by
        intro c t
        apply (carrierRingEquiv σ).injective
        exact tensorContraction_smul σ c t }

/-- The right-hand source functor at the actual regular input. -/
def dualForgetfulObject : NondegenerateModuleCat (A σ)ᵐᵒᵖ :=
  NonUnitalModuleDual.dualObject (IsIdempotented.of_ring (A σ)) (forgetfulObject σ)

/-- Its recovered coefficient module is exactly the ordinary full dual
of the restriction module. -/
def dualTensorEquiv :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ)).op
      (dualForgetfulObject σ).property
    (dualForgetfulObject σ).obj ≃ₗ[ℂ] Module.Dual ℂ (Carrier σ) := by
  letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ))
    (forgetfulObject σ).property
  exact (unitalDualEquiv (forgetfulObject σ) (tensor_unital σ)).trans
    (tensorEquiv σ).symm.dualMap

theorem regular_scalarMul (c : ℂ) (z : regularObject.obj) :
    (show ℂ from NondegenerateScalars.scalarMul ℂ (M := regularObject.obj)
      regularObject.property c z) =
      c * (show ℂ from z) := by
  exact (NondegenerateScalars.scalarMul_eq ℂ (IsIdempotented.of_ring ℂ)
    regularObject.property c z ⟨1, IsIdempotentElem.one⟩
      (one_mul (show ℂ from z))).trans (by
        change (c * 1) * (show ℂ from z) = c * (show ℂ from z)
        rw [mul_one])

abbrev regularDualObject : NondegenerateModuleCat ℂᵐᵒᵖ :=
  NonUnitalModuleDual.dualObject (IsIdempotented.of_ring ℂ) regularObject

theorem regularDual_apply (φ : regularDualObject.obj) (z : ℂ) :
    φ.val (show regularObject.obj from z) =
      z * φ.val (show regularObject.obj from (1 : ℂ)) := by
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
    regularObject.property
  let : SMul ℂ regularObject.obj :=
    (NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
      regularObject.property).toDistribMulAction.toDistribSMul.toSMul
  have hs : z • (show regularObject.obj from (1 : ℂ)) =
      (show regularObject.obj from z) :=
    (regular_scalarMul z (show regularObject.obj from (1 : ℂ))).trans (mul_one z)
  exact (congrArg φ.val hs.symm).trans (φ.val.map_smul z _)

def regularFunctional (t : ℂ) : regularDualObject.obj :=
  (unitalDualEquiv regularObject (fun z => one_mul (show ℂ from z))).symm
    (letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
      regularObject.property
     { toFun := fun z => t * (show ℂ from z)
       map_add' := fun z w => mul_add t (show ℂ from z) (show ℂ from w)
       map_smul' := by
         intro c z
         change t * (show ℂ from NondegenerateScalars.scalarMul ℂ
           (M := regularObject.obj) regularObject.property c z) =
             c * (t * (show ℂ from z))
         exact (congrArg (t * ·) (regular_scalarMul c z)).trans
           (mul_left_comm t c (show ℂ from z)) })

@[simp] theorem regularFunctional_apply (t : ℂ) (z : ℂ) :
    (regularFunctional t).val (show regularObject.obj from z) = t * z := rfl

abbrev pseudoDualObject : NondegenerateModuleCat (A σ)ᵐᵒᵖ :=
  (RenardRightHomFunctors.rightPseudoF (left_regular_commute σ)
    (IsIdempotented.of_ring (A σ))).obj regularDualObject

abbrev HCarrier := (pseudoDualObject σ).obj.carrier

local instance : NonUnitalModule (A σ)ᵐᵒᵖ (HCarrier σ) :=
  (pseudoDualObject σ).obj.isModule

def doubleEvaluation (h : HCarrier σ) : ℂ :=
  ((show NonUnitalModuleHom ℂᵐᵒᵖ ℂ regularDualObject.obj from h.val) 1).val
    (show regularObject.obj from (1 : ℂ))

/-- Every actual right intertwiner is determined by double evaluation. -/
theorem pseudo_apply (h : HCarrier σ) (b z : ℂ) :
    ((show NonUnitalModuleHom ℂᵐᵒᵖ ℂ regularDualObject.obj from h.val) b).val
      (show regularObject.obj from z) = doubleEvaluation σ h * b * z := by
  let f : NonUnitalModuleHom ℂᵐᵒᵖ ℂ regularDualObject.obj := h.val
  have hb : f b = op b • f 1 := by
    have hh := f.map_smul (op b) 1
    change f (1 * b) = op b • f 1 at hh
    simpa only [one_mul] using hh
  change (f b).val (show regularObject.obj from z) = _
  rw [hb]
  change (f 1).val (show regularObject.obj from b * z) = _
  rw [regularDual_apply]
  change (b * z) * doubleEvaluation σ h = doubleEvaluation σ h * b * z
  ring

def parameterHom (t : ℂ) : NonUnitalModuleHom ℂᵐᵒᵖ ℂ regularDualObject.obj where
  toFun b := regularFunctional (t * b)
  map_zero' := by
    let := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
      regularObject.property
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    change (t * 0) * (show ℂ from z) = 0
    exact (congrArg (fun w : ℂ => w * (show ℂ from z)) (mul_zero t)).trans
      (zero_mul (show ℂ from z))
  map_add' b c := by
    let := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
      regularObject.property
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    change (t * (b + c)) * (show ℂ from z) =
      (t * b) * (show ℂ from z) + (t * c) * (show ℂ from z)
    ring
  map_smul' b c := by
    let := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
      regularObject.property
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    change (t * (c * b.unop)) * (show ℂ from z) =
      (t * c) * (b.unop * (show ℂ from z))
    ring

/-- All of these intertwiners belong to the actual nondegenerate Hom part. -/
def parameter (t : ℂ) : HCarrier σ :=
  ⟨parameterHom t, (RenardRightHomFunctors.mem_rightPseudoPart
    (left_regular_commute σ) (IsIdempotented.of_ring (A σ)) (parameterHom t)).mpr
      ⟨⟨1, IsIdempotentElem.one⟩,
        fun b => congrArg (parameterHom t) (left_unital σ b)⟩⟩

@[simp] theorem doubleEvaluation_parameter (t : ℂ) :
    doubleEvaluation σ (parameter σ t) = t := by
  change (t * 1) * 1 = t
  simp

theorem parameter_doubleEvaluation (h : HCarrier σ) :
    parameter σ (doubleEvaluation σ h) = h := by
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring ℂ)
    regularObject.property
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro b
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  exact (pseudo_apply σ h b (show ℂ from z)).symm

theorem doubleEvaluation_injective : Function.Injective (doubleEvaluation σ) :=
  Function.LeftInverse.injective (parameter_doubleEvaluation σ)

@[simp] theorem doubleEvaluation_add (h k : HCarrier σ) :
    doubleEvaluation σ (h + k) = doubleEvaluation σ h + doubleEvaluation σ k := rfl

/-- The residual original right action is multiplication through `σ`. -/
theorem doubleEvaluation_action (a : A σ) (h : HCarrier σ) :
    doubleEvaluation σ (op a • h) =
      σ (aRingEquiv σ a) * doubleEvaluation σ h := by
  change ((show NonUnitalModuleHom ℂᵐᵒᵖ ℂ regularDualObject.obj from h.val)
    (σ (aRingEquiv σ a) * 1)).val (show regularObject.obj from (1 : ℂ)) = _
  rw [pseudo_apply]
  ring

theorem pseudo_unital (h : HCarrier σ) : op (1 : A σ) • h = h := by
  apply doubleEvaluation_injective σ
  rw [doubleEvaluation_action]
  simp

/-- In particular the coefficients recovered on the actual Hom part are restricted. -/
theorem doubleEvaluation_smul (c : ℂ) (h : HCarrier σ) :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ)).op
      (pseudoDualObject σ).property
    doubleEvaluation σ (c • h) = σ c * doubleEvaluation σ h := by
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ)).op
    (pseudoDualObject σ).property
  rw [NondegenerateScalars.complex_smul_eq (IsIdempotented.of_ring (A σ)).op
    (pseudoDualObject σ).property c h ⟨op 1, IsIdempotentElem.one⟩ (pseudo_unital σ h)]
  change doubleEvaluation σ (op (c • (1 : A σ)) • h) = _
  rw [doubleEvaluation_action]
  change σ (c * 1) * doubleEvaluation σ h = σ c * doubleEvaluation σ h
  rw [mul_one]

/-- The other actual source functor has precisely the restriction coefficients. -/
def homEquiv :
    letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ)).op
      (pseudoDualObject σ).property
    HCarrier σ ≃ₗ[ℂ] Carrier σ := by
  letI := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ)).op
    (pseudoDualObject σ).property
  exact
    { toFun := fun h => (carrierRingEquiv σ).symm (doubleEvaluation σ h)
      invFun := fun z => parameter σ (carrierRingEquiv σ z)
      left_inv := by
        intro h
        change parameter σ (carrierRingEquiv σ
          ((carrierRingEquiv σ).symm (doubleEvaluation σ h))) = h
        rw [RingEquiv.apply_symm_apply]
        exact parameter_doubleEvaluation σ h
      right_inv := by
        intro z
        apply (carrierRingEquiv σ).injective
        change doubleEvaluation σ (parameter σ (carrierRingEquiv σ z)) =
          carrierRingEquiv σ z
        exact doubleEvaluation_parameter σ _
      map_add' := by
        intro h k
        apply (carrierRingEquiv σ).injective
        exact doubleEvaluation_add σ h k
      map_smul' := by
        intro c h
        apply (carrierRingEquiv σ).injective
        exact doubleEvaluation_smul σ c h }

/-- A proper embedding rules out every bijective original-action intertwiner
between the actual two functor values. -/
theorem no_bijective_intertwiner (hσ : ¬ Function.Surjective σ)
    (f : NonUnitalModuleHom (A σ)ᵐᵒᵖ (HCarrier σ) (dualForgetfulObject σ).obj) :
    ¬ Function.Bijective f := by
  intro hf
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ)).op
    (pseudoDualObject σ).property
  let := NondegenerateScalars.complexModule (IsIdempotented.of_ring (A σ)).op
    (dualForgetfulObject σ).property
  let e := LinearEquiv.ofBijective
    (NondegenerateScalars.complexToLinearMap (IsIdempotented.of_ring (A σ)).op
      (pseudoDualObject σ).property (dualForgetfulObject σ).property f) hf
  exact (no_linearEquiv_dual σ hσ).false
    ((homEquiv σ).symm.trans (e.trans (dualTensorEquiv σ)))

/-- The functor values fail to be isomorphic even at the regular `B` object. -/
theorem no_objectIso (hσ : ¬ Function.Surjective σ) :
    IsEmpty (pseudoDualObject σ ≅ dualForgetfulObject σ) := by
  refine ⟨fun e => no_bijective_intertwiner σ hσ e.hom.hom ?_⟩
  let f : NonUnitalModuleHom (A σ)ᵐᵒᵖ (HCarrier σ) (dualForgetfulObject σ).obj :=
    e.hom.hom
  let g : NonUnitalModuleHom (A σ)ᵐᵒᵖ (dualForgetfulObject σ).obj (HCarrier σ) :=
    e.inv.hom
  have hl : Function.LeftInverse g f := by
    intro h
    exact congrArg (fun k : pseudoDualObject σ ⟶ pseudoDualObject σ =>
      (show NonUnitalModuleHom (A σ)ᵐᵒᵖ (HCarrier σ) (HCarrier σ) from k.hom) h)
        e.hom_inv_id
  have hr : Function.RightInverse g f := by
    intro h
    exact congrArg (fun k : dualForgetfulObject σ ⟶ dualForgetfulObject σ =>
      (show NonUnitalModuleHom (A σ)ᵐᵒᵖ (dualForgetfulObject σ).obj
        (dualForgetfulObject σ).obj from k.hom) h) e.inv_hom_id
  exact ⟨hl.injective, hr.surjective⟩

/-- The actual contravariant pseudo-forgetful-dual composite. -/
def pseudoDualFunctor :
    (NondegenerateModuleCat.{0, 0} ℂ)ᵒᵖ ⥤ NondegenerateModuleCat.{0, 0} (A σ)ᵐᵒᵖ :=
  NonUnitalModuleDual.leftToRightFunctor (IsIdempotented.of_ring ℂ) ⋙
    RenardRightHomFunctors.rightPseudoF (left_regular_commute σ)
      (IsIdempotented.of_ring (A σ))

/-- The actual contravariant dual-forgetful composite. -/
def dualForgetfulFunctor :
    (NondegenerateModuleCat.{0, 0} ℂ)ᵒᵖ ⥤ NondegenerateModuleCat.{0, 0} (A σ)ᵐᵒᵖ :=
  (NondegenerateTensorFunctor.regularF (IsIdempotented.of_ring (A σ))
    (IsIdempotented.of_ring ℂ) (left_regular_commute σ) (left_nondegenerate σ)).op ⋙
      NonUnitalModuleDual.leftToRightFunctor (IsIdempotented.of_ring (A σ))

/-- No abstract natural comparison exists for a proper self-embedding. -/
theorem no_naturalIso (hσ : ¬ Function.Surjective σ) :
    IsEmpty (pseudoDualFunctor σ ≅ dualForgetfulFunctor σ) :=
  ⟨fun e => (no_objectIso σ hσ).false (e.app (Opposite.op regularObject))⟩

/-- The obstruction is unconditional: a proper self-embedding has been constructed. -/
theorem exists_counterexample :
    ∃ σ : ℂ →+* ℂ, ¬ Function.Surjective σ ∧
      IsEmpty (pseudoDualFunctor σ ≅ dualForgetfulFunctor σ) := by
  obtain ⟨σ, hσ⟩ := exists_nonsurjective_endomorphism
  exact ⟨σ, hσ, no_naturalIso σ hσ⟩

end Actions

end Langlands.Algebra.RenardDualitySourceObstruction
