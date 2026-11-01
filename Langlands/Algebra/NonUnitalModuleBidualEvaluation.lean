import Langlands.Algebra.NonUnitalModuleDualFunctor

/-!
# Canonical evaluation into the actual nondegenerate bidual

Renard, I.4.1, printed p.23 / PDF p.29. An original fixing idempotent
puts evaluation in the actual second dual before any separation argument.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDual

open MulOpposite CategoryTheory

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

section Original

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hM) := fullAction hA hM
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ
    (FullDual hA.op (isNondegenerate hA hM)) := fullAction hA.op (isNondegenerate hA hM)

/-- The actual second nondegenerate dual, with no change of carrier. -/
abbrev Bidual := Dual hA.op (isNondegenerate hA hM)

/-- The original `A` action is the specified double-opposite transport. -/
@[instance_reducible]
def bidualAction : NonUnitalModule A (Bidual hA hM) :=
  fromDoubleOppositeAction

theorem bidual_carrier : Bidual hA hM = Dual hA.op (isNondegenerate hA hM) := rfl

theorem bidualAction_eq : bidualAction hA hM =
    fromDoubleOppositeAction (A := A) (M := Dual hA.op (isNondegenerate hA hM)) := rfl

/-- Full evaluation on the actual first dual, with its recovered complex scalars. -/
def fullEvaluation (m : M) : FullDual hA.op (isNondegenerate hA hM) := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
  exact
    { toFun := fun φ => φ.val m
      map_add' _ _ := rfl
      map_smul' c φ := canonical_smul_apply hA hM c φ m }

theorem fullEvaluation_coe (m : M) :
    ⇑(fullEvaluation hA hM m) = fun φ => φ.val m := rfl

@[simp] theorem fullEvaluation_apply (m : M) (φ : Dual hA hM) :
    fullEvaluation hA hM m φ = φ.val m := rfl

/-- Full evaluation is complex linear also in the original vector. -/
def fullEvaluationLinear :
    letI := NondegenerateScalars.complexModule hA hM
    M →ₗ[ℂ] FullDual hA.op (isNondegenerate hA hM) := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
  exact
    { toFun := fullEvaluation hA hM
      map_add' m n := fullDual_ext hA.op (isNondegenerate hA hM)
        (fun φ => φ.val.map_add m n)
      map_smul' c m := fullDual_ext hA.op (isNondegenerate hA hM)
        (fun φ => φ.val.map_smul c m) }

theorem fullEvaluationLinear_coe :
    letI := NondegenerateScalars.complexModule hA hM
    ⇑(fullEvaluationLinear hA hM) = fullEvaluation hA hM := rfl

/-- Every original local fixer of `m` fixes the full evaluation functional. -/
theorem fullEvaluation_fixed (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    op (op (e : A)) • fullEvaluation hA hM m = fullEvaluation hA hM m := by
  apply fullDual_ext hA.op (isNondegenerate hA hM)
  intro φ
  change φ.val ((e : A) • m) = φ.val m
  rw [he]

/-- Membership uses the local fixer of the original vector, without separation. -/
theorem fullEvaluation_mem (m : M) :
    fullEvaluation hA hM m ∈
      nondegeneratePart hA.op.op (FullDual hA.op (isNondegenerate hA hM)) := by
  obtain ⟨e, he⟩ := hM m
  refine ⟨⟨op (op (e : A)), ?_⟩, fullEvaluation_fixed hA hM m e he⟩
  change op (op (e.val * e.val)) = op (op e.val)
  exact congrArg (fun a : A => op (op a)) e.property.eq

local instance : NonUnitalModule A (Bidual hA hM) := bidualAction hA hM

/-- The transported actual second dual is intrinsically nondegenerate over `A`. -/
theorem bidual_isNondegenerate : IsNondegenerate A (Bidual hA hM) :=
  fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op (isNondegenerate hA hM))

theorem bidualAction_smul_val (a : A) (Φ : Bidual hA hM) :
    (a • Φ).val = Φ.val.comp
      (NondegenerateScalars.toLinearEndHom ℂ hA.op (isNondegenerate hA hM) (op a)) := rfl

@[simp] theorem bidualAction_smul_apply (a : A) (Φ : Bidual hA hM) (φ : Dual hA hM) :
    (a • Φ).val φ = Φ.val (op a • φ) := rfl

/-- Renard's canonical map into the actual nondegenerate bidual. -/
def evaluation : NonUnitalModuleHom A M (Bidual hA hM) where
  toFun m := ⟨fullEvaluation hA hM m, fullEvaluation_mem hA hM m⟩
  map_zero' := by
    apply dual_ext hA.op (isNondegenerate hA hM)
    intro φ
    let _ := NondegenerateScalars.complexModule hA hM
    exact φ.val.map_zero
  map_add' m n := by
    apply dual_ext hA.op (isNondegenerate hA hM)
    intro φ
    let _ := NondegenerateScalars.complexModule hA hM
    exact φ.val.map_add m n
  map_smul' a m := by
    apply dual_ext hA.op (isNondegenerate hA hM)
    intro φ
    rfl

/-- Equality of the entire included functional. -/
theorem evaluation_val (m : M) : (evaluation hA hM m).val = fullEvaluation hA hM m := rfl

@[simp] theorem evaluation_apply (m : M) (φ : Dual hA hM) :
    (evaluation hA hM m).val φ = φ.val m := rfl

theorem evaluation_coe : ⇑(evaluation hA hM) =
    fun m => ⟨fullEvaluation hA hM m, fullEvaluation_mem hA hM m⟩ := rfl

theorem evaluation_map_smul (a : A) (m : M) :
    evaluation hA hM (a • m) = a • evaluation hA hM m :=
  (evaluation hA hM).map_smul a m

/-- The same map for the precisely recovered source and target complex structures. -/
def evaluationLinear :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    M →ₗ[ℂ] Bidual hA hM :=
  NondegenerateScalars.complexToLinearMap hA hM (bidual_isNondegenerate hA hM)
    (evaluation hA hM)

theorem evaluationLinear_toAddMonoidHom :
    (evaluationLinear hA hM).toAddMonoidHom = (evaluation hA hM).toAddMonoidHom := rfl

@[simp] theorem evaluationLinear_apply (m : M) (φ : Dual hA hM) :
    (evaluationLinear hA hM m).val φ = φ.val m := rfl

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  (hN : IsNondegenerate A N)

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hN) := fullAction hA hN
local instance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ
    (FullDual hA.op (isNondegenerate hA hN)) := fullAction hA.op (isNondegenerate hA hN)
local instance : NonUnitalModule A (Bidual hA hN) := bidualAction hA hN

/-- Twice the actual pullback, then the specified original-ring transport. -/
def doublePullback (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom A (Bidual hA hM) (Bidual hA hN) :=
  fromDoubleOppositeMap
    (pullback hA.op (isNondegenerate hA hN) (isNondegenerate hA hM)
      (pullback hA hM hN f))

theorem doublePullback_eq (f : NonUnitalModuleHom A M N) :
    doublePullback hA hM hN f = fromDoubleOppositeMap
      (pullback hA.op (isNondegenerate hA hN) (isNondegenerate hA hM)
        (pullback hA hM hN f)) := rfl

/-- The whole included functional is the actual second pullback. -/
theorem doublePullback_val (f : NonUnitalModuleHom A M N) (Φ : Bidual hA hM) :
    (doublePullback hA hM hN f Φ).val =
      fullPullback hA.op (isNondegenerate hA hN) (isNondegenerate hA hM)
        (pullback hA hM hN f) Φ.val := rfl

@[simp] theorem doublePullback_apply (f : NonUnitalModuleHom A M N)
    (Φ : Bidual hA hM) (φ : Dual hA hN) :
    (doublePullback hA hM hN f Φ).val φ = Φ.val (pullback hA hM hN f φ) := rfl

/-- Naturality is equality of the entire original bundled intertwiners. -/
theorem evaluation_naturality (f : NonUnitalModuleHom A M N) :
    (doublePullback hA hM hN f).comp (evaluation hA hM) =
      (evaluation hA hN).comp f := by
  apply NonUnitalModuleHom.ext
  intro m
  exact dual_ext hA.op (isNondegenerate hA hN) (fun _ => rfl)

end Original

section Categorical

/-- Exactly the published left-to-right/right-to-left categorical composite. -/
abbrev bidualFunctor (hA : IsIdempotented A) :
    NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uA, uM} A :=
  (leftToRightFunctor hA).rightOp ⋙ rightToLeftFunctor hA

theorem bidualFunctor_eq (hA : IsIdempotented A) :
    bidualFunctor.{uA, uM} hA =
      (leftToRightFunctor hA).rightOp ⋙ rightToLeftFunctor hA := rfl

theorem bidualFunctor_obj (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (bidualFunctor hA).obj M = rightDualObject hA (dualObject hA M) := rfl

theorem bidualFunctor_obj_carrier (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((bidualFunctor hA).obj M).obj.carrier = Bidual hA M.property := rfl

theorem bidualFunctor_obj_action (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((bidualFunctor hA).obj M).obj.isModule = bidualAction hA M.property := rfl

theorem bidualFunctor_obj_smul_val (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (a : A)
    (Φ : ((bidualFunctor hA).obj M).obj) :
    (@SMul.smul A _ ((bidualFunctor hA).obj M).obj.isModule.toDistribSMul.toSMul a Φ).val =
      Φ.val.comp
        (NondegenerateScalars.toLinearEndHom ℂ hA.op
          (isNondegenerate hA M.property) (op a)) := rfl

@[simp] theorem bidualFunctor_obj_smul_apply (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (a : A)
    (Φ : ((bidualFunctor hA).obj M).obj) (φ : (dualObject hA M).obj) :
    (@SMul.smul A _ ((bidualFunctor hA).obj M).obj.isModule.toDistribSMul.toSMul a Φ).val φ =
      Φ.val (op a • φ) := rfl

theorem bidualFunctor_map_hom (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    letI := bidualAction hA M.property
    letI := bidualAction hA N.property
    ((bidualFunctor hA).map f).hom = doublePullback hA M.property N.property f.hom := rfl

theorem bidualFunctor_map_val (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (Φ : ((bidualFunctor hA).obj M).obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((bidualFunctor hA).map f).hom Φ).val =
      fullPullback hA.op (isNondegenerate hA N.property) (isNondegenerate hA M.property)
        (pullback hA M.property N.property f.hom) Φ.val := rfl

@[simp] theorem bidualFunctor_map_apply (hA : IsIdempotented A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (Φ : ((bidualFunctor hA).obj M).obj) (φ : (dualObject hA N).obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((bidualFunctor hA).map f).hom Φ).val φ =
      Φ.val (pullback hA M.property N.property f.hom φ) := rfl

/-- The canonical evaluation is a natural transformation into this actual composite. -/
def evaluationNatTrans (hA : IsIdempotented A) :
    𝟭 (NondegenerateModuleCat.{uA, uM} A) ⟶ bidualFunctor hA where
  app M := ObjectProperty.homMk (evaluation hA M.property)
  naturality {M N} f := by
    apply ObjectProperty.hom_ext
    exact (evaluation_naturality hA M.property N.property f.hom).symm

theorem evaluationNatTrans_app_hom (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    letI := bidualAction hA M.property
    ((evaluationNatTrans hA).app M).hom = evaluation hA M.property := rfl

theorem evaluationNatTrans_app_toAddMonoidHom (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    letI := bidualAction hA M.property
    ((evaluationNatTrans hA).app M).hom.toAddMonoidHom =
      (evaluation hA M.property).toAddMonoidHom := rfl

theorem evaluationNatTrans_app_val (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (m : M.obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((evaluationNatTrans hA).app M).hom m).val =
      fullEvaluation hA M.property m := rfl

@[simp] theorem evaluationNatTrans_app_apply (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (m : M.obj) (φ : (dualObject hA M).obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((evaluationNatTrans hA).app M).hom m).val φ =
      φ.val m := rfl

end Categorical

end Langlands.Algebra.NonUnitalModuleDual
