import Langlands.Algebra.NonUnitalModuleCornerInduction

/-!
# Evaluation for actual corner induction

The original-action balanced pairing underlying Renard (9 July 2026), I.3.2,
printed pp.21–22/PDF pp.27–28, and its additive natural transformations.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerEvaluation

open CategoryTheory
open NonUnitalModuleCorner NonUnitalModuleCornerInduction

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A]

attribute [local instance] rightCornerModule cornerModule tensorModule

section Pointwise

variable (e : Idempotent A) (M : Type uM) [AddCommGroup M] [hM : NonUnitalModule A M]

/-- The biadditive pairing uses the specified original action on `M`. -/
def pairing : A →+ FixedPart e M →+ M where
  toFun a :=
    { toFun := fun z => a • z.val
      map_zero' := smul_zero a
      map_add' := fun z w => smul_add a z.val w.val }
  map_zero' := AddMonoidHom.ext (fun z => NonUnitalModule.zero_smul z.val)
  map_add' a b := AddMonoidHom.ext (fun z => NonUnitalModule.add_smul a b z.val)

theorem pairing_function :
    (fun a z => pairing e M a z) =
      fun a z => hM.toDistribSMul.toSMul.smul a z.val := rfl

@[simp] theorem pairing_apply (a : A) (z : FixedPart e M) :
    pairing e M a z = a • z.val := rfl

/-- Balancing uses actual right multiplication and the inherited corner action. -/
theorem pairing_balancing (c : Idempotent.Corner e) (a : A) (z : FixedPart e M) :
    pairing e M (a * Idempotent.Corner.toAmbient e c) z =
      pairing e M a ((fixedPartModule e M).toSMul.smul c z) := by
  exact mul_smul a (Idempotent.Corner.toAmbient e c) z.val

theorem pairing_isBalanced :
    NonUnitalModuleTensor.IsBalanced (Idempotent.Corner e) (pairing e M) :=
  fun c a z => pairing_balancing e M c a z

/-- Equivariance in the regular left factor uses the original associativity law. -/
theorem pairing_left_linear (a₀ a : A) (z : FixedPart e M) :
    pairing e M (a₀ * a) z = a₀ • pairing e M a z :=
  mul_smul a₀ a z.val

/-- The actual quotient lift, bundled with the named residual original action. -/
def evaluation :
    @NonUnitalModuleHom A (Tensor e (FixedPart e M)) M _
      (tensorAddCommGroup e (FixedPart e M)) _
      (tensorModule e (FixedPart e M)) hM := by
  letI := NonUnitalModule.regular A
  exact NonUnitalBimoduleTensor.leftLift (regularCornerCommute e)
    (pairing e M) (pairing_isBalanced e M) (pairing_left_linear e M)

/-- Equality of complete additive maps with the published balanced-quotient lift. -/
theorem evaluation_toAddMonoidHom :
    (evaluation e M).toAddMonoidHom =
      NonUnitalModuleTensor.lift (Idempotent.Corner e)
        (pairing e M) (pairing_isBalanced e M) := rfl

@[simp] theorem evaluation_tmul (a : A) (z : FixedPart e M) :
    evaluation e M (tmul e a z) = a • z.val := rfl

/-- Evaluation at the idempotent recovers the original fixed vector. -/
@[simp] theorem evaluation_idempotent (z : FixedPart e M) :
    evaluation e M (tmul e (e : A) z) = z.val :=
  z.property

theorem evaluation_map_smul (a : A) (t : Tensor e (FixedPart e M)) :
    evaluation e M ((tensorModule e (FixedPart e M)).toDistribSMul.toSMul.smul a t) =
      hM.toDistribSMul.toSMul.smul a (evaluation e M t) :=
  (evaluation e M).map_smul a t

/-- Pure-tensor values determine the whole original intertwiner. -/
theorem evaluation_unique
    (F : @NonUnitalModuleHom A (Tensor e (FixedPart e M)) M _
      (tensorAddCommGroup e (FixedPart e M)) _
      (tensorModule e (FixedPart e M)) hM)
    (hF : ∀ a z, F (tmul e a z) = a • z.val) :
    F = evaluation e M := by
  apply NonUnitalModuleHom.ext
  exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext (Idempotent.Corner e) hF)

end Pointwise

section Naturality

variable (e : Idempotent A)
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [hM : NonUnitalModule A M] [hN : NonUnitalModule A N]

/-- Naturality is equality of whole intertwiners for independent carrier universes. -/
theorem evaluation_naturality (f : NonUnitalModuleHom A M N) :
    f.comp (evaluation e M) =
      (evaluation e N).comp (inducedMap e (restrict e f)) := by
  apply NonUnitalModuleHom.ext
  apply DFunLike.congr_fun
  apply NonUnitalModuleTensor.hom_ext (Idempotent.Corner e)
  intro a z
  exact f.map_smul a z.val

theorem evaluation_naturality_toAddMonoidHom (f : NonUnitalModuleHom A M N) :
    f.toAddMonoidHom.comp (evaluation e M).toAddMonoidHom =
      (evaluation e N).toAddMonoidHom.comp
        (inducedMap e (restrict e f)).toAddMonoidHom :=
  congrArg NonUnitalModuleHom.toAddMonoidHom (evaluation_naturality e f)

theorem evaluation_naturality_apply (f : NonUnitalModuleHom A M N)
    (t : Tensor e (FixedPart e M)) :
    f (evaluation e M t) = evaluation e N (inducedMap e (restrict e f) t) :=
  congrArg (fun F => F t) (evaluation_naturality e f)

end Naturality

/-- Evaluation as an actual natural transformation at the tensor carrier bound. -/
def ambientEvaluation (e : Idempotent A) :
    NonUnitalModuleCorner.functor.{uA, max uA uM} e ⋙
        ambientFunctor.{uA, max uA uM} e ⟶
      𝟭 (NonUnitalModuleCat.{uA, max uA uM} A) where
  app M := evaluation e M
  naturality _ _ f := (evaluation_naturality e f).symm

theorem ambientEvaluation_app (e : Idempotent A)
    (M : NonUnitalModuleCat.{uA, max uA uM} A) :
    (ambientEvaluation e).app M = evaluation e M := rfl

theorem ambientEvaluation_app_toAddMonoidHom (e : Idempotent A)
    (M : NonUnitalModuleCat.{uA, max uA uM} A) :
    ((ambientEvaluation e).app M).toAddMonoidHom =
      NonUnitalModuleTensor.lift (Idempotent.Corner e)
        (pairing e M) (pairing_isBalanced e M) := rfl

@[simp] theorem ambientEvaluation_app_tmul (e : Idempotent A)
    (M : NonUnitalModuleCat.{uA, max uA uM} A) (a : A) (z : FixedPart e M) :
    ((ambientEvaluation e).app M).toAddMonoidHom (tmul e a z) = a • z.val := rfl

theorem ambientEvaluation_naturality (e : Idempotent A)
    {M N : NonUnitalModuleCat.{uA, max uA uM} A} (f : M ⟶ N) :
    f.comp ((ambientEvaluation e).app M) =
      ((ambientEvaluation e).app N).comp (inducedMap e (restrict e f)) :=
  evaluation_naturality e f

/-- The same components in the full nondegenerate subcategory. -/
def nondegenerateEvaluation (hA : IsIdempotented A) (e : Idempotent A) :
    NonUnitalModuleCorner.nondegenerateFunctor.{uA, max uA uM} e ⋙
        NonUnitalModuleCornerInduction.nondegenerateFunctor.{uA, max uA uM} hA e ⟶
      𝟭 (NondegenerateModuleCat.{uA, max uA uM} A) where
  app M := ObjectProperty.homMk (evaluation e M.obj)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (evaluation_naturality e f.hom).symm

theorem nondegenerateEvaluation_app (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    (nondegenerateEvaluation hA e).app M =
      ObjectProperty.homMk (evaluation e M.obj) := rfl

theorem nondegenerateEvaluation_app_hom (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    ((nondegenerateEvaluation hA e).app M).hom = evaluation e M.obj := rfl

theorem nondegenerateEvaluation_app_toAddMonoidHom
    (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    ((nondegenerateEvaluation hA e).app M).hom.toAddMonoidHom =
      NonUnitalModuleTensor.lift (Idempotent.Corner e)
        (pairing e M.obj) (pairing_isBalanced e M.obj) := rfl

@[simp] theorem nondegenerateEvaluation_app_tmul
    (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) (a : A) (z : FixedPart e M.obj) :
    ((nondegenerateEvaluation hA e).app M).hom.toAddMonoidHom (tmul e a z) =
      a • z.val := rfl

theorem nondegenerateEvaluation_naturality
    (hA : IsIdempotented A) (e : Idempotent A)
    {M N : NondegenerateModuleCat.{uA, max uA uM} A} (f : M ⟶ N) :
    f.hom.comp ((nondegenerateEvaluation hA e).app M).hom =
      ((nondegenerateEvaluation hA e).app N).hom.comp
        (inducedMap e (restrict e f.hom)) :=
  evaluation_naturality e f.hom

/-- The actual inclusion sends each whole component to ambient evaluation. -/
theorem inclusion_app (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    (nondegenerateInclusion A).map ((nondegenerateEvaluation hA e).app M) =
      (ambientEvaluation e).app ((nondegenerateInclusion A).obj M) := rfl

/-- Under inclusion, both sides of whole-map naturality are the ambient sides. -/
theorem inclusion_naturality (hA : IsIdempotented A) (e : Idempotent A)
    {M N : NondegenerateModuleCat.{uA, max uA uM} A} (f : M ⟶ N) :
    ((nondegenerateInclusion A).map f).comp
        ((nondegenerateInclusion A).map ((nondegenerateEvaluation hA e).app M)) =
      ((ambientEvaluation e).app N.obj).comp
        (inducedMap e (restrict e ((nondegenerateInclusion A).map f))) :=
  evaluation_naturality e f.hom

end Langlands.Algebra.NonUnitalModuleCornerEvaluation
