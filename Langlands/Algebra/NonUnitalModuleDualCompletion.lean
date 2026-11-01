import Langlands.Algebra.NonUnitalModuleCompletionFunctor
import Langlands.Algebra.NonUnitalModuleDualFixedPartMaps

/-!
# The full dual and the completion of the nondegenerate dual

Renard (9 July 2026), I.4.3, printed p.25 / PDF31. The two actual maps between
the full complex dual `M*` and the completion of the nondegenerate dual `M~`,
realized directly on actual compatible families of actual dual vectors.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualCompletion

open MulOpposite
open NonUnitalModuleDual (FullDual Dual)
open NonUnitalModuleDualFixedPartMaps (oppositeIdempotent)

universe uA uM

/-- A right local unit for one element of an idempotented ring. -/
private theorem exists_rightUnit {B : Type*} [NonUnitalRing B] (hB : IsIdempotented B)
    (b : B) : ∃ f : Idempotent B, b * (f : B) = b := by
  classical
  obtain ⟨f, hf⟩ := (IsIdempotented.iff_two_sided_local_units.mp hB) {b}
  exact ⟨f, (hf b (by simp)).2⟩

section Order

variable {A : Type uA} [NonUnitalRing A]

/-- The published opposite idempotent preserves Renard's corner order. -/
theorem oppositeIdempotent_le {e f : Idempotent A} (h : e ≤ f) :
    oppositeIdempotent e ≤ oppositeIdempotent f := by
  obtain ⟨h₁, h₂⟩ := (Idempotent.le_iff_mul e f).mp h
  refine (Idempotent.le_iff_mul _ _).mpr ⟨?_, ?_⟩
  · change op ((e : A) * f) = op (e : A)
    rw [h₂]
  · change op ((f : A) * e) = op (e : A)
    rw [h₁]

end Order

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

attribute [local instance] NonUnitalModuleDual.fullAction NonUnitalModuleDual.dualAction

section Scalars

variable (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The completion is exactly the published completion functor's object at the dual. -/
theorem completion_eq_functor_obj :
    ((nondegenerateModuleCompletionFunctor hA.op).obj
        ⟨NonUnitalModuleCat.of Aᵐᵒᵖ (Dual hA hM), NonUnitalModuleDual.isNondegenerate hA hM⟩ :
      Type (max uA uM)) = NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) := rfl

/-- The completion functor's object carries exactly the published family action. -/
theorem completion_functor_obj_action :
    ((nondegenerateModuleCompletionFunctor hA.op).obj
        ⟨NonUnitalModuleCat.of Aᵐᵒᵖ (Dual hA hM),
          NonUnitalModuleDual.isNondegenerate hA hM⟩).isModule =
      NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op := rfl

/-- The pointwise complex module on actual compatible families of actual dual vectors,
using the published scalar module on the nondegenerate dual. -/
@[instance_reducible]
def completionModule : Module ℂ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) := by
  letI := NonUnitalModuleDual.dualModule hA hM
  letI := NonUnitalModuleDual.dual_smulCommClass hA hM
  exact
    { smul c x := ⟨fun e => c • x.val e, by
        constructor
        · intro e
          change (e : Aᵐᵒᵖ) • (c • x.val e) = c • x.val e
          rw [← smul_comm c (e : Aᵐᵒᵖ) (x.val e), x.property.1 e]
        · intro e f hef
          change (e : Aᵐᵒᵖ) • (c • x.val f) = c • x.val e
          rw [← smul_comm c (e : Aᵐᵒᵖ) (x.val f), x.property.2 e f hef]⟩
      one_smul x := Subtype.ext (funext fun e => one_smul ℂ (x.val e))
      mul_smul c d x := Subtype.ext (funext fun e => mul_smul c d (x.val e))
      smul_zero c := Subtype.ext (funext fun _ => smul_zero c)
      smul_add c x y := Subtype.ext (funext fun e => smul_add c (x.val e) (y.val e))
      add_smul c d x := Subtype.ext (funext fun e => add_smul c d (x.val e))
      zero_smul x := Subtype.ext (funext fun e => zero_smul ℂ (x.val e)) }

/-- Equality of the entire scaled family. -/
theorem completionModule_smul_coe (c : ℂ) (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :
    letI := NonUnitalModuleDual.dualModule hA hM
    letI := completionModule hA hM
    (c • x).val = fun e => c • x.val e := rfl

/-- At every actual coordinate the scalar operation is `c • x(e)` in the actual dual. -/
theorem completionModule_smul_val (c : ℂ) (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))
    (e : Idempotent Aᵐᵒᵖ) :
    letI := NonUnitalModuleDual.dualModule hA hM
    letI := completionModule hA hM
    (c • x).val e = c • x.val e := rfl

/-- Equality of the entire included full-dual functional at every coordinate. -/
theorem completionModule_smul_functional (c : ℂ)
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (e : Idempotent Aᵐᵒᵖ) :
    letI := completionModule hA hM
    ((c • x).val e).val = c • (x.val e).val := rfl

@[simp] theorem completionModule_smul_apply (c : ℂ)
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (e : Idempotent Aᵐᵒᵖ) (m : M) :
    letI := completionModule hA hM
    ((c • x).val e).val m = c • (x.val e).val m := rfl

/-- Compatibility with the unchanged published family action. -/
theorem completion_isScalarTower :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    letI := completionModule hA hM
    IsScalarTower ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
  let _ := completionModule hA hM
  let _ := NonUnitalModuleDual.dualModule hA hM
  let _ := NonUnitalModuleDual.dual_isScalarTower hA hM
  refine ⟨fun c a x => ?_⟩
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := exists_rightUnit hA.op ((e : Aᵐᵒᵖ) * a)
  have hf' : ((e : Aᵐᵒᵖ) * (c • a)) * (f : Aᵐᵒᵖ) = (e : Aᵐᵒᵖ) * (c • a) := by
    rw [mul_smul_comm, smul_mul_assoc, hf]
  change ((c • a) • x).val e = c • (a • x).val e
  rw [NonUnitalModuleLeftLimit.smul_val hA.op (c • a) x e f hf',
    NonUnitalModuleLeftLimit.smul_val hA.op a x e f hf, mul_smul_comm, smul_assoc]

theorem completion_smulCommClass :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    letI := completionModule hA hM
    SMulCommClass ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
  let _ := completionModule hA hM
  let _ := NonUnitalModuleDual.dualModule hA hM
  let _ := NonUnitalModuleDual.dual_smulCommClass hA hM
  refine ⟨fun c a x => ?_⟩
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := exists_rightUnit hA.op ((e : Aᵐᵒᵖ) * a)
  change c • (a • x).val e = (a • (c • x)).val e
  rw [NonUnitalModuleLeftLimit.smul_val hA.op a x e f hf,
    NonUnitalModuleLeftLimit.smul_val hA.op a (c • x) e f hf]
  exact smul_comm c ((e : Aᵐᵒᵖ) * a) (x.val f)

end Scalars

section Forward

variable (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The full functional `e • φ`, viewed in the actual dual with `e` itself as fixer. -/
def forwardCoordinate (e : Idempotent Aᵐᵒᵖ) (φ : FullDual hA hM) : Dual hA hM :=
  ⟨(e : Aᵐᵒᵖ) • φ, ⟨e, by rw [← mul_smul, e.property.eq]⟩⟩

theorem forwardCoordinate_eq (e : Idempotent Aᵐᵒᵖ) (φ : FullDual hA hM) :
    forwardCoordinate hA hM e φ =
      ⟨(e : Aᵐᵒᵖ) • φ, ⟨e, by rw [← mul_smul, e.property.eq]⟩⟩ := rfl

@[simp] theorem forwardCoordinate_val (e : Idempotent Aᵐᵒᵖ) (φ : FullDual hA hM) :
    (forwardCoordinate hA hM e φ).val = (e : Aᵐᵒᵖ) • φ := rfl

/-- Coordinate fixation. -/
theorem forwardCoordinate_fixed (e : Idempotent Aᵐᵒᵖ) (φ : FullDual hA hM) :
    (e : Aᵐᵒᵖ) • forwardCoordinate hA hM e φ = forwardCoordinate hA hM e φ := by
  apply Subtype.ext
  change (e : Aᵐᵒᵖ) • ((e : Aᵐᵒᵖ) • φ) = (e : Aᵐᵒᵖ) • φ
  rw [← mul_smul, e.property.eq]

/-- Coordinate coherence. -/
theorem forwardCoordinate_coherent {e f : Idempotent Aᵐᵒᵖ} (hef : e ≤ f)
    (φ : FullDual hA hM) :
    (e : Aᵐᵒᵖ) • forwardCoordinate hA hM f φ = forwardCoordinate hA hM e φ := by
  apply Subtype.ext
  change (e : Aᵐᵒᵖ) • ((f : Aᵐᵒᵖ) • φ) = (e : Aᵐᵒᵖ) • φ
  rw [← mul_smul, ((Idempotent.le_iff_mul e f).mp hef).2]

/-- The actual forward map `M* → (M~)_A`. -/
def toCompletion (φ : FullDual hA hM) : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  ⟨fun e => forwardCoordinate hA hM e φ, by
    constructor
    · intro e
      exact forwardCoordinate_fixed hA hM e φ
    · intro e f hef
      exact forwardCoordinate_coherent hA hM hef φ⟩

theorem toCompletion_val (φ : FullDual hA hM) (e : Idempotent Aᵐᵒᵖ) :
    (toCompletion hA hM φ).val e = forwardCoordinate hA hM e φ := rfl

/-- Equality of the complete coordinate functional. -/
theorem toCompletion_functional (φ : FullDual hA hM) (e : Idempotent Aᵐᵒᵖ) :
    ((toCompletion hA hM φ).val e).val = (e : Aᵐᵒᵖ) • φ := rfl

/-- The entire coordinate function, through the published full action. -/
theorem toCompletion_coe (φ : FullDual hA hM) (e : Idempotent Aᵐᵒᵖ) :
    ⇑((toCompletion hA hM φ).val e).val = fun m => φ (e.val.unop • m) := rfl

@[simp] theorem toCompletion_apply (φ : FullDual hA hM) (e : Idempotent Aᵐᵒᵖ) (m : M) :
    ((toCompletion hA hM φ).val e).val m = φ (e.val.unop • m) := rfl

theorem toCompletion_fixed (φ : FullDual hA hM) (e : Idempotent Aᵐᵒᵖ) :
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val e = (toCompletion hA hM φ).val e :=
  (toCompletion hA hM φ).property.1 e

theorem toCompletion_coherent (φ : FullDual hA hM) {e f : Idempotent Aᵐᵒᵖ} (hef : e ≤ f) :
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val f = (toCompletion hA hM φ).val e :=
  (toCompletion hA hM φ).property.2 e f hef

theorem toCompletion_zero : toCompletion hA hM 0 = 0 :=
  Subtype.ext (funext fun e => Subtype.ext (smul_zero (e : Aᵐᵒᵖ)))

theorem toCompletion_add (φ ψ : FullDual hA hM) :
    toCompletion hA hM (φ + ψ) = toCompletion hA hM φ + toCompletion hA hM ψ :=
  Subtype.ext (funext fun e => Subtype.ext (smul_add (e : Aᵐᵒᵖ) φ ψ))

theorem toCompletion_complex_smul (c : ℂ) (φ : FullDual hA hM) :
    letI := completionModule hA hM
    toCompletion hA hM (c • φ) = c • toCompletion hA hM φ := by
  let _ := completionModule hA hM
  let _ := NonUnitalModuleDual.full_smulCommClass hA hM
  exact Subtype.ext (funext fun e => Subtype.ext (smul_comm c (e : Aᵐᵒᵖ) φ).symm)

/-- Right-action equivariance for the published full and family actions. -/
theorem toCompletion_action (a : Aᵐᵒᵖ) (φ : FullDual hA hM) :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    toCompletion hA hM (a • φ) = a • toCompletion hA hM φ := by
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := exists_rightUnit hA.op ((e : Aᵐᵒᵖ) * a)
  rw [NonUnitalModuleLeftLimit.smul_val hA.op a _ e f hf]
  apply Subtype.ext
  change (e : Aᵐᵒᵖ) • (a • φ) = ((e : Aᵐᵒᵖ) * a) • ((f : Aᵐᵒᵖ) • φ)
  rw [← mul_smul ((e : Aᵐᵒᵖ) * a) (f : Aᵐᵒᵖ) φ, hf, mul_smul]

/-- The forward map as an additive map. -/
def toCompletionAddHom : FullDual hA hM →+ NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) where
  toFun := toCompletion hA hM
  map_zero' := toCompletion_zero hA hM
  map_add' := toCompletion_add hA hM

@[simp] theorem toCompletionAddHom_apply (φ : FullDual hA hM) :
    toCompletionAddHom hA hM φ = toCompletion hA hM φ := rfl

/-- The forward map as a complex-linear map. -/
def toCompletionLinear :
    letI := completionModule hA hM
    FullDual hA hM →ₗ[ℂ] NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  letI := completionModule hA hM
  { toFun := toCompletion hA hM
    map_add' := toCompletion_add hA hM
    map_smul' := toCompletion_complex_smul hA hM }

theorem toCompletionLinear_coe :
    letI := completionModule hA hM
    ⇑(toCompletionLinear hA hM) = toCompletion hA hM := rfl

/-- The complex-linear package has exactly the specified additive map. -/
theorem toCompletionLinear_toAddMonoidHom :
    letI := completionModule hA hM
    (toCompletionLinear hA hM).toAddMonoidHom = toCompletionAddHom hA hM := rfl

/-- The forward map as an original intertwiner of right modules. -/
def toCompletionHom :
    @NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA hM) (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))
      _ _ _ (NonUnitalModuleDual.fullAction hA hM)
      (NonUnitalModuleLeftLimit.nonUnitalModule hA.op) := by
  letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
  exact
    { toAddMonoidHom := toCompletionAddHom hA hM
      map_smul' := toCompletion_action hA hM }

/-- The intertwiner package has exactly the specified additive map. -/
theorem toCompletionHom_toAddMonoidHom :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    (toCompletionHom hA hM).toAddMonoidHom = toCompletionAddHom hA hM := rfl

@[simp] theorem toCompletionHom_apply (φ : FullDual hA hM) :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    toCompletionHom hA hM φ = toCompletion hA hM φ := rfl

end Forward

section Reverse

variable (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- Compatible-family coherence moves an evaluation to a larger fixing idempotent. -/
theorem coordinate_apply_eq_of_le (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))
    {e f : Idempotent A} (hef : e ≤ f) {m : M} (he : (e : A) • m = m) :
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m := by
  have hx := x.property.2 (oppositeIdempotent e) (oppositeIdempotent f)
    (oppositeIdempotent_le hef)
  calc
    (x.val (oppositeIdempotent e)).val m =
        ((oppositeIdempotent e : Aᵐᵒᵖ) • x.val (oppositeIdempotent f)).val m := by
      rw [hx]
    _ = (x.val (oppositeIdempotent f)).val ((e : A) • m) := rfl
    _ = (x.val (oppositeIdempotent f)).val m := by rw [he]

/-- Independence of the fixing idempotent, through a common upper bound. -/
theorem coordinate_apply_independent (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))
    (m : M) (e f : Idempotent A) (he : (e : A) • m = m) (hf : (f : A) • m = m) :
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  rw [coordinate_apply_eq_of_le hA hM x (hg e (by simp)) he,
    coordinate_apply_eq_of_le hA hM x (hg f (by simp)) hf]

/-- The implementation's value, using a chosen fixing idempotent. -/
private def fullValue (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (m : M) : ℂ :=
  (x.val (oppositeIdempotent (hM m).choose)).val m

private theorem fullValue_eq (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (m : M)
    (e : Idempotent A) (he : (e : A) • m = m) :
    fullValue hA hM x m = (x.val (oppositeIdempotent e)).val m :=
  coordinate_apply_independent hA hM x m _ e (hM m).choose_spec he

omit [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] in
include hA hM in
private theorem exists_common_fixer (m n : M) :
    ∃ g : Idempotent A, (g : A) • m = m ∧ (g : A) • n = n := by
  classical
  obtain ⟨e, he⟩ := hM m
  obtain ⟨f, hf⟩ := hM n
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  exact ⟨g, Idempotent.smul_eq_of_le (hg e (by simp)) he,
    Idempotent.smul_eq_of_le (hg f (by simp)) hf⟩

/-- A fixing idempotent also fixes every recovered complex multiple. -/
theorem fixer_complex_smul (c : ℂ) {m : M} {e : Idempotent A} (he : (e : A) • m = m) :
    letI := NondegenerateScalars.complexModule hA hM
    (e : A) • (c • m) = c • m := by
  let _ := NondegenerateScalars.complexModule hA hM
  rw [NondegenerateScalars.action_smul ℂ hA hM, ← NondegenerateScalars.smul_action ℂ hA hM,
    he]

/-- The actual reverse map `(M~)_A → M*`: a linear functional on the recovered complex `M`. -/
def toFullDual (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) : FullDual hA hM := by
  letI := NondegenerateScalars.complexModule hA hM
  exact
    { toFun := fullValue hA hM x
      map_add' := fun m n => by
        obtain ⟨g, hgm, hgn⟩ := exists_common_fixer hA hM m n
        have hgs : (g : A) • (m + n) = m + n := by rw [smul_add, hgm, hgn]
        rw [fullValue_eq hA hM x (m + n) g hgs, fullValue_eq hA hM x m g hgm,
          fullValue_eq hA hM x n g hgn]
        exact (x.val (oppositeIdempotent g)).val.map_add m n
      map_smul' := fun c m => by
        obtain ⟨e, he⟩ := hM m
        rw [fullValue_eq hA hM x (c • m) e (fixer_complex_smul hA hM c he),
          fullValue_eq hA hM x m e he]
        exact (x.val (oppositeIdempotent e)).val.map_smul c m }

/-- The every-fixer formula: the value at `m` uses any idempotent fixing `m`. -/
theorem toFullDual_apply (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (m : M)
    (e : Idempotent A) (he : (e : A) • m = m) :
    toFullDual hA hM x m = (x.val (oppositeIdempotent e)).val m :=
  fullValue_eq hA hM x m e he

theorem toFullDual_zero : toFullDual hA hM 0 = 0 := by
  let _ := NondegenerateScalars.complexModule hA hM
  apply LinearMap.ext
  intro m
  obtain ⟨e, he⟩ := hM m
  rw [toFullDual_apply hA hM 0 m e he]
  rfl

theorem toFullDual_add (x y : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :
    toFullDual hA hM (x + y) = toFullDual hA hM x + toFullDual hA hM y := by
  let _ := NondegenerateScalars.complexModule hA hM
  apply LinearMap.ext
  intro m
  obtain ⟨e, he⟩ := hM m
  rw [toFullDual_apply hA hM (x + y) m e he, LinearMap.add_apply,
    toFullDual_apply hA hM x m e he, toFullDual_apply hA hM y m e he]
  rfl

theorem toFullDual_complex_smul (c : ℂ) (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :
    letI := completionModule hA hM
    toFullDual hA hM (c • x) = c • toFullDual hA hM x := by
  let _ := completionModule hA hM
  let _ := NondegenerateScalars.complexModule hA hM
  apply LinearMap.ext
  intro m
  obtain ⟨e, he⟩ := hM m
  rw [toFullDual_apply hA hM (c • x) m e he, LinearMap.smul_apply,
    toFullDual_apply hA hM x m e he]
  rfl

/-- Right-action equivariance for the published family and full actions. -/
theorem toFullDual_action (a : Aᵐᵒᵖ) (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    toFullDual hA hM (a • x) = a • toFullDual hA hM x := by
  classical
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
  let _ := NondegenerateScalars.complexModule hA hM
  apply LinearMap.ext
  intro m
  obtain ⟨e₀, he₀⟩ := hM m
  obtain ⟨h, hh⟩ := hA {a.unop, (e₀ : A)}
  have hha : (h : A) * a.unop = a.unop :=
    ((Idempotent.sandwich_eq_iff h a.unop).mp (hh a.unop (by simp))).1
  have hm : (h : A) • m = m :=
    Idempotent.smul_eq_of_le ((Idempotent.le_iff_sandwich e₀ h).mpr (hh e₀ (by simp))) he₀
  have ham : (h : A) • (a.unop • m) = a.unop • m := by rw [← mul_smul, hha]
  have hunit : ((oppositeIdempotent h : Aᵐᵒᵖ) * a) * (oppositeIdempotent h : Aᵐᵒᵖ) =
      (oppositeIdempotent h : Aᵐᵒᵖ) * a := by
    apply MulOpposite.unop_injective
    change (h : A) * (a.unop * h) = a.unop * h
    rw [← mul_assoc, hha]
  rw [toFullDual_apply hA hM (a • x) m h hm,
    NonUnitalModuleLeftLimit.smul_val hA.op a x _ _ hunit]
  change (x.val (oppositeIdempotent h)).val ((a.unop * h) • m) =
    toFullDual hA hM x (a.unop • m)
  rw [toFullDual_apply hA hM x (a.unop • m) h ham, mul_smul, hm]

/-- The reverse map as an additive map. -/
def toFullDualAddHom : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →+ FullDual hA hM where
  toFun := toFullDual hA hM
  map_zero' := toFullDual_zero hA hM
  map_add' := toFullDual_add hA hM

@[simp] theorem toFullDualAddHom_apply (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :
    toFullDualAddHom hA hM x = toFullDual hA hM x := rfl

/-- The reverse map as a complex-linear map. -/
def toFullDualLinear :
    letI := completionModule hA hM
    NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →ₗ[ℂ] FullDual hA hM :=
  letI := completionModule hA hM
  { toFun := toFullDual hA hM
    map_add' := toFullDual_add hA hM
    map_smul' := toFullDual_complex_smul hA hM }

theorem toFullDualLinear_coe :
    letI := completionModule hA hM
    ⇑(toFullDualLinear hA hM) = toFullDual hA hM := rfl

/-- The complex-linear package has exactly the specified additive map. -/
theorem toFullDualLinear_toAddMonoidHom :
    letI := completionModule hA hM
    (toFullDualLinear hA hM).toAddMonoidHom = toFullDualAddHom hA hM := rfl

/-- The reverse map as an original intertwiner of right modules. -/
def toFullDualHom :
    @NonUnitalModuleHom Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (FullDual hA hM)
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA.op)
      (NonUnitalModuleDual.fullAction hA hM) := by
  letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
  exact
    { toAddMonoidHom := toFullDualAddHom hA hM
      map_smul' := toFullDual_action hA hM }

/-- The intertwiner package has exactly the specified additive map. -/
theorem toFullDualHom_toAddMonoidHom :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    (toFullDualHom hA hM).toAddMonoidHom = toFullDualAddHom hA hM := rfl

@[simp] theorem toFullDualHom_apply (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
    toFullDualHom hA hM x = toFullDual hA hM x := rfl

end Reverse

/-! Complete unapplied interfaces at independent universes `uA` and `uM`. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Module ℂ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :=
  @completionModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleDual.dualModule hA hM
     letI := completionModule hA hM
     (c • x).val = fun e => c • x.val e) :=
  @completionModule_smul_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) →
    (letI := NonUnitalModuleDual.dualModule hA hM
     letI := completionModule hA hM
     (c • x).val e = c • x.val e) :=
  @completionModule_smul_val.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) →
    (letI := completionModule hA hM
     ((c • x).val e).val = c • (x.val e).val) :=
  @completionModule_smul_functional.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) → (m : M) →
    (letI := completionModule hA hM
     ((c • x).val e).val m = c • (x.val e).val m) :=
  @completionModule_smul_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     letI := completionModule hA hM
     IsScalarTower ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))) :=
  @completion_isScalarTower.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     letI := completionModule hA hM
     SMulCommClass ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))) :=
  @completion_smulCommClass.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent Aᵐᵒᵖ → FullDual hA hM → Dual hA hM :=
  @forwardCoordinate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent Aᵐᵒᵖ) → (φ : FullDual hA hM) →
    (forwardCoordinate hA hM e φ).val = (e : Aᵐᵒᵖ) • φ :=
  @forwardCoordinate_val.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    FullDual hA hM → NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  @toCompletion.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    (toCompletion hA hM φ).val e = forwardCoordinate hA hM e φ :=
  @toCompletion_val.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    ((toCompletion hA hM φ).val e).val = (e : Aᵐᵒᵖ) • φ :=
  @toCompletion_functional.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    ⇑((toCompletion hA hM φ).val e).val = fun m => φ (e.val.unop • m) :=
  @toCompletion_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) → (m : M) →
    ((toCompletion hA hM φ).val e).val m = φ (e.val.unop • m) :=
  @toCompletion_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val e = (toCompletion hA hM φ).val e :=
  @toCompletion_fixed.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → {e f : Idempotent Aᵐᵒᵖ} → e ≤ f →
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val f = (toCompletion hA hM φ).val e :=
  @toCompletion_coherent.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    toCompletion hA hM 0 = 0 :=
  @toCompletion_zero.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ ψ : FullDual hA hM) →
    toCompletion hA hM (φ + ψ) = toCompletion hA hM φ + toCompletion hA hM ψ :=
  @toCompletion_add.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (φ : FullDual hA hM) →
    (letI := completionModule hA hM
     toCompletion hA hM (c • φ) = c • toCompletion hA hM φ) :=
  @toCompletion_complex_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (a : Aᵐᵒᵖ) → (φ : FullDual hA hM) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toCompletion hA hM (a • φ) = a • toCompletion hA hM φ) :=
  @toCompletion_action.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    FullDual hA hM →+ NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  @toCompletionAddHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) →
    toCompletionAddHom hA hM φ = toCompletion hA hM φ :=
  @toCompletionAddHom_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     FullDual hA hM →ₗ[ℂ] NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :=
  @toCompletionLinear.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     ⇑(toCompletionLinear hA hM) = toCompletion hA hM) :=
  @toCompletionLinear_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     (toCompletionLinear hA hM).toAddMonoidHom = toCompletionAddHom hA hM) :=
  @toCompletionLinear_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    @NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA hM) (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))
      _ _ _ (NonUnitalModuleDual.fullAction hA hM)
      (NonUnitalModuleLeftLimit.nonUnitalModule hA.op) :=
  @toCompletionHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     (toCompletionHom hA hM).toAddMonoidHom = toCompletionAddHom hA hM) :=
  @toCompletionHom_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toCompletionHom hA hM φ = toCompletion hA hM φ) :=
  @toCompletionHom_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → {e f : Idempotent A} → e ≤ f → {m : M} →
    (e : A) • m = m →
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m :=
  @coordinate_apply_eq_of_le.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (m : M) → (e f : Idempotent A) →
    (e : A) • m = m → (f : A) • m = m →
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m :=
  @coordinate_apply_independent.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → {m : M} → {e : Idempotent A} → (e : A) • m = m →
    (letI := NondegenerateScalars.complexModule hA hM
     (e : A) • (c • m) = c • m) :=
  @fixer_complex_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) → FullDual hA hM :=
  @toFullDual.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (m : M) → (e : Idempotent A) → (e : A) • m = m →
    toFullDual hA hM x m = (x.val (oppositeIdempotent e)).val m :=
  @toFullDual_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    toFullDual hA hM 0 = 0 :=
  @toFullDual_zero.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x y : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    toFullDual hA hM (x + y) = toFullDual hA hM x + toFullDual hA hM y :=
  @toFullDual_add.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := completionModule hA hM
     toFullDual hA hM (c • x) = c • toFullDual hA hM x) :=
  @toFullDual_complex_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (a : Aᵐᵒᵖ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toFullDual hA hM (a • x) = a • toFullDual hA hM x) :=
  @toFullDual_action.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →+ FullDual hA hM :=
  @toFullDualAddHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    toFullDualAddHom hA hM x = toFullDual hA hM x :=
  @toFullDualAddHom_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →ₗ[ℂ] FullDual hA hM) :=
  @toFullDualLinear.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     ⇑(toFullDualLinear hA hM) = toFullDual hA hM) :=
  @toFullDualLinear_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     (toFullDualLinear hA hM).toAddMonoidHom = toFullDualAddHom hA hM) :=
  @toFullDualLinear_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    @NonUnitalModuleHom Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (FullDual hA hM)
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA.op)
      (NonUnitalModuleDual.fullAction hA hM) :=
  @toFullDualHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     (toFullDualHom hA hM).toAddMonoidHom = toFullDualAddHom hA hM) :=
  @toFullDualHom_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toFullDualHom hA hM x = toFullDual hA hM x) :=
  @toFullDualHom_apply.{uA, uM}

/-! Unequal universe assignment `(uA, uM) = (0, 1)`. -/

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Module ℂ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :=
  @completionModule.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleDual.dualModule hA hM
     letI := completionModule hA hM
     (c • x).val = fun e => c • x.val e) :=
  @completionModule_smul_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) →
    (letI := NonUnitalModuleDual.dualModule hA hM
     letI := completionModule hA hM
     (c • x).val e = c • x.val e) :=
  @completionModule_smul_val.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) →
    (letI := completionModule hA hM
     ((c • x).val e).val = c • (x.val e).val) :=
  @completionModule_smul_functional.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) → (m : M) →
    (letI := completionModule hA hM
     ((c • x).val e).val m = c • (x.val e).val m) :=
  @completionModule_smul_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     letI := completionModule hA hM
     IsScalarTower ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))) :=
  @completion_isScalarTower.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     letI := completionModule hA hM
     SMulCommClass ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))) :=
  @completion_smulCommClass.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent Aᵐᵒᵖ → FullDual hA hM → Dual hA hM :=
  @forwardCoordinate.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent Aᵐᵒᵖ) → (φ : FullDual hA hM) →
    (forwardCoordinate hA hM e φ).val = (e : Aᵐᵒᵖ) • φ :=
  @forwardCoordinate_val.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    FullDual hA hM → NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  @toCompletion.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    (toCompletion hA hM φ).val e = forwardCoordinate hA hM e φ :=
  @toCompletion_val.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    ((toCompletion hA hM φ).val e).val = (e : Aᵐᵒᵖ) • φ :=
  @toCompletion_functional.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    ⇑((toCompletion hA hM φ).val e).val = fun m => φ (e.val.unop • m) :=
  @toCompletion_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) → (m : M) →
    ((toCompletion hA hM φ).val e).val m = φ (e.val.unop • m) :=
  @toCompletion_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val e = (toCompletion hA hM φ).val e :=
  @toCompletion_fixed.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → {e f : Idempotent Aᵐᵒᵖ} → e ≤ f →
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val f = (toCompletion hA hM φ).val e :=
  @toCompletion_coherent.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    toCompletion hA hM 0 = 0 :=
  @toCompletion_zero.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ ψ : FullDual hA hM) →
    toCompletion hA hM (φ + ψ) = toCompletion hA hM φ + toCompletion hA hM ψ :=
  @toCompletion_add.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (φ : FullDual hA hM) →
    (letI := completionModule hA hM
     toCompletion hA hM (c • φ) = c • toCompletion hA hM φ) :=
  @toCompletion_complex_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (a : Aᵐᵒᵖ) → (φ : FullDual hA hM) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toCompletion hA hM (a • φ) = a • toCompletion hA hM φ) :=
  @toCompletion_action.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    FullDual hA hM →+ NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  @toCompletionAddHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) →
    toCompletionAddHom hA hM φ = toCompletion hA hM φ :=
  @toCompletionAddHom_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     FullDual hA hM →ₗ[ℂ] NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :=
  @toCompletionLinear.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     ⇑(toCompletionLinear hA hM) = toCompletion hA hM) :=
  @toCompletionLinear_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     (toCompletionLinear hA hM).toAddMonoidHom = toCompletionAddHom hA hM) :=
  @toCompletionLinear_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    @NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA hM) (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))
      _ _ _ (NonUnitalModuleDual.fullAction hA hM)
      (NonUnitalModuleLeftLimit.nonUnitalModule hA.op) :=
  @toCompletionHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     (toCompletionHom hA hM).toAddMonoidHom = toCompletionAddHom hA hM) :=
  @toCompletionHom_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toCompletionHom hA hM φ = toCompletion hA hM φ) :=
  @toCompletionHom_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → {e f : Idempotent A} → e ≤ f → {m : M} →
    (e : A) • m = m →
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m :=
  @coordinate_apply_eq_of_le.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (m : M) → (e f : Idempotent A) →
    (e : A) • m = m → (f : A) • m = m →
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m :=
  @coordinate_apply_independent.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → {m : M} → {e : Idempotent A} → (e : A) • m = m →
    (letI := NondegenerateScalars.complexModule hA hM
     (e : A) • (c • m) = c • m) :=
  @fixer_complex_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) → FullDual hA hM :=
  @toFullDual.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (m : M) → (e : Idempotent A) → (e : A) • m = m →
    toFullDual hA hM x m = (x.val (oppositeIdempotent e)).val m :=
  @toFullDual_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    toFullDual hA hM 0 = 0 :=
  @toFullDual_zero.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x y : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    toFullDual hA hM (x + y) = toFullDual hA hM x + toFullDual hA hM y :=
  @toFullDual_add.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := completionModule hA hM
     toFullDual hA hM (c • x) = c • toFullDual hA hM x) :=
  @toFullDual_complex_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (a : Aᵐᵒᵖ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toFullDual hA hM (a • x) = a • toFullDual hA hM x) :=
  @toFullDual_action.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →+ FullDual hA hM :=
  @toFullDualAddHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    toFullDualAddHom hA hM x = toFullDual hA hM x :=
  @toFullDualAddHom_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →ₗ[ℂ] FullDual hA hM) :=
  @toFullDualLinear.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     ⇑(toFullDualLinear hA hM) = toFullDual hA hM) :=
  @toFullDualLinear_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     (toFullDualLinear hA hM).toAddMonoidHom = toFullDualAddHom hA hM) :=
  @toFullDualLinear_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    @NonUnitalModuleHom Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (FullDual hA hM)
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA.op)
      (NonUnitalModuleDual.fullAction hA hM) :=
  @toFullDualHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     (toFullDualHom hA hM).toAddMonoidHom = toFullDualAddHom hA hM) :=
  @toFullDualHom_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toFullDualHom hA hM x = toFullDual hA hM x) :=
  @toFullDualHom_apply.{0, 1}

/-! Unequal universe assignment `(uA, uM) = (1, 0)`. -/

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Module ℂ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :=
  @completionModule.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleDual.dualModule hA hM
     letI := completionModule hA hM
     (c • x).val = fun e => c • x.val e) :=
  @completionModule_smul_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) →
    (letI := NonUnitalModuleDual.dualModule hA hM
     letI := completionModule hA hM
     (c • x).val e = c • x.val e) :=
  @completionModule_smul_val.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) →
    (letI := completionModule hA hM
     ((c • x).val e).val = c • (x.val e).val) :=
  @completionModule_smul_functional.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (e : Idempotent Aᵐᵒᵖ) → (m : M) →
    (letI := completionModule hA hM
     ((c • x).val e).val m = c • (x.val e).val m) :=
  @completionModule_smul_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     letI := completionModule hA hM
     IsScalarTower ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))) :=
  @completion_isScalarTower.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     letI := completionModule hA hM
     SMulCommClass ℂ Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))) :=
  @completion_smulCommClass.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent Aᵐᵒᵖ → FullDual hA hM → Dual hA hM :=
  @forwardCoordinate.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent Aᵐᵒᵖ) → (φ : FullDual hA hM) →
    (forwardCoordinate hA hM e φ).val = (e : Aᵐᵒᵖ) • φ :=
  @forwardCoordinate_val.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    FullDual hA hM → NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  @toCompletion.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    (toCompletion hA hM φ).val e = forwardCoordinate hA hM e φ :=
  @toCompletion_val.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    ((toCompletion hA hM φ).val e).val = (e : Aᵐᵒᵖ) • φ :=
  @toCompletion_functional.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    ⇑((toCompletion hA hM φ).val e).val = fun m => φ (e.val.unop • m) :=
  @toCompletion_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) → (m : M) →
    ((toCompletion hA hM φ).val e).val m = φ (e.val.unop • m) :=
  @toCompletion_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → (e : Idempotent Aᵐᵒᵖ) →
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val e = (toCompletion hA hM φ).val e :=
  @toCompletion_fixed.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) → {e f : Idempotent Aᵐᵒᵖ} → e ≤ f →
    (e : Aᵐᵒᵖ) • (toCompletion hA hM φ).val f = (toCompletion hA hM φ).val e :=
  @toCompletion_coherent.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    toCompletion hA hM 0 = 0 :=
  @toCompletion_zero.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ ψ : FullDual hA hM) →
    toCompletion hA hM (φ + ψ) = toCompletion hA hM φ + toCompletion hA hM ψ :=
  @toCompletion_add.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (φ : FullDual hA hM) →
    (letI := completionModule hA hM
     toCompletion hA hM (c • φ) = c • toCompletion hA hM φ) :=
  @toCompletion_complex_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (a : Aᵐᵒᵖ) → (φ : FullDual hA hM) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toCompletion hA hM (a • φ) = a • toCompletion hA hM φ) :=
  @toCompletion_action.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    FullDual hA hM →+ NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) :=
  @toCompletionAddHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) →
    toCompletionAddHom hA hM φ = toCompletion hA hM φ :=
  @toCompletionAddHom_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     FullDual hA hM →ₗ[ℂ] NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :=
  @toCompletionLinear.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     ⇑(toCompletionLinear hA hM) = toCompletion hA hM) :=
  @toCompletionLinear_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     (toCompletionLinear hA hM).toAddMonoidHom = toCompletionAddHom hA hM) :=
  @toCompletionLinear_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    @NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA hM) (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM))
      _ _ _ (NonUnitalModuleDual.fullAction hA hM)
      (NonUnitalModuleLeftLimit.nonUnitalModule hA.op) :=
  @toCompletionHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     (toCompletionHom hA hM).toAddMonoidHom = toCompletionAddHom hA hM) :=
  @toCompletionHom_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (φ : FullDual hA hM) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toCompletionHom hA hM φ = toCompletion hA hM φ) :=
  @toCompletionHom_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → {e f : Idempotent A} → e ≤ f → {m : M} →
    (e : A) • m = m →
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m :=
  @coordinate_apply_eq_of_le.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (m : M) → (e f : Idempotent A) →
    (e : A) • m = m → (f : A) • m = m →
    (x.val (oppositeIdempotent e)).val m = (x.val (oppositeIdempotent f)).val m :=
  @coordinate_apply_independent.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → {m : M} → {e : Idempotent A} → (e : A) • m = m →
    (letI := NondegenerateScalars.complexModule hA hM
     (e : A) • (c • m) = c • m) :=
  @fixer_complex_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) → FullDual hA hM :=
  @toFullDual.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) → (m : M) → (e : Idempotent A) → (e : A) • m = m →
    toFullDual hA hM x m = (x.val (oppositeIdempotent e)).val m :=
  @toFullDual_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    toFullDual hA hM 0 = 0 :=
  @toFullDual_zero.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x y : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    toFullDual hA hM (x + y) = toFullDual hA hM x + toFullDual hA hM y :=
  @toFullDual_add.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (c : ℂ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := completionModule hA hM
     toFullDual hA hM (c • x) = c • toFullDual hA hM x) :=
  @toFullDual_complex_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (a : Aᵐᵒᵖ) → (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toFullDual hA hM (a • x) = a • toFullDual hA hM x) :=
  @toFullDual_action.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →+ FullDual hA hM :=
  @toFullDualAddHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    toFullDualAddHom hA hM x = toFullDual hA hM x :=
  @toFullDualAddHom_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM) →ₗ[ℂ] FullDual hA hM) :=
  @toFullDualLinear.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     ⇑(toFullDualLinear hA hM) = toFullDual hA hM) :=
  @toFullDualLinear_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := completionModule hA hM
     (toFullDualLinear hA hM).toAddMonoidHom = toFullDualAddHom hA hM) :=
  @toFullDualLinear_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    @NonUnitalModuleHom Aᵐᵒᵖ (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) (FullDual hA hM)
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA.op)
      (NonUnitalModuleDual.fullAction hA hM) :=
  @toFullDualHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     (toFullDualHom hA hM).toAddMonoidHom = toFullDualAddHom hA hM) :=
  @toFullDualHom_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] → [IsScalarTower ℂ A A] →
    [SMulCommClass ℂ A A] → {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) →
    (letI := NonUnitalModuleLeftLimit.nonUnitalModule (M := Dual hA hM) hA.op
     toFullDualHom hA hM x = toFullDual hA hM x) :=
  @toFullDualHom_apply.{1, 0}

/-! Zero cases: the zero carrier over every idempotented ring, and the zero ring. -/

section ZeroCases

/-- The zero carrier is nondegenerate for every action, with the zero idempotent as fixer. -/
private theorem punit_isNondegenerate (A : Type uA) [NonUnitalRing A]
    [NonUnitalModule A PUnit.{uM + 1}] : IsNondegenerate A PUnit.{uM + 1} :=
  fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)

local instance : NonUnitalModule A PUnit.{uM + 1} := NonUnitalModule.zero

example :
    @NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA (punit_isNondegenerate.{uA, uM} A))
      (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA (punit_isNondegenerate.{uA, uM} A)))
      _ _ _ (NonUnitalModuleDual.fullAction hA (punit_isNondegenerate A))
      (NonUnitalModuleLeftLimit.nonUnitalModule hA.op) :=
  toCompletionHom hA (punit_isNondegenerate A)

example :
    @NonUnitalModuleHom Aᵐᵒᵖ
      (NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA (punit_isNondegenerate.{uA, uM} A)))
      (FullDual hA (punit_isNondegenerate.{uA, uM} A))
      _ _ _ (NonUnitalModuleLeftLimit.nonUnitalModule hA.op)
      (NonUnitalModuleDual.fullAction hA (punit_isNondegenerate A)) :=
  toFullDualHom hA (punit_isNondegenerate A)

/-- On the zero carrier the reverse map is zero. -/
example (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA (punit_isNondegenerate.{uA, uM} A))) :
    toFullDual hA (punit_isNondegenerate A) x = 0 := by
  let _ := NondegenerateScalars.complexModule hA (punit_isNondegenerate.{uA, uM} A)
  apply LinearMap.ext
  intro m
  rw [toFullDual_apply hA _ x m ⟨0, IsIdempotentElem.zero⟩ (Subsingleton.elim _ _),
    Subsingleton.elim m 0, map_zero, map_zero]

/-- The zero ring with the zero carrier. -/
example :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule
      (M := Dual (IsIdempotented.of_ring PUnit.{uA + 1})
        (punit_isNondegenerate.{uA, uM} PUnit.{uA + 1}))
      (IsIdempotented.of_ring PUnit.{uA + 1}).op
    (toFullDualHom (IsIdempotented.of_ring PUnit.{uA + 1})
        (punit_isNondegenerate.{uA, uM} PUnit.{uA + 1})).toAddMonoidHom =
      toFullDualAddHom (IsIdempotented.of_ring PUnit.{uA + 1})
        (punit_isNondegenerate PUnit.{uA + 1}) := rfl

example :
    letI := NonUnitalModuleLeftLimit.nonUnitalModule
      (M := Dual (IsIdempotented.of_ring PUnit.{uA + 1})
        (punit_isNondegenerate.{uA, uM} PUnit.{uA + 1}))
      (IsIdempotented.of_ring PUnit.{uA + 1}).op
    (toCompletionHom (IsIdempotented.of_ring PUnit.{uA + 1})
        (punit_isNondegenerate.{uA, uM} PUnit.{uA + 1})).toAddMonoidHom =
      toCompletionAddHom (IsIdempotented.of_ring PUnit.{uA + 1})
        (punit_isNondegenerate PUnit.{uA + 1}) := rfl

end ZeroCases

end Langlands.Algebra.NonUnitalModuleDualCompletion
