import Langlands.Algebra.NondegenerateScalars
import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.LinearAlgebra.Dual.Defs

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDual

open MulOpposite

universe uA uM uN uP

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

/-- The actual full complex dual, using precisely the recovered scalar module. -/
abbrev FullDual (hA : IsIdempotented A) (hM : IsNondegenerate A M) :=
  letI := NondegenerateScalars.complexModule hA hM
  Module.Dual ℂ M

/-- Precomposition with the original action; multiplication reverses. -/
@[instance_reducible]
def fullAction (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    NonUnitalModule Aᵐᵒᵖ (FullDual hA hM) := by
  letI := NondegenerateScalars.complexModule hA hM
  exact
    { smul a φ := φ.comp (NondegenerateScalars.toLinearEndHom ℂ hA hM a.unop)
      smul_zero a := by ext m; rfl
      smul_add a φ ψ := by ext m; rfl
      mul_smul a b φ := by
        ext m
        change φ ((a * b).unop • m) = φ (b.unop • (a.unop • m))
        rw [unop_mul, mul_smul]
      add_smul a b φ := by
        ext m
        change φ ((a + b).unop • m) = φ (a.unop • m) + φ (b.unop • m)
        rw [unop_add, NonUnitalModule.add_smul, φ.map_add]
      zero_smul φ := by
        ext m
        change φ ((0 : Aᵐᵒᵖ).unop • m) = 0
        rw [unop_zero, NonUnitalModule.zero_smul, φ.map_zero] }

section Object

variable (hA : IsIdempotented A) (hM : IsNondegenerate A M)

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hM) := fullAction hA hM

@[simp] theorem fullAction_apply (a : A) (φ : FullDual hA hM) (m : M) :
    (op a • φ) m = φ (a • m) := rfl

/-- Equality of the entire underlying function. -/
theorem fullAction_coe (a : Aᵐᵒᵖ) (φ : FullDual hA hM) :
    ⇑(a • φ) = fun m => φ (a.unop • m) := rfl

/-- The action is exactly composition with the published linear original action. -/
theorem fullAction_eq_comp (a : Aᵐᵒᵖ) (φ : FullDual hA hM) :
    letI := NondegenerateScalars.complexModule hA hM
    a • φ = φ.comp (NondegenerateScalars.toLinearEndHom ℂ hA hM a.unop) := rfl

/-- Compatibility with the usual pointwise complex scalars on the full dual. -/
theorem full_isScalarTower : IsScalarTower ℂ Aᵐᵒᵖ (FullDual hA hM) := by
  let _ := NondegenerateScalars.complexModule hA hM
  refine ⟨fun c a φ => ?_⟩
  apply LinearMap.ext
  intro m
  change φ ((c • a.unop) • m) = c • φ (a.unop • m)
  rw [← NondegenerateScalars.smul_action ℂ hA hM, φ.map_smul]

theorem full_smulCommClass : SMulCommClass ℂ Aᵐᵒᵖ (FullDual hA hM) := by
  let _ := NondegenerateScalars.complexModule hA hM
  refine ⟨fun c a φ => ?_⟩
  apply LinearMap.ext
  intro m
  rfl

/-- The actual nondegenerate part of the full dual, with its inherited action. -/
abbrev Dual := nondegeneratePart hA.op (FullDual hA hM)

/-- The inherited original right action, named without installing a global instance. -/
@[instance_reducible]
def dualAction : NonUnitalModule Aᵐᵒᵖ (Dual hA hM) := inferInstance

/-- The actual inclusion keeps the same linear functionals. -/
def inclusion : NonUnitalModuleHom Aᵐᵒᵖ (Dual hA hM) (FullDual hA hM) :=
  (nondegeneratePart hA.op (FullDual hA hM)).subtype

theorem inclusion_coe :
    ⇑(inclusion hA hM) = fun φ => φ.val := rfl

@[simp] theorem inclusion_apply (φ : Dual hA hM) : inclusion hA hM φ = φ.val := rfl

@[simp] theorem dualAction_apply (a : A) (φ : Dual hA hM) (m : M) :
    (op a • φ).val m = φ.val (a • m) := rfl

/-- Nondegeneracy is intrinsic to this subtype and the inherited action. -/
theorem isNondegenerate : IsNondegenerate Aᵐᵒᵖ (Dual hA hM) :=
  nondegeneratePart_isNondegenerate hA.op

/-- Membership can use the original algebra's idempotents, not opposite notation. -/
theorem mem_dual_iff (φ : FullDual hA hM) :
    φ ∈ nondegeneratePart hA.op (FullDual hA hM) ↔
      ∃ e : Idempotent A, ∀ m : M, φ ((e : A) • m) = φ m := by
  let _ := NondegenerateScalars.complexModule hA hM
  constructor
  · rintro ⟨e, he⟩
    refine ⟨⟨e.val.unop, ?_⟩, ?_⟩
    · change e.val.unop * e.val.unop = e.val.unop
      have hh := congrArg unop e.property.eq
      simpa only [unop_mul] using hh
    · intro m
      exact congrArg (fun ψ : FullDual hA hM => ψ m) he
  · rintro ⟨e, he⟩
    refine ⟨⟨op e.val, ?_⟩, ?_⟩
    · change op (e.val * e.val) = op e.val
      exact congrArg op e.property.eq
    · exact LinearMap.ext he


/-- The inherited pointwise complex module on the actual nondegenerate subtype. -/
@[instance_reducible]
def dualModule : Module ℂ (Dual hA hM) := by
  letI := full_smulCommClass hA hM
  exact
    { smul c φ := ⟨c • φ.val, by
        obtain ⟨e, he⟩ := φ.property
        exact ⟨e, (smul_comm c (e : Aᵐᵒᵖ) φ.val).symm.trans (congrArg (c • ·) he)⟩⟩
      one_smul φ := Subtype.ext (one_smul ℂ φ.val)
      mul_smul c d φ := Subtype.ext (mul_smul c d φ.val)
      smul_zero c := Subtype.ext (smul_zero c)
      smul_add c φ ψ := Subtype.ext (smul_add c φ.val ψ.val)
      add_smul c d φ := Subtype.ext (add_smul c d φ.val)
      zero_smul φ := Subtype.ext (zero_smul ℂ φ.val) }

/-- Subtype scalars retain the entire full-dual functional. -/
theorem dualModule_smul_val (c : ℂ) (φ : Dual hA hM) :
    letI := dualModule hA hM
    (c • φ).val = c • φ.val := rfl

@[simp] theorem dualModule_smul_apply (c : ℂ) (φ : Dual hA hM) (m : M) :
    letI := dualModule hA hM
    (c • φ).val m = c • φ.val m := rfl

/-- Scalar compatibility on the subtype follows from that on the full dual. -/
theorem dual_isScalarTower :
    letI := dualModule hA hM
    IsScalarTower ℂ Aᵐᵒᵖ (Dual hA hM) := by
  let _ := dualModule hA hM
  let _ := full_isScalarTower hA hM
  exact ⟨fun c a φ => Subtype.ext (smul_assoc c a φ.val)⟩

theorem dual_smulCommClass :
    letI := dualModule hA hM
    SMulCommClass ℂ Aᵐᵒᵖ (Dual hA hM) := by
  let _ := dualModule hA hM
  let _ := full_smulCommClass hA hM
  exact ⟨fun c a φ => Subtype.ext (smul_comm c a φ.val)⟩

/-- The scalar module recovered from this same right action is exactly the inherited one. -/
theorem canonicalModule_eq_dualModule :
    NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM) = dualModule hA hM := by
  let _ := dualModule hA hM
  let _ := dual_isScalarTower hA hM
  exact NondegenerateScalars.module_eq_of_compatible ℂ hA.op (isNondegenerate hA hM)

/-- Canonically recovered scalars retain the same entire pointwise functional. -/
theorem canonical_smul_val (c : ℂ) (φ : Dual hA hM) :
    letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
    (c • φ).val = c • φ.val := by
  rw [canonicalModule_eq_dualModule]
  rfl

@[simp] theorem canonical_smul_apply (c : ℂ) (φ : Dual hA hM) (m : M) :
    letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
    (c • φ).val m = c • φ.val m :=
  congrArg (fun ψ : FullDual hA hM => ψ m) (canonical_smul_val hA hM c φ)

/-- Inclusion is complex linear for the explicitly inherited scalar module. -/
def inclusionLinear :
    letI := dualModule hA hM
    Dual hA hM →ₗ[ℂ] FullDual hA hM :=
  letI := dualModule hA hM
  { toFun := fun φ => φ.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

theorem inclusionLinear_coe :
    letI := dualModule hA hM
    ⇑(inclusionLinear hA hM) = fun φ => φ.val := rfl

end Object

end Langlands.Algebra.NonUnitalModuleDual
