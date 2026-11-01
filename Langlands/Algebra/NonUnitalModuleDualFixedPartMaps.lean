import Langlands.Algebra.NonUnitalModuleCornerScalars
import Langlands.Algebra.NonUnitalModuleDual

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualFixedPartMaps

open MulOpposite
open NonUnitalModuleCorner (FixedPart)

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- The actual opposite idempotent has underlying value `op e`. -/
def oppositeIdempotent (e : Idempotent A) : Idempotent Aᵐᵒᵖ :=
  ⟨op (e : A), by
    change op ((e : A) * e) = op (e : A)
    exact congrArg op e.property.eq⟩

@[simp] theorem oppositeIdempotent_val (e : Idempotent A) :
    (oppositeIdempotent e : Aᵐᵒᵖ) = op (e : A) := rfl

theorem oppositeIdempotent_mul_self (e : Idempotent A) :
    (oppositeIdempotent e : Aᵐᵒᵖ) * oppositeIdempotent e =
      (oppositeIdempotent e : Aᵐᵒᵖ) := (oppositeIdempotent e).property.eq

section Maps

variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hM) :=
  NonUnitalModuleDual.fullAction hA hM

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hM) :=
  NonUnitalModuleDual.dualAction hA hM

/-- Exactly the published fixed-part subtype of the actual nondegenerate dual. -/
abbrev RightFixedPart (e : Idempotent A) :=
  FixedPart (oppositeIdempotent e) (NonUnitalModuleDual.Dual hA hM)

theorem rightFixedPart_eq_subtype (e : Idempotent A) :
    RightFixedPart hA hM e =
      {φ : NonUnitalModuleDual.Dual hA hM // op (e : A) • φ = φ} := rfl

theorem rightFixedPart_eq_nestedSubtype (e : Idempotent A) :
    RightFixedPart hA hM e =
      {φ : {ψ : NonUnitalModuleDual.FullDual hA hM //
        ψ ∈ nondegeneratePart hA.op (NonUnitalModuleDual.FullDual hA hM)} //
        op (e : A) • φ = φ} := rfl

/-- The right fixed part inherits the published dual's precise complex scalars. -/
@[instance_reducible]
def rightFixedModule (e : Idempotent A) : Module ℂ (RightFixedPart hA hM e) := by
  letI := NonUnitalModuleDual.dualModule hA hM
  letI := NonUnitalModuleDual.dual_smulCommClass hA hM
  exact NonUnitalModuleCorner.inheritedComplexModule
    (oppositeIdempotent e) (NonUnitalModuleDual.Dual hA hM)

/-- Recovering scalars from the unchanged right action gives this same module. -/
theorem rightFixedModule_eq_canonical (e : Idempotent A) :
    rightFixedModule hA hM e =
      NonUnitalModuleCorner.complexModule hA.op
        (NonUnitalModuleDual.isNondegenerate hA hM) (oppositeIdempotent e) := by
  apply Module.ext' _ _
  intro c φ
  exact Subtype.ext (congrArg
    (fun S : Module ℂ (NonUnitalModuleDual.Dual hA hM) => S.toSMul.smul c φ.val)
    (NonUnitalModuleDual.canonicalModule_eq_dualModule hA hM)).symm

theorem rightFixedModule_smul (e : Idempotent A) (c : ℂ)
    (φ : RightFixedPart hA hM e) :
    letI := NonUnitalModuleDual.dualModule hA hM
    letI := NonUnitalModuleDual.dual_smulCommClass hA hM
    letI := rightFixedModule hA hM e
    c • φ = ⟨c • φ.val,
      NonUnitalModuleCorner.smul_mem_fixedPart (oppositeIdempotent e) c φ⟩ := rfl

theorem rightFixedModule_smul_val (e : Idempotent A) (c : ℂ)
    (φ : RightFixedPart hA hM e) :
    letI := NonUnitalModuleDual.dualModule hA hM
    letI := rightFixedModule hA hM e
    (c • φ).val = c • φ.val := rfl

/-- The entire included full-dual functional uses pointwise complex scalars. -/
theorem rightFixedModule_smul_functional (e : Idempotent A) (c : ℂ)
    (φ : RightFixedPart hA hM e) :
    letI := rightFixedModule hA hM e
    (c • φ).val.val = c • φ.val.val := rfl

@[simp] theorem rightFixedModule_smul_apply (e : Idempotent A) (c : ℂ)
    (φ : RightFixedPart hA hM e) (m : M) :
    letI := rightFixedModule hA hM e
    (c • φ).val.val m = c • φ.val.val m := rfl

/-- The two subtype layers retain the original full functional and its fixation. -/
theorem rightFixedPart_fixed_functional (e : Idempotent A)
    (φ : RightFixedPart hA hM e) :
    op (e : A) • φ.val.val = φ.val.val :=
  congrArg Subtype.val φ.property

@[simp] theorem rightFixedPart_fixed_apply (e : Idempotent A)
    (φ : RightFixedPart hA hM e) (m : M) :
    φ.val.val ((e : A) • m) = φ.val.val m :=
  congrArg (fun ψ : NonUnitalModuleDual.FullDual hA hM => ψ m)
    (rightFixedPart_fixed_functional hA hM e φ)

/-- A fixed full functional belongs to both actual subtypes, using this idempotent. -/
def ofFixedFull (e : Idempotent A) (ψ : NonUnitalModuleDual.FullDual hA hM)
    (hψ : op (e : A) • ψ = ψ) : RightFixedPart hA hM e :=
  ⟨⟨ψ, ⟨oppositeIdempotent e, hψ⟩⟩, Subtype.ext hψ⟩

/-- The full nested-subtype constructor, with the actual membership witnesses. -/
theorem ofFixedFull_eq (e : Idempotent A) (ψ : NonUnitalModuleDual.FullDual hA hM)
    (hψ : op (e : A) • ψ = ψ) :
    ofFixedFull hA hM e ψ hψ =
      ⟨⟨ψ, ⟨oppositeIdempotent e, hψ⟩⟩, Subtype.ext hψ⟩ := rfl

@[simp] theorem ofFixedFull_functional (e : Idempotent A)
    (ψ : NonUnitalModuleDual.FullDual hA hM) (hψ : op (e : A) • ψ = ψ) :
    (ofFixedFull hA hM e ψ hψ).val.val = ψ := rfl

/-- Restrict the actual included functional along the actual complex-linear inclusion. -/
def restriction (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := rightFixedModule hA hM e
    RightFixedPart hA hM e →ₗ[ℂ] Module.Dual ℂ (FixedPart e M) := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := rightFixedModule hA hM e
  exact
    { toFun := fun φ => φ.val.val.comp (NonUnitalModuleCorner.inclusionLinear hA hM e)
      map_add' _ _ := by ext x; rfl
      map_smul' _ _ := by ext x; rfl }

theorem restriction_functional (e : Idempotent A) (φ : RightFixedPart hA hM e) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NonUnitalModuleCorner.complexModule hA hM e
    restriction hA hM e φ =
      φ.val.val.comp (NonUnitalModuleCorner.inclusionLinear hA hM e) := rfl

theorem restriction_coe (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ⇑(restriction hA hM e) =
      fun φ => φ.val.val.comp (NonUnitalModuleCorner.inclusionLinear hA hM e) := rfl

theorem restriction_function_coe (e : Idempotent A) (φ : RightFixedPart hA hM e) :
    ⇑(restriction hA hM e φ) = fun x => φ.val.val x.val := rfl

@[simp] theorem restriction_apply (e : Idempotent A) (φ : RightFixedPart hA hM e)
    (x : FixedPart e M) :
    restriction hA hM e φ x = φ.val.val x.val := rfl

/-- The full extension is exactly precomposition with the idempotent projection. -/
def extensionFunctional (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[ℂ] NonUnitalModuleDual.FullDual hA hM := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NonUnitalModuleCorner.complexModule hA hM e
  exact
    { toFun := fun ell => ell.comp (NonUnitalModuleCorner.projectionLinear hA hM e)
      map_add' _ _ := by ext m; rfl
      map_smul' _ _ := by ext m; rfl }

theorem extensionFunctional_eq_comp (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      extensionFunctional hA hM e ell =
        ell.comp (NonUnitalModuleCorner.projectionLinear hA hM e) := fun _ => rfl

@[simp] theorem extensionFunctional_apply (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ (ell : Module.Dual ℂ (FixedPart e M)) (m : M),
      extensionFunctional hA hM e ell m = ell (NonUnitalModuleCorner.projection e m) :=
  fun _ _ => rfl

/-- Idempotence of the actual coordinate fixes the entire extended functional. -/
theorem extensionFunctional_fixed (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      op (e : A) • extensionFunctional hA hM e ell =
        extensionFunctional hA hM e ell := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  intro ell
  apply LinearMap.ext
  intro m
  change ell (NonUnitalModuleCorner.projection e ((e : A) • m)) =
    ell (NonUnitalModuleCorner.projection e m)
  apply congrArg ell
  exact Subtype.ext (NonUnitalModuleCorner.coordinate_idempotent e m)

/-- The same opposite idempotent witnesses membership in the actual nondegenerate part. -/
theorem extensionFunctional_mem_dual (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      extensionFunctional hA hM e ell ∈
        nondegeneratePart hA.op (NonUnitalModuleDual.FullDual hA hM) := by
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  intro ell
  exact ⟨oppositeIdempotent e, extensionFunctional_fixed hA hM e ell⟩

/-- Canonical extension into the actual right fixed part of the actual dual. -/
def extension (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := rightFixedModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[ℂ] RightFixedPart hA hM e := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := rightFixedModule hA hM e
  exact
    { toFun := fun ell => ofFixedFull hA hM e (extensionFunctional hA hM e ell)
        (extensionFunctional_fixed hA hM e ell)
      map_add' _ _ := Subtype.ext (Subtype.ext (by ext m; rfl))
      map_smul' _ _ := Subtype.ext (Subtype.ext (by ext m; rfl)) }

theorem extension_eq_nestedSubtype (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      extension hA hM e ell =
        ⟨⟨extensionFunctional hA hM e ell, extensionFunctional_mem_dual hA hM e ell⟩,
          Subtype.ext (extensionFunctional_fixed hA hM e ell)⟩ := fun _ => rfl

/-- Equality of the entire included full-dual functional. -/
theorem extension_functional (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      (extension hA hM e ell).val.val =
        ell.comp (NonUnitalModuleCorner.projectionLinear hA hM e) := fun _ => rfl

theorem extension_coe (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ⇑(extension hA hM e) =
      fun ell => ofFixedFull hA hM e (extensionFunctional hA hM e ell)
        (extensionFunctional_fixed hA hM e ell) := rfl

theorem extension_function_coe (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      ⇑(extension hA hM e ell).val.val =
        fun m => ell (NonUnitalModuleCorner.projection e m) := fun _ => rfl

@[simp] theorem extension_apply (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ (ell : Module.Dual ℂ (FixedPart e M)) (m : M),
      (extension hA hM e ell).val.val m = ell (NonUnitalModuleCorner.projection e m) :=
  fun _ _ => rfl

end Maps

/-! Complete unapplied interfaces retain independent algebra and carrier universes. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Type uM := @RightFixedPart.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) → Module ℂ (RightFixedPart hA hM e) :=
  @rightFixedModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := rightFixedModule hA hM e
    RightFixedPart hA hM e →ₗ[ℂ] Module.Dual ℂ (FixedPart e M) :=
  @restriction.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := rightFixedModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[ℂ] RightFixedPart hA hM e :=
  @extension.{uA, uM}

end Langlands.Algebra.NonUnitalModuleDualFixedPartMaps
