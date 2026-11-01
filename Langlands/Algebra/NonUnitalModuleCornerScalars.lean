import Langlands.Algebra.NonUnitalModuleCorner
import Langlands.Algebra.NondegenerateScalars

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCorner

universe uA uM uN uP

section Inherited

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  [Module ℂ M] [SMulCommClass ℂ A M]

/-- Compatible ambient complex scalars preserve the actual fixed subgroup. -/
theorem smul_mem_fixedPart (e : Idempotent A) (c : ℂ) (x : FixedPart e M) :
    c • x.val ∈ fixedPart e M := by
  change (e : A) • (c • x.val) = c • x.val
  rw [← smul_comm c (e : A), show (e : A) • x.val = x.val from x.property]

/-- Inherit the given complex scalars, keeping the published subgroup and its group. -/
@[instance_reducible]
def inheritedComplexModule (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] [Module ℂ M] [SMulCommClass ℂ A M] :
    Module ℂ (FixedPart e M) where
  smul c x := ⟨c • x.val, smul_mem_fixedPart e c x⟩
  one_smul x := Subtype.ext (one_smul ℂ x.val)
  mul_smul c d x := Subtype.ext (mul_smul c d x.val)
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c x y := Subtype.ext (smul_add c x.val y.val)
  add_smul c d x := Subtype.ext (add_smul c d x.val)
  zero_smul x := Subtype.ext (zero_smul ℂ x.val)

theorem inheritedComplexModule_smul (e : Idempotent A) (c : ℂ) (x : FixedPart e M) :
    letI := inheritedComplexModule e M
    c • x = ⟨c • x.val, smul_mem_fixedPart e c x⟩ := rfl

theorem inheritedComplexModule_smul_val (e : Idempotent A) (c : ℂ)
    (x : FixedPart e M) :
    letI := inheritedComplexModule e M
    (c • x).val = c • x.val := rfl

/-- The inherited scalars commute with exactly the published corner action. -/
theorem inherited_smulCommClass (e : Idempotent A) :
    letI := inheritedComplexModule e M
    letI := fixedPartModule e M
    SMulCommClass ℂ (Idempotent.Corner e) (FixedPart e M) := by
  let _ := inheritedComplexModule e M
  exact ⟨fun c a x => Subtype.ext (smul_comm c a.val x.val)⟩

end Inherited

section Canonical

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The fixed part inherits precisely the canonical ambient complex module. -/
@[instance_reducible]
def complexModule (e : Idempotent A) : Module ℂ (FixedPart e M) := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NondegenerateScalars.smulCommClass ℂ hA hM
  exact inheritedComplexModule e M

theorem complex_smul_mem (e : Idempotent A) (c : ℂ) (x : FixedPart e M) :
    letI := NondegenerateScalars.complexModule hA hM
    c • x.val ∈ fixedPart e M := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.smulCommClass ℂ hA hM
  exact smul_mem_fixedPart e c x

theorem complex_smul (e : Idempotent A) (c : ℂ) (x : FixedPart e M) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := complexModule hA hM e
    c • x = ⟨c • x.val, complex_smul_mem hA hM e c x⟩ := rfl

theorem complex_smul_val (e : Idempotent A) (c : ℂ) (x : FixedPart e M) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := complexModule hA hM e
    (c • x).val = c • x.val := rfl

theorem complex_smulCommClass (e : Idempotent A) :
    letI := complexModule hA hM e
    letI := fixedPartModule e M
    SMulCommClass ℂ (Idempotent.Corner e) (FixedPart e M) := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.smulCommClass ℂ hA hM
  exact inherited_smulCommClass e

/-- Every actual corner element acts complex linearly for the inherited scalars. -/
def cornerLinearAction (e : Idempotent A) (a : Idempotent.Corner e) :
    letI := complexModule hA hM e
    Module.End ℂ (FixedPart e M) := by
  letI := complexModule hA hM e
  letI := complex_smulCommClass hA hM e
  exact
    { toFun := fun x => a • x
      map_add' := smul_add a
      map_smul' c x := (smul_comm c a x).symm }

theorem cornerLinearAction_apply (e : Idempotent A) (a : Idempotent.Corner e)
    (x : FixedPart e M) :
    letI := complexModule hA hM e
    cornerLinearAction hA hM e a x = a • x := rfl

/-- The actual additive inclusion with its intrinsic complex linearity. -/
def inclusionLinear (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := complexModule hA hM e
    FixedPart e M →ₗ[ℂ] M :=
  letI := NondegenerateScalars.complexModule hA hM
  letI := complexModule hA hM e
  { toFun := inclusion e
    map_add' := (inclusion e).map_add
    map_smul' _ _ := rfl }

theorem inclusionLinear_toAddMonoidHom (e : Idempotent A) :
    (inclusionLinear hA hM e).toAddMonoidHom = inclusion e := rfl

theorem inclusionLinear_coe (e : Idempotent A) :
    ⇑(inclusionLinear hA hM e) = fun x => x.val := rfl

@[simp] theorem inclusionLinear_apply (e : Idempotent A) (x : FixedPart e M) :
    inclusionLinear hA hM e x = x.val := rfl

/-- The actual additive idempotent projection with its intrinsic complex linearity. -/
def projectionLinear (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := complexModule hA hM e
    M →ₗ[ℂ] FixedPart e M := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NondegenerateScalars.smulCommClass ℂ hA hM
  letI := complexModule hA hM e
  exact
    { toFun := projection e
      map_add' := (projection e).map_add
      map_smul' c m := Subtype.ext ((smul_comm c (e : A) m).symm) }

theorem projectionLinear_toAddMonoidHom (e : Idempotent A) :
    (projectionLinear hA hM e).toAddMonoidHom = projection e := rfl

theorem projectionLinear_coe (e : Idempotent A) :
    ⇑(projectionLinear hA hM e) = ⇑(projection (M := M) e) := rfl

@[simp] theorem projectionLinear_apply (e : Idempotent A) (m : M) :
    projectionLinear hA hM e m = projection e m := rfl

@[simp] theorem projectionLinear_val (e : Idempotent A) (m : M) :
    (projectionLinear hA hM e m).val = (e : A) • m := rfl

theorem projectionLinear_inclusionLinear (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := complexModule hA hM e
    (projectionLinear hA hM e).comp (inclusionLinear hA hM e) = LinearMap.id := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := complexModule hA hM e
  apply LinearMap.toAddMonoidHom_injective
  exact projection_inclusion e

theorem inclusionLinear_projectionLinear (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := complexModule hA hM e
    (inclusionLinear hA hM e).comp (projectionLinear hA hM e) =
      NondegenerateScalars.toLinearEndHom ℂ hA hM (e : A) := by
  let _ := NondegenerateScalars.complexModule hA hM
  apply LinearMap.toAddMonoidHom_injective
  exact inclusion_projection e

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  (hN : IsNondegenerate A N)

/-- The published corner restriction, with automatic canonical complex linearity. -/
def restrictLinear (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    letI := complexModule hA hM e
    letI := complexModule hA hN e
    FixedPart e M →ₗ[ℂ] FixedPart e N := by
  letI := NondegenerateScalars.complexModule hA hM
  letI := NondegenerateScalars.complexModule hA hN
  letI := complexModule hA hM e
  letI := complexModule hA hN e
  exact
    { toFun := restrict e f
      map_add' := (restrict e f).map_add
      map_smul' c x := Subtype.ext
        ((NondegenerateScalars.complexToLinearMap hA hM hN f).map_smul c x.val) }

theorem restrictLinear_toAddMonoidHom (e : Idempotent A)
    (f : NonUnitalModuleHom A M N) :
    (restrictLinear hA hM hN e f).toAddMonoidHom = (restrict e f).toAddMonoidHom := rfl

theorem restrictLinear_coe (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    ⇑(restrictLinear hA hM hN e f) =
      fun x => ⟨f x.val, map_mem_fixedPart e f x.property⟩ := rfl

@[simp] theorem restrictLinear_apply (e : Idempotent A)
    (f : NonUnitalModuleHom A M N) (x : FixedPart e M) :
    restrictLinear hA hM hN e f x = restrict e f x := rfl

@[simp] theorem restrictLinear_val (e : Idempotent A)
    (f : NonUnitalModuleHom A M N) (x : FixedPart e M) :
    (restrictLinear hA hM hN e f x).val = f x.val := rfl

theorem inclusionLinear_naturality (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    letI := complexModule hA hM e
    letI := complexModule hA hN e
    (inclusionLinear hA hN e).comp (restrictLinear hA hM hN e f) =
      (NondegenerateScalars.complexToLinearMap hA hM hN f).comp
        (inclusionLinear hA hM e) := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.complexModule hA hN
  let _ := complexModule hA hM e
  apply LinearMap.toAddMonoidHom_injective
  exact inclusion_naturality e f

theorem projectionLinear_naturality (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    letI := complexModule hA hM e
    letI := complexModule hA hN e
    (restrictLinear hA hM hN e f).comp (projectionLinear hA hM e) =
      (projectionLinear hA hN e).comp
        (NondegenerateScalars.complexToLinearMap hA hM hN f) := by
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.complexModule hA hN
  let _ := complexModule hA hN e
  apply LinearMap.toAddMonoidHom_injective
  exact projection_naturality e f

omit hN in
theorem restrictLinear_id (e : Idempotent A) :
    letI := complexModule hA hM e
    restrictLinear hA hM hM e (NonUnitalModuleHom.id A M) = LinearMap.id := by
  let _ := complexModule hA hM e
  apply LinearMap.toAddMonoidHom_injective
  ext x
  rfl

variable {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]
  (hP : IsNondegenerate A P)

theorem restrictLinear_comp (e : Idempotent A) (g : NonUnitalModuleHom A N P)
    (f : NonUnitalModuleHom A M N) :
    letI := complexModule hA hM e
    letI := complexModule hA hN e
    letI := complexModule hA hP e
    restrictLinear hA hM hP e (g.comp f) =
      (restrictLinear hA hN hP e g).comp (restrictLinear hA hM hN e f) := by
  let _ := complexModule hA hM e
  let _ := complexModule hA hN e
  let _ := complexModule hA hP e
  apply LinearMap.toAddMonoidHom_injective
  ext x
  rfl

end Canonical

/-! Complete unapplied interfaces retain independent algebra and carrier universes. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) → Module ℂ (FixedPart e M) := @complexModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) → (e : Idempotent A) →
    NonUnitalModuleHom A M N →
    letI := complexModule hA hM e
    letI := complexModule hA hN e
    FixedPart e M →ₗ[ℂ] FixedPart e N := @restrictLinear.{uA, uM, uN}

end Langlands.Algebra.NonUnitalModuleCorner
