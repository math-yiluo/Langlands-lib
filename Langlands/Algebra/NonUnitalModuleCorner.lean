import Langlands.Algebra.NonUnitalModuleUniformity
import Langlands.Algebra.NondegenerateModuleAdditive
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The actual fixed-part splitting and corner functor

Renard (9 July 2026), Chapter I conventions, printed p.6/PDF12, and
I.3.1, printed p.19/PDF25. All ambient actions are the specified original
nonunital actions. The splitting is additive.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCorner

open CategoryTheory

universe uA uM uN uP

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [hM : NonUnitalModule A M] [hN : NonUnitalModule A N] [hP : NonUnitalModule A P]

/-- The published endomorphism description, explicitly selecting the original action. -/
abbrev originalAction : A →ₙ+* AddMonoid.End M := NonUnitalModule.toEndHom hM

theorem originalAction_apply (a : A) (m : M) :
    originalAction a m = hM.toDistribSMul.toSMul.smul a m := rfl

@[simp] theorem originalAction_zero (m : M) :
    originalAction (0 : A) m = 0 :=
  congrArg (fun f : AddMonoid.End M => f m) originalAction.map_zero

@[simp] theorem originalAction_mul (a b : A) (m : M) :
    originalAction (a * b) m = originalAction a (originalAction b m) :=
  congrArg (fun f : AddMonoid.End M => f m) (originalAction.map_mul a b)

theorem originalAction_coordinate (e : Idempotent A) :
    originalAction (M := M) (e : A) = e.leftActionCoordinate := rfl

@[simp] theorem coordinate_idempotent (e : Idempotent A) (m : M) :
    e.leftActionCoordinate (e.leftActionCoordinate m) = e.leftActionCoordinate m := by
  change originalAction (e : A) (originalAction (e : A) m) = originalAction (e : A) m
  rw [← originalAction_mul, e.property.eq]

/-- The actual additive subgroup of vectors fixed by the chosen idempotent. -/
def fixedPart (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] : AddSubgroup M where
  carrier := {m | e.leftActionCoordinate m = m}
  zero_mem' := (e.leftActionCoordinate (M := M)).map_zero
  add_mem' := by
    intro m n hm hn
    change e.leftActionCoordinate (m + n) = m + n
    rw [map_add, hm, hn]
  neg_mem' := by
    intro m hm
    change e.leftActionCoordinate (-m) = -m
    rw [map_neg, hm]

@[simp] theorem mem_fixedPart (e : Idempotent A) (m : M) :
    m ∈ fixedPart e M ↔ e.leftActionCoordinate m = m := Iff.rfl

theorem mem_fixedPart_iff_image (e : Idempotent A) (m : M) :
    m ∈ fixedPart e M ↔ ∃ n : M, e.leftActionCoordinate n = m := by
  constructor
  · intro hm
    exact ⟨m, hm⟩
  · rintro ⟨n, rfl⟩
    exact coordinate_idempotent e n

theorem fixedPart_eq_range (e : Idempotent A) :
    fixedPart e M = (e.leftActionCoordinate (M := M)).range := by
  ext m
  exact mem_fixedPart_iff_image e m

/-- A dedicated carrier for the fixed subgroup. -/
def FixedPart (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] := ↥(fixedPart e M)

/-- Exactly the inherited subgroup structure. -/
instance fixedPartAddCommGroup (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] : AddCommGroup (FixedPart e M) :=
  inferInstanceAs (AddCommGroup ↥(fixedPart e M))

/-- The full additive inclusion; no ambient scalar-linearity is asserted. -/
def inclusion (e : Idempotent A) : FixedPart e M →+ M :=
  (fixedPart e M).subtype

@[simp] theorem inclusion_apply (e : Idempotent A) (x : FixedPart e M) :
    inclusion e x = x.val := rfl

theorem coe_inclusion (e : Idempotent A) :
    ⇑(inclusion (M := M) e) = fun x => x.val := rfl

@[simp] theorem inclusion_zero (e : Idempotent A) :
    inclusion (M := M) e 0 = 0 := (inclusion e).map_zero

/-- The full additive projection onto the fixed subgroup. -/
def projection (e : Idempotent A) : M →+ FixedPart e M where
  toFun m := ⟨e.leftActionCoordinate m, coordinate_idempotent e m⟩
  map_zero' := Subtype.ext (e.leftActionCoordinate (M := M)).map_zero
  map_add' m n := Subtype.ext ((e.leftActionCoordinate (M := M)).map_add m n)

@[simp] theorem projection_apply (e : Idempotent A) (m : M) :
    (projection e m).val = e.leftActionCoordinate m := rfl

theorem coe_projection (e : Idempotent A) :
    ⇑(projection (M := M) e) =
      fun m => ⟨e.leftActionCoordinate m, coordinate_idempotent e m⟩ := rfl

@[simp] theorem projection_zero (e : Idempotent A) :
    projection (M := M) e 0 = 0 := (projection e).map_zero

@[simp] theorem projection_inclusion (e : Idempotent A) :
    (projection (M := M) e).comp (inclusion e) = AddMonoidHom.id (FixedPart e M) := by
  ext x
  exact Subtype.ext x.property

@[simp] theorem inclusion_projection (e : Idempotent A) :
    (inclusion (M := M) e).comp (projection e) = e.leftActionCoordinate := rfl

/-- The original ambient action of a corner element preserves the fixed subgroup. -/
theorem corner_action_mem (e : Idempotent A) (a : Idempotent.Corner e)
    (x : FixedPart e M) :
    originalAction (M := M) (Idempotent.Corner.toAmbient e a) x.val ∈ fixedPart e M := by
  change originalAction (e : A) (originalAction a.val x.val) =
    originalAction a.val x.val
  rw [← originalAction_mul, ((Idempotent.mem_corner_iff e a.val).mp a.property).1]

/-- The actual unital action, for the published corner ring and inherited group. -/
instance fixedPartModule (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] : Module (Idempotent.Corner e) (FixedPart e M) where
  smul a x := ⟨originalAction (Idempotent.Corner.toAmbient e a) x.val,
    corner_action_mem e a x⟩
  one_smul x := Subtype.ext x.property
  mul_smul a b x := Subtype.ext (originalAction_mul a.val b.val x.val)
  smul_zero a := Subtype.ext ((originalAction a.val).map_zero)
  smul_add a x y := Subtype.ext ((originalAction a.val).map_add x.val y.val)
  add_smul a b x := Subtype.ext
    (congrArg (fun f : AddMonoid.End M => f x.val) (originalAction.map_add a.val b.val))
  zero_smul x := Subtype.ext
    (congrArg (fun f : AddMonoid.End M => f x.val) originalAction.map_zero)

@[simp] theorem fixedPart_smul_val (e : Idempotent A)
    (a : Idempotent.Corner e) (x : FixedPart e M) :
    (a • x).val = originalAction (Idempotent.Corner.toAmbient e a) x.val := rfl

/-- The action formula using the named module's own scalar operation. -/
theorem fixedPartModule_smul (e : Idempotent A)
    (a : Idempotent.Corner e) (x : FixedPart e M) :
    (fixedPartModule e M).toSMul.smul a x =
      ⟨originalAction (Idempotent.Corner.toAmbient e a) x.val,
        corner_action_mem e a x⟩ := rfl

/-- The complete action formula explicitly installs all three chosen structures. -/
theorem fixedPart_smul (e : Idempotent A) (a : Idempotent.Corner e) (x : FixedPart e M) :
    letI := Idempotent.Corner.ring e
    letI := fixedPartAddCommGroup e M
    letI := fixedPartModule e M
    a • x = ⟨originalAction (Idempotent.Corner.toAmbient e a) x.val,
      corner_action_mem e a x⟩ := rfl

/-- The unit of the named corner ring acts as the identity. -/
theorem fixedPart_one_smul (e : Idempotent A) (x : FixedPart e M) :
    letI := Idempotent.Corner.ring e
    letI := fixedPartAddCommGroup e M
    letI := fixedPartModule e M
    (1 : Idempotent.Corner e) • x = x := one_smul _ x

/-- The complementary additive operator is identity minus the original coordinate. -/
def residual (e : Idempotent A) : M →+ M :=
  AddMonoidHom.id M - e.leftActionCoordinate

@[simp] theorem residual_apply (e : Idempotent A) (m : M) :
    residual e m = m - e.leftActionCoordinate m := rfl

theorem coe_residual (e : Idempotent A) :
    ⇑(residual (M := M) e) = fun m => m - e.leftActionCoordinate m := rfl

@[simp] theorem residual_zero (e : Idempotent A) :
    residual (M := M) e 0 = 0 := (residual e).map_zero

theorem mem_kernel_iff_residual (e : Idempotent A) (m : M) :
    m ∈ e.leftActionKernel ↔ ∃ n : M, residual e n = m := by
  rw [Idempotent.mem_leftActionKernel_iff_residual]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

theorem kernel_eq_residual_range (e : Idempotent A) :
    e.leftActionKernel (M := M) = (residual e).range := by
  ext m
  exact mem_kernel_iff_residual e m

/-- The additive splitting with the published original-action kernel. -/
def splitting (e : Idempotent A) : M ≃+ FixedPart e M × e.leftActionKernel (M := M) where
  toFun m := (projection e m, ⟨residual e m,
    (mem_kernel_iff_residual e _).mpr ⟨m, rfl⟩⟩)
  invFun p := p.1.val + p.2.val
  left_inv m := by
    change e.leftActionCoordinate m + (m - e.leftActionCoordinate m) = m
    rw [add_comm, sub_add_cancel]
  right_inv p := by
    rcases p with ⟨x, y⟩
    have hx : e.leftActionCoordinate x.val = x.val := x.property
    have hy : e.leftActionCoordinate y.val = 0 := y.property
    apply Prod.ext
    · apply Subtype.ext
      change e.leftActionCoordinate (x.val + y.val) = x.val
      rw [map_add, hx, hy, add_zero]
    · apply Subtype.ext
      change x.val + y.val - e.leftActionCoordinate (x.val + y.val) = y.val
      rw [map_add, hx, hy, add_zero, add_sub_cancel_left]
  map_add' m n := by
    apply Prod.ext
    · exact (projection e).map_add m n
    · exact Subtype.ext ((residual e).map_add m n)

theorem coe_splitting (e : Idempotent A) :
    ⇑(splitting (M := M) e) = fun m =>
      (projection e m, ⟨residual e m, (mem_kernel_iff_residual e _).mpr ⟨m, rfl⟩⟩) := rfl

theorem coe_splitting_symm (e : Idempotent A) :
    ⇑(splitting (M := M) e).symm = fun p => p.1.val + p.2.val := rfl

@[simp] theorem splitting_fst_val (e : Idempotent A) (m : M) :
    ((splitting e m).1).val = e.leftActionCoordinate m := rfl

@[simp] theorem splitting_snd_val (e : Idempotent A) (m : M) :
    ((splitting e m).2).val = m - e.leftActionCoordinate m := rfl

@[simp] theorem splitting_symm_apply (e : Idempotent A)
    (p : FixedPart e M × e.leftActionKernel (M := M)) :
    (splitting e).symm p = p.1.val + p.2.val := rfl

/-- The splitting includes zero without a nontriviality assumption. -/
@[simp] theorem splitting_zero (e : Idempotent A) :
    splitting (M := M) e 0 = 0 := (splitting (M := M) e).map_zero

/-- Every original intertwiner preserves the actual fixed subgroup. -/
theorem map_mem_fixedPart (e : Idempotent A) (f : NonUnitalModuleHom A M N)
    {m : M} (hm : m ∈ fixedPart e M) : f m ∈ fixedPart e N := by
  change (e : A) • f m = f m
  rw [← f.map_smul, show (e : A) • m = m from hm]

/-- Restriction of an original additive intertwiner is corner-linear. -/
def restrict (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    FixedPart e M →ₗ[Idempotent.Corner e] FixedPart e N where
  toFun x := ⟨f x.val, map_mem_fixedPart e f x.property⟩
  map_add' x y := Subtype.ext (f.map_add x.val y.val)
  map_smul' a x := Subtype.ext (f.map_smul a.val x.val)

@[simp] theorem restrict_apply (e : Idempotent A) (f : NonUnitalModuleHom A M N)
    (x : FixedPart e M) : (restrict e f x).val = f x.val := rfl

theorem coe_restrict (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    ⇑(restrict e f) = fun x => ⟨f x.val, map_mem_fixedPart e f x.property⟩ := rfl

@[simp] theorem restrict_apply_zero (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    restrict e f 0 = 0 := (restrict e f).map_zero

@[simp] theorem restrict_id (e : Idempotent A) :
    restrict e (NonUnitalModuleHom.id A M) = LinearMap.id := by
  ext x
  rfl

@[simp] theorem restrict_comp (e : Idempotent A)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    restrict e (g.comp f) = (restrict e g).comp (restrict e f) := by
  ext x
  rfl

@[simp] theorem restrict_zero (e : Idempotent A) :
    restrict e (0 : NonUnitalModuleHom A M N) = 0 := by
  ext x
  rfl

@[simp] theorem restrict_add (e : Idempotent A) (f g : NonUnitalModuleHom A M N) :
    restrict e (f + g) = restrict e f + restrict e g := by
  ext x
  rfl

@[simp] theorem restrict_neg (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    restrict e (-f) = -restrict e f := by
  ext x
  rfl

/-- Restriction as an additive map on the published pointwise Hom groups. -/
def restrictAddHom (e : Idempotent A) :
    NonUnitalModuleHom A M N →+
      (FixedPart e M →ₗ[Idempotent.Corner e] FixedPart e N) where
  toFun := restrict e
  map_zero' := restrict_zero e
  map_add' := restrict_add e

theorem coe_restrictAddHom (e : Idempotent A) :
    ⇑(restrictAddHom (M := M) (N := N) e) = restrict e := rfl

/-- Naturality as an equality of entire additive maps. -/
theorem inclusion_naturality (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    (inclusion e).comp (restrict e f).toAddMonoidHom =
      f.toAddMonoidHom.comp (inclusion e) := rfl

/-- Naturality as an equality of entire additive maps, including at zero. -/
theorem projection_naturality (e : Idempotent A) (f : NonUnitalModuleHom A M N) :
    (restrict e f).toAddMonoidHom.comp (projection e) =
      (projection e).comp f.toAddMonoidHom := by
  ext m
  exact Subtype.ext (f.map_smul (e : A) m)

/-- The actual corner functor on every original ambient module. -/
def functor (e : Idempotent A) :
    NonUnitalModuleCat.{uA, uM} A ⥤ ModuleCat.{uM} (Idempotent.Corner e) where
  obj M := ModuleCat.of (Idempotent.Corner e) (FixedPart e M)
  map f := ModuleCat.ofHom (restrict e f)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

@[simp] theorem functor_obj (e : Idempotent A) (M : NonUnitalModuleCat.{uA, uM} A) :
    (functor e).obj M = ModuleCat.of (Idempotent.Corner e) (FixedPart e M) := rfl

@[simp] theorem functor_map_hom (e : Idempotent A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((functor e).map f).hom = restrict e f := rfl

instance functor_additive (e : Idempotent A) : (functor.{uA, uM} e).Additive where
  map_add := by
    intro M N f g
    ext x
    rfl

@[simp] theorem functor_map_zero (e : Idempotent A) (M N : NonUnitalModuleCat.{uA, uM} A) :
    (functor e).map (0 : M ⟶ N) = 0 := (functor e).map_zero M N

@[simp] theorem functor_map_add (e : Idempotent A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f g : M ⟶ N) :
    (functor e).map (f + g) = (functor e).map f + (functor e).map g :=
  (functor e).map_add

/-- Renard's `j_e`, the restriction along the published nondegenerate inclusion. -/
def nondegenerateFunctor (e : Idempotent A) :
    NondegenerateModuleCat.{uA, uM} A ⥤ ModuleCat.{uM} (Idempotent.Corner e) :=
  nondegenerateInclusion A ⋙ functor e

instance nondegenerateFunctor_additive (e : Idempotent A) :
    (nondegenerateFunctor.{uA, uM} e).Additive := by
  change (nondegenerateInclusion A ⋙ functor.{uA, uM} e).Additive
  infer_instance

@[simp] theorem nondegenerateFunctor_obj (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (nondegenerateFunctor e).obj M =
      ModuleCat.of (Idempotent.Corner e) (FixedPart e M.obj) := rfl

@[simp] theorem nondegenerateFunctor_map_hom (e : Idempotent A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nondegenerateFunctor e).map f).hom = restrict e f.hom := rfl

@[simp] theorem nondegenerateFunctor_map_zero (e : Idempotent A)
    (M N : NondegenerateModuleCat.{uA, uM} A) :
    (nondegenerateFunctor e).map (0 : M ⟶ N) = 0 := (nondegenerateFunctor e).map_zero M N

@[simp] theorem nondegenerateFunctor_map_add (e : Idempotent A)
    {M N : NondegenerateModuleCat.{uA, uM} A} (f g : M ⟶ N) :
    (nondegenerateFunctor e).map (f + g) =
      (nondegenerateFunctor e).map f + (nondegenerateFunctor e).map g :=
  (nondegenerateFunctor e).map_add

/-- The zero idempotent has exactly the zero fixed subgroup. -/
theorem fixedPart_zero_idempotent :
    fixedPart (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) M = ⊥ := by
  ext m
  change originalAction (0 : A) m = m ↔ m = 0
  rw [originalAction_zero]
  exact eq_comm

/-- The complete projection is zero for the zero idempotent. -/
theorem projection_zero_idempotent :
    projection (M := M) (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) = 0 := by
  ext m
  apply Subtype.ext
  exact originalAction_zero m

/-- The complete complementary operator is the identity for the zero idempotent. -/
theorem residual_zero_idempotent :
    residual (M := M) (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) =
      AddMonoidHom.id M := by
  ext m
  change m - originalAction (0 : A) m = m
  rw [originalAction_zero, sub_zero]

/-- The complementary kernel is all of the carrier for the zero idempotent. -/
theorem kernel_zero_idempotent :
    (⟨0, IsIdempotentElem.zero⟩ : Idempotent A).leftActionKernel (M := M) = ⊤ := by
  ext m
  change originalAction (0 : A) m = 0 ↔ True
  rw [originalAction_zero]
  exact iff_true_intro rfl

omit hM in
/-- For a specified zero original action, every fixed subgroup is zero. -/
theorem fixedPart_zero_action (e : Idempotent A) :
    letI : NonUnitalModule A M := NonUnitalModule.zero
    fixedPart e M = ⊥ := by
  let : NonUnitalModule A M := NonUnitalModule.zero
  ext m
  change (0 : M) = m ↔ m = 0
  exact eq_comm

end Langlands.Algebra.NonUnitalModuleCorner
