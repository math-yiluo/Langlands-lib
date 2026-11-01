import Langlands.Algebra.NonUnitalModuleDualFixedPartMaps

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualFixedPartComparison

open MulOpposite
open NonUnitalModuleDualFixedPartMaps
open NonUnitalModuleCorner (FixedPart)

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

def cornerOp (e : Idempotent A) (a : Idempotent.Corner e) :
    Idempotent.Corner (oppositeIdempotent e) := by
  refine ⟨op a.val, ?_⟩
  apply (Idempotent.mem_corner_iff _ _).mpr
  constructor
  · change op (a.val * (e : A)) = op a.val
    exact congrArg op ((Idempotent.mem_corner_iff e a.val).mp a.property).2
  · change op ((e : A) * a.val) = op a.val
    exact congrArg op ((Idempotent.mem_corner_iff e a.val).mp a.property).1

def cornerUnop (e : Idempotent A)
    (a : Idempotent.Corner (oppositeIdempotent e)) : Idempotent.Corner e := by
  refine ⟨a.val.unop, ?_⟩
  apply (Idempotent.mem_corner_iff e _).mpr
  have ha := (Idempotent.mem_corner_iff (oppositeIdempotent e) a.val).mp a.property
  constructor
  · exact congrArg unop ha.2
  · exact congrArg unop ha.1

def cornerOppositeEquiv (e : Idempotent A) :
    (Idempotent.Corner e)ᵐᵒᵖ ≃+* Idempotent.Corner (oppositeIdempotent e) where
  toFun a := cornerOp e a.unop
  invFun a := op (cornerUnop e a)
  left_inv a := by
    apply unop_injective
    exact Subtype.ext rfl
  right_inv a := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem cornerOppositeEquiv_val (e : Idempotent A)
    (a : (Idempotent.Corner e)ᵐᵒᵖ) :
    (cornerOppositeEquiv e a).val = op a.unop.val := rfl

theorem cornerOppositeEquiv_symm_val (e : Idempotent A)
    (a : Idempotent.Corner (oppositeIdempotent e)) :
    ((cornerOppositeEquiv e).symm a).unop.val = a.val.unop := rfl

section Maps

variable [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hM) :=
  NonUnitalModuleDual.fullAction hA hM

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hM) :=
  NonUnitalModuleDual.dualAction hA hM

abbrev FullRightFixedPart (e : Idempotent A) :=
  FixedPart (oppositeIdempotent e) (NonUnitalModuleDual.FullDual hA hM)

theorem fullRightFixedPart_eq_subtype (e : Idempotent A) :
    FullRightFixedPart hA hM e =
      {psi : NonUnitalModuleDual.FullDual hA hM // op (e : A) • psi = psi} := rfl

@[instance_reducible]
def fullRightFixedModule (e : Idempotent A) :
    Module ℂ (FullRightFixedPart hA hM e) := by
  letI := NonUnitalModuleDual.full_smulCommClass hA hM
  exact NonUnitalModuleCorner.inheritedComplexModule
    (oppositeIdempotent e) (NonUnitalModuleDual.FullDual hA hM)

theorem fullRightFixedModule_smul_val (e : Idempotent A) (c : ℂ)
    (psi : FullRightFixedPart hA hM e) :
    letI := fullRightFixedModule hA hM e
    (c • psi).val = c • psi.val := rfl

theorem fullRightFixedModule_smulCommClass (e : Idempotent A) :
    letI := fullRightFixedModule hA hM e
    SMulCommClass ℂ (Idempotent.Corner (oppositeIdempotent e))
      (FullRightFixedPart hA hM e) := by
  let _ := fullRightFixedModule hA hM e
  exact ⟨fun _ _ _ => Subtype.ext rfl⟩

/-- The ordinary dual has the original right corner action by precomposition. -/
@[instance_reducible]
def fixedPartDualCornerModule (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    Module (Idempotent.Corner (oppositeIdempotent e))
      (Module.Dual ℂ (FixedPart e M)) := by
  letI := NonUnitalModuleCorner.complexModule hA hM e
  exact
    { smul a ell := ell.comp
        (NonUnitalModuleCorner.cornerLinearAction hA hM e (cornerUnop e a))
      one_smul ell := by
        ext x
        change ell ((1 : Idempotent.Corner e) • x) = ell x
        rw [one_smul]
      mul_smul a b ell := by
        ext x
        change ell ((cornerUnop e (a * b)) • x) =
          ell ((cornerUnop e b) • ((cornerUnop e a) • x))
        apply congrArg ell
        apply Subtype.ext
        change (a.val * b.val).unop • x.val =
          b.val.unop • (a.val.unop • x.val)
        rw [unop_mul, mul_smul]
      smul_zero a := by ext x; rfl
      smul_add a ell k := by ext x; rfl
      add_smul a b ell := by
        ext x
        change ell ((cornerUnop e a + cornerUnop e b) • x) =
          ell ((cornerUnop e a) • x) + ell ((cornerUnop e b) • x)
        rw [add_smul, ell.map_add]
      zero_smul ell := by
        ext x
        change ell ((0 : Idempotent.Corner e) • x) = 0
        rw [zero_smul, ell.map_zero] }

theorem fixedPartDualCornerModule_functional (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    ∀ (a : Idempotent.Corner (oppositeIdempotent e))
      (ell : Module.Dual ℂ (FixedPart e M)),
      a • ell = ell.comp
        (NonUnitalModuleCorner.cornerLinearAction hA hM e (cornerUnop e a)) :=
  fun _ _ => rfl

theorem fixedPartDualCornerModule_apply (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    ∀ (a : Idempotent.Corner (oppositeIdempotent e))
      (ell : Module.Dual ℂ (FixedPart e M)) (x : FixedPart e M),
      (a • ell) x = ell ((cornerUnop e a) • x) := fun _ _ _ => rfl

theorem fixedPartDualCornerModule_smulCommClass (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    SMulCommClass ℂ (Idempotent.Corner (oppositeIdempotent e))
      (Module.Dual ℂ (FixedPart e M)) := by
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  let _ := fixedPartDualCornerModule hA hM e
  exact ⟨fun _ _ _ => by ext x; rfl⟩

def toFullFixed (e : Idempotent A) :
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    RightFixedPart hA hM e →ₗ[ℂ] FullRightFixedPart hA hM e :=
  letI := rightFixedModule hA hM e
  letI := fullRightFixedModule hA hM e
  { toFun := fun phi =>
      ⟨phi.val.val, rightFixedPart_fixed_functional hA hM e phi⟩
    map_add' _ _ := Subtype.ext rfl
    map_smul' _ _ := Subtype.ext rfl }

def fromFullFixed (e : Idempotent A) :
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    FullRightFixedPart hA hM e →ₗ[ℂ] RightFixedPart hA hM e :=
  letI := rightFixedModule hA hM e
  letI := fullRightFixedModule hA hM e
  { toFun := fun psi => ofFixedFull hA hM e psi.val psi.property
    map_add' _ _ := Subtype.ext (Subtype.ext rfl)
    map_smul' _ _ := Subtype.ext (Subtype.ext rfl) }

def toFullFixedCorner (e : Idempotent A) :
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      FullRightFixedPart hA hM e := by
  let _ := rightFixedModule hA hM e
  let _ := fullRightFixedModule hA hM e
  exact
    { toFun := toFullFixed hA hM e
      map_add' := (toFullFixed hA hM e).map_add
      map_smul' _ _ := Subtype.ext rfl }

def fromFullFixedCorner (e : Idempotent A) :
    FullRightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e := by
  let _ := rightFixedModule hA hM e
  let _ := fullRightFixedModule hA hM e
  exact
    { toFun := fromFullFixed hA hM e
      map_add' := (fromFullFixed hA hM e).map_add
      map_smul' _ _ := Subtype.ext (Subtype.ext rfl) }

def restrictionCorner (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      Module.Dual ℂ (FixedPart e M) := by
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  let _ := fixedPartDualCornerModule hA hM e
  let _ := rightFixedModule hA hM e
  exact
    { toFun := restriction hA hM e
      map_add' := (restriction hA hM e).map_add
      map_smul' _ _ := by ext x; rfl }

def extensionCorner (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e := by
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  let _ := fixedPartDualCornerModule hA hM e
  let _ := rightFixedModule hA hM e
  let _ := NondegenerateScalars.complexModule hA hM
  exact
    { toFun := extension hA hM e
      map_add' := (extension hA hM e).map_add
      map_smul' a ell := by
        apply Subtype.ext
        apply Subtype.ext
        apply LinearMap.ext
        intro m
        change ell ((cornerUnop e a) • (NonUnitalModuleCorner.projection e m)) =
          ell (NonUnitalModuleCorner.projection e (a.val.unop • m))
        apply congrArg ell
        apply Subtype.ext
        change a.val.unop • ((e : A) • m) =
          (e : A) • (a.val.unop • m)
        have ha := (Idempotent.mem_corner_iff e (cornerUnop e a).val).mp
          (cornerUnop e a).property
        change (e : A) * a.val.unop = a.val.unop ∧
          a.val.unop * (e : A) = a.val.unop at ha
        rw [← mul_smul, ← mul_smul, ha.1, ha.2] }

theorem toFullFixed_functional (e : Idempotent A)
    (phi : RightFixedPart hA hM e) :
    (toFullFixed hA hM e phi).val = phi.val.val := rfl

theorem fromFullFixed_functional (e : Idempotent A)
    (psi : FullRightFixedPart hA hM e) :
    (fromFullFixed hA hM e psi).val.val = psi.val := rfl

theorem toFullFixed_coe (e : Idempotent A) :
    ⇑(toFullFixed hA hM e) =
      fun phi => ⟨phi.val.val, rightFixedPart_fixed_functional hA hM e phi⟩ := rfl

theorem fromFullFixed_coe (e : Idempotent A) :
    ⇑(fromFullFixed hA hM e) =
      fun psi => ofFixedFull hA hM e psi.val psi.property := rfl

theorem toFullFixedCorner_toAddMonoidHom (e : Idempotent A) :
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    (toFullFixedCorner hA hM e).toAddMonoidHom =
      (toFullFixed hA hM e).toAddMonoidHom := rfl

theorem fromFullFixedCorner_toAddMonoidHom (e : Idempotent A) :
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    (fromFullFixedCorner hA hM e).toAddMonoidHom =
      (fromFullFixed hA hM e).toAddMonoidHom := rfl

theorem restrictionCorner_toAddMonoidHom (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    letI := rightFixedModule hA hM e
    (restrictionCorner hA hM e).toAddMonoidHom =
      (restriction hA hM e).toAddMonoidHom := rfl

theorem extensionCorner_toAddMonoidHom (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    letI := rightFixedModule hA hM e
    (extensionCorner hA hM e).toAddMonoidHom =
      (extension hA hM e).toAddMonoidHom := rfl

theorem restrictionCorner_functional (e : Idempotent A)
    (phi : RightFixedPart hA hM e) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    restrictionCorner hA hM e phi =
      phi.val.val.comp (NonUnitalModuleCorner.inclusionLinear hA hM e) := rfl

theorem extensionCorner_functional (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      (extensionCorner hA hM e ell).val.val =
        ell.comp (NonUnitalModuleCorner.projectionLinear hA hM e) := fun _ => rfl

end Maps

/-! Complete unapplied interfaces keep algebra and carrier universes independent. -/

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    (Idempotent.Corner e)ᵐᵒᵖ ≃+* Idempotent.Corner (oppositeIdempotent e) :=
  @cornerOppositeEquiv.{uA}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Type uM := @FullRightFixedPart.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) → Module ℂ (FullRightFixedPart hA hM e) :=
  @fullRightFixedModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    Module (Idempotent.Corner (oppositeIdempotent e))
      (Module.Dual ℂ (FixedPart e M)) :=
  @fixedPartDualCornerModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    RightFixedPart hA hM e →ₗ[ℂ] FullRightFixedPart hA hM e :=
  @toFullFixed.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    FullRightFixedPart hA hM e →ₗ[ℂ] RightFixedPart hA hM e :=
  @fromFullFixed.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      FullRightFixedPart hA hM e :=
  @toFullFixedCorner.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    FullRightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e :=
  @fromFullFixedCorner.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      Module.Dual ℂ (FixedPart e M) :=
  @restrictionCorner.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e :=
  @extensionCorner.{uA, uM}

end Langlands.Algebra.NonUnitalModuleDualFixedPartComparison
