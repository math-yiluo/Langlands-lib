import Langlands.Algebra.NonUnitalBimoduleHomActions
import Langlands.Algebra.NondegenerateModuleHomScalars

/-!
# Coefficient-linear residual actions on the original Hom spaces

An internal sufficient-input adapter for Renard I.2.1–I.2.3 and I.4.2.
The original actions and additive Hom groups are retained.
-/

set_option autoImplicit false

open MulOpposite

namespace Langlands.Algebra.NonUnitalBimoduleHomScalars

universe uK uR uS uX uZ

section Left

variable (k : Type uK) {R : Type uR} {S : Type uS} {X : Type uX} {Z : Type uZ}
  [CommRing k] [NonUnitalRing R] [NonUnitalRing S]
  [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  [Module k S]
  [AddCommGroup X] [AddCommGroup Z]
  [NonUnitalModule R X] [NonUnitalModule Sᵐᵒᵖ X] [NonUnitalModule R Z]
  (hR : IsIdempotented R) (hX : ActionsCommute R S X)
  (hRZ : IsNondegenerate R Z)

/-- Sufficient input relative to exactly the recovered source coefficient module. -/
def SourceCompatible (hRX : IsNondegenerate R X) : Prop :=
  letI := NondegenerateScalars.module k hR hRX
  IsScalarTower k Sᵐᵒᵖ X

/-- Each original precomposition map is coefficient-linear for the pointwise module. -/
noncomputable def sourceLinearEnd (s : S) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    Module.End k (NonUnitalModuleHom R X Z) :=
  letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  { toFun := NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s))
    map_add' := (NonUnitalBimoduleHomActions.precomposeAddHom
      (hX.rightActionHom (op s))).map_add
    map_smul' _ _ := by ext x; rfl }

omit [Module k S] in
theorem sourceLinearEnd_toAddMonoidHom (s : S) :
    (sourceLinearEnd k hR hX hRZ s).toAddMonoidHom =
      NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s)) := rfl

omit [Module k S] in
theorem sourceLinearEnd_function (s : S) :
    (sourceLinearEnd k hR hX hRZ s : NonUnitalModuleHom R X Z →
      NonUnitalModuleHom R X Z) =
      NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s)) := rfl

omit [Module k S] in
@[simp] theorem sourceLinearEnd_apply (s : S) (f : NonUnitalModuleHom R X Z) (x : X) :
    sourceLinearEnd k hR hX hRZ s f x = f (op s • x) := rfl

theorem source_smul_apply (s : S) (f : NonUnitalModuleHom R X Z) (x : X) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (s • f) x = f (op s • x) := rfl

/-- Compatibility in the residual algebra scalar follows from the source input. -/
theorem sourceIsScalarTower (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    IsScalarTower k S (NonUnitalModuleHom R X Z) := by
  let := NondegenerateScalars.module k hR hRX
  let := NondegenerateScalars.module k hR hRZ
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let : IsScalarTower k Sᵐᵒᵖ X := hc
  refine ⟨fun c s f => ?_⟩
  ext x
  change f ((c • op s) • x) = c • f (op s • x)
  rw [smul_assoc]
  exact NondegenerateScalars.map_smul k hR hRX hRZ f c (op s • x)

omit [Module k S] in
/-- Pointwise Hom coefficients commute with original source precomposition. -/
theorem sourceSmulCommClass :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    SMulCommClass k S (NonUnitalModuleHom R X Z) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  exact ⟨fun _ _ _ => by ext x; rfl⟩

/-- Actual coefficient-algebra action; all output compatibility is derived. -/
noncomputable def sourceActionHom (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    S →ₙₐ[k] Module.End k (NonUnitalModuleHom R X Z) :=
  letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  letI := sourceIsScalarTower k hR hX hRZ hRX hc
  letI := sourceSmulCommClass k hR hX hRZ
  NonUnitalModule.toLinearEndHom k

theorem sourceActionHom_linearEnd (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    sourceActionHom k hR hX hRZ hRX hc s = sourceLinearEnd k hR hX hRZ s := rfl

theorem sourceActionHom_toAddMonoidHom (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    (sourceActionHom k hR hX hRZ hRX hc s).toAddMonoidHom =
      NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s)) := rfl

theorem sourceActionHom_function (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    (sourceActionHom k hR hX hRZ hRX hc s : NonUnitalModuleHom R X Z →
      NonUnitalModuleHom R X Z) =
      NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s)) := rfl

@[simp] theorem sourceActionHom_apply (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) (f : NonUnitalModuleHom R X Z) (x : X) :
    sourceActionHom k hR hX hRZ hRX hc s f x = f (op s • x) := rfl

theorem sourceActionHom_ofLinearEndHom (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    NonUnitalModule.ofLinearEndHom (sourceActionHom k hR hX hRZ hRX hc) =
      NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX :=
  NonUnitalModule.ext fun _ _ => rfl

end Left

section Right

variable (k : Type uK) {R : Type uR} {S : Type uS} {Y : Type uX} {Z : Type uZ}
  [CommRing k] [NonUnitalRing R] [NonUnitalRing S]
  [Module k R]
  [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hS : IsIdempotented S) (hY : ActionsCommute R S Y)
  (hSZ : IsNondegenerate Sᵐᵒᵖ Z)

/-- Sufficient input relative to exactly the right-recovered source module. -/
def RightSourceCompatible (hSY : IsNondegenerate Sᵐᵒᵖ Y) : Prop :=
  letI := NondegenerateScalars.module k hS.op hSY
  IsScalarTower k R Y

/-- Original left-action precomposition, with pointwise recovered coefficients. -/
noncomputable def rightSourceLinearEnd (r : R) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    Module.End k (NonUnitalModuleHom Sᵐᵒᵖ Y Z) :=
  letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  { toFun := NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r)
    map_add' := (NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r)).map_add
    map_smul' _ _ := by ext y; rfl }

omit [Module k R] in
theorem rightSourceLinearEnd_toAddMonoidHom (r : R) :
    (rightSourceLinearEnd k hS hY hSZ r).toAddMonoidHom =
      NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r) := rfl

omit [Module k R] in
theorem rightSourceLinearEnd_function (r : R) :
    (rightSourceLinearEnd k hS hY hSZ r : NonUnitalModuleHom Sᵐᵒᵖ Y Z →
      NonUnitalModuleHom Sᵐᵒᵖ Y Z) =
      NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r) := rfl

omit [Module k R] in
@[simp] theorem rightSourceLinearEnd_apply (r : R)
    (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) (y : Y) :
    rightSourceLinearEnd k hS hY hSZ r f y = f (r • y) := rfl

theorem rightSource_smul_apply (r : R) (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) (y : Y) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (op r • f) y = f (r • y) := rfl

/-- Intrinsic coefficient compatibility in the right residual scalar. -/
theorem rightSourceIsScalarTower (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    IsScalarTower k Rᵐᵒᵖ (NonUnitalModuleHom Sᵐᵒᵖ Y Z) := by
  let := NondegenerateScalars.module k hS.op hSY
  let := NondegenerateScalars.module k hS.op hSZ
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let : IsScalarTower k R Y := hc
  refine ⟨fun c r f => ?_⟩
  ext y
  change f ((c • unop r) • y) = c • f (unop r • y)
  rw [smul_assoc]
  exact NondegenerateScalars.map_smul k hS.op hSY hSZ f c (unop r • y)

omit [Module k R] in
theorem rightSourceSmulCommClass :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    SMulCommClass k Rᵐᵒᵖ (NonUnitalModuleHom Sᵐᵒᵖ Y Z) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  exact ⟨fun _ _ _ => by ext y; rfl⟩

/-- Actual right residual action on the unchanged published Hom carrier. -/
noncomputable def rightSourceActionHom (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    Rᵐᵒᵖ →ₙₐ[k] Module.End k (NonUnitalModuleHom Sᵐᵒᵖ Y Z) :=
  letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  letI := rightSourceIsScalarTower k hS hY hSZ hSY hc
  letI := rightSourceSmulCommClass k hS hY hSZ
  NonUnitalModule.toLinearEndHom k

theorem rightSourceActionHom_linearEnd (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    rightSourceActionHom k hS hY hSZ hSY hc (op r) =
      rightSourceLinearEnd k hS hY hSZ r := rfl

theorem rightSourceActionHom_toAddMonoidHom (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    (rightSourceActionHom k hS hY hSZ hSY hc (op r)).toAddMonoidHom =
      NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r) := rfl

theorem rightSourceActionHom_function (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    (rightSourceActionHom k hS hY hSZ hSY hc (op r) : NonUnitalModuleHom Sᵐᵒᵖ Y Z →
      NonUnitalModuleHom Sᵐᵒᵖ Y Z) =
      NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r) := rfl

@[simp] theorem rightSourceActionHom_apply (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R)
    (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) (y : Y) :
    rightSourceActionHom k hS hY hSZ hSY hc (op r) f y = f (r • y) := rfl

theorem rightSourceActionHom_ofLinearEndHom (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    NonUnitalModule.ofLinearEndHom (rightSourceActionHom k hS hY hSZ hSY hc) =
      NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY :=
  NonUnitalModule.ext fun _ _ => rfl

end Right

end Langlands.Algebra.NonUnitalBimoduleHomScalars
