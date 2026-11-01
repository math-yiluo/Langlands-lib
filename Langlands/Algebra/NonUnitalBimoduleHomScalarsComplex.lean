import Langlands.Algebra.NonUnitalBimoduleHomScalarsParts

set_option autoImplicit false

open MulOpposite

namespace Langlands.Algebra.NonUnitalBimoduleHomScalars

universe uR uS uX uZ

section LeftComplex

variable {R : Type uR} {S : Type uS} {X : Type uX} {Z : Type uZ}
  [NonUnitalRing R] [NonUnitalRing S]
  [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] [Module ℂ S]
  [AddCommGroup X] [AddCommGroup Z]
  [NonUnitalModule R X] [NonUnitalModule Sᵐᵒᵖ X] [NonUnitalModule R Z]
  (hR : IsIdempotented R) (hX : ActionsCommute R S X)
  (hRZ : IsNondegenerate R Z) (hRX : IsNondegenerate R X)
  (hc : SourceCompatible ℂ hR hRX (S := S))

/-- The actual complex residual source action, on the original Hom carrier. -/
noncomputable abbrev complexSourceActionHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    S →ₙₐ[ℂ] Module.End ℂ (NonUnitalModuleHom R X Z) :=
  sourceActionHom ℂ hR hX hRZ hRX hc

theorem complexSourceActionHom_toAddMonoidHom (s : S) :
    (complexSourceActionHom hR hX hRZ hRX hc s).toAddMonoidHom =
      NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s)) := rfl

theorem complexSourceActionHom_function (s : S) :
    (complexSourceActionHom hR hX hRZ hRX hc s : NonUnitalModuleHom R X Z →
      NonUnitalModuleHom R X Z) =
      NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s)) := rfl

@[simp] theorem complexSourceActionHom_apply (s : S) (f : NonUnitalModuleHom R X Z) (x : X) :
    complexSourceActionHom hR hX hRZ hRX hc s f x = f (op s • x) := rfl

theorem complexSourceActionHom_ofLinearEndHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    NonUnitalModule.ofLinearEndHom (complexSourceActionHom hR hX hRZ hRX hc) =
      NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX :=
  sourceActionHom_ofLinearEndHom ℂ hR hX hRZ hRX hc

end LeftComplex

section RightComplex

variable {R : Type uR} {S : Type uS} {Y : Type uX} {Z : Type uZ}
  [NonUnitalRing R] [NonUnitalRing S]
  [Module ℂ R] [Module ℂ S] [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hS : IsIdempotented S) (hY : ActionsCommute R S Y)
  (hSZ : IsNondegenerate Sᵐᵒᵖ Z) (hSY : IsNondegenerate Sᵐᵒᵖ Y)
  (hc : RightSourceCompatible ℂ hS hSY (R := R))

/-- The actual complex right residual action, on the original Hom carrier. -/
noncomputable abbrev complexRightSourceActionHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    Rᵐᵒᵖ →ₙₐ[ℂ] Module.End ℂ (NonUnitalModuleHom Sᵐᵒᵖ Y Z) :=
  rightSourceActionHom ℂ hS hY hSZ hSY hc

theorem complexRightSourceActionHom_toAddMonoidHom (r : R) :
    (complexRightSourceActionHom hS hY hSZ hSY hc (op r)).toAddMonoidHom =
      NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r) := rfl

theorem complexRightSourceActionHom_function (r : R) :
    (complexRightSourceActionHom hS hY hSZ hSY hc (op r) :
      NonUnitalModuleHom Sᵐᵒᵖ Y Z → NonUnitalModuleHom Sᵐᵒᵖ Y Z) =
      NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r) := rfl

@[simp] theorem complexRightSourceActionHom_apply (r : R)
    (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) (y : Y) :
    complexRightSourceActionHom hS hY hSZ hSY hc (op r) f y = f (r • y) := rfl

theorem complexRightSourceActionHom_ofLinearEndHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    NonUnitalModule.ofLinearEndHom (complexRightSourceActionHom hS hY hSZ hSY hc) =
      NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY :=
  rightSourceActionHom_ofLinearEndHom ℂ hS hY hSZ hSY hc

end RightComplex

section LeftComplexParts

variable {R : Type uR} {S : Type uS} {X : Type uX} {Z : Type uZ}
  [NonUnitalRing R] [NonUnitalRing S]
  [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [AddCommGroup X] [AddCommGroup Z]
  [NonUnitalModule R X] [NonUnitalModule Sᵐᵒᵖ X] [NonUnitalModule R Z]
  (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hX : ActionsCommute R S X) (hRZ : IsNondegenerate R Z)

/-- Actual inherited complex coefficients on the original residual Hom part. -/
noncomputable abbrev complexSourcePartModule :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    Module ℂ (nondegeneratePart hS (NonUnitalModuleHom R X Z)) :=
  sourcePartModule ℂ hR hS hX hRZ

/-- The actual complex-linear original subtype inclusion. -/
noncomputable abbrev complexSourcePartInclusion :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := complexSourcePartModule hR hS hX hRZ
    nondegeneratePart hS (NonUnitalModuleHom R X Z) →ₗ[ℂ] NonUnitalModuleHom R X Z :=
  sourcePartInclusion ℂ hR hS hX hRZ

theorem complexSourcePartInclusion_toAddMonoidHom :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (complexSourcePartInclusion hR hS hX hRZ).toAddMonoidHom =
      (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom := rfl

theorem complexSourcePartInclusion_function :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (complexSourcePartInclusion hR hS hX hRZ :
      nondegeneratePart hS (NonUnitalModuleHom R X Z) → NonUnitalModuleHom R X Z) =
      Subtype.val := rfl

@[simp] theorem complexSourcePartInclusion_apply :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ f : nondegeneratePart hS (NonUnitalModuleHom R X Z),
      complexSourcePartInclusion hR hS hX hRZ f = f.val := fun _ => rfl

@[simp] theorem complexSourcePart_smul_apply (c : ℂ) :
    letI := NondegenerateScalars.module ℂ hR hRZ
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := complexSourcePartModule hR hS hX hRZ
    ∀ (f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) (x : X),
      (c • f : nondegeneratePart hS (NonUnitalModuleHom R X Z)).val x = c • f.val x :=
  sourcePart_smul_apply ℂ hR hS hX hRZ c

variable [Module ℂ S] (hRX : IsNondegenerate R X)
  (hc : SourceCompatible ℂ hR hRX (S := S))

/-- The actual complex residual action on the exact original part. -/
noncomputable abbrev complexSourcePartActionHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := complexSourcePartModule hR hS hX hRZ
    S →ₙₐ[ℂ] Module.End ℂ (nondegeneratePart hS (NonUnitalModuleHom R X Z)) :=
  sourcePartActionHom ℂ hR hS hX hRZ hRX hc

theorem complexSourcePartActionHom_toAddMonoidHom (s : S) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (complexSourcePartActionHom hR hS hX hRZ hRX hc s).toAddMonoidHom =
      NonUnitalModule.toEndHom
        (inferInstance : NonUnitalModule S (nondegeneratePart hS (NonUnitalModuleHom R X Z))) s := rfl

theorem complexSourcePartActionHom_function (s : S) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (complexSourcePartActionHom hR hS hX hRZ hRX hc s :
      nondegeneratePart hS (NonUnitalModuleHom R X Z) →
      nondegeneratePart hS (NonUnitalModuleHom R X Z)) = (s • ·) := rfl

theorem complexSourcePartActionHom_subtype_toAddMonoidHom (s : S) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom.comp
        (complexSourcePartActionHom hR hS hX hRZ hRX hc s).toAddMonoidHom =
      (NonUnitalBimoduleHomActions.precomposeAddHom (hX.rightActionHom (op s))).comp
        (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom := rfl

@[simp] theorem complexSourcePartActionHom_apply (s : S) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ (f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) (x : X),
      (complexSourcePartActionHom hR hS hX hRZ hRX hc s f).val x = f.val (op s • x) :=
  fun _ _ => rfl

theorem complexSourcePartActionHom_ofLinearEndHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := complexSourcePartModule hR hS hX hRZ
    NonUnitalModule.ofLinearEndHom (complexSourcePartActionHom hR hS hX hRZ hRX hc) =
      (inferInstance : NonUnitalModule S (nondegeneratePart hS (NonUnitalModuleHom R X Z))) :=
  sourcePartActionHom_ofLinearEndHom ℂ hR hS hX hRZ hRX hc

variable [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]

include hRX hc in
/-- Actual recovered and inherited complex Modules are equal. -/
theorem complexSourcePartRecoveredModule_eq :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    NondegenerateScalars.module ℂ hS
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom R X Z) hS) =
      complexSourcePartModule hR hS hX hRZ :=
  sourcePartRecoveredModule_eq ℂ hR hS hX hRZ hRX hc

include hRX hc in
/-- Equality of both complex scalar actions on every original part element. -/
theorem complexSourcePart_recovered_smul_eq (c : ℂ) :
    letI := NondegenerateModuleHomScalars.homModule ℂ hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ f : nondegeneratePart hS (NonUnitalModuleHom R X Z),
      (letI := NondegenerateScalars.module ℂ hS
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom R X Z) hS); c • f) =
      (letI := complexSourcePartModule hR hS hX hRZ; c • f) :=
  sourcePart_recovered_smul_eq ℂ hR hS hX hRZ hRX hc c

end LeftComplexParts


section RightComplexParts

variable {R : Type uR} {S : Type uS} {Y : Type uX} {Z : Type uZ}
  [NonUnitalRing R] [NonUnitalRing S]
  [Module ℂ S] [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hY : ActionsCommute R S Y) (hSZ : IsNondegenerate Sᵐᵒᵖ Z)

/-- Actual inherited complex coefficients on the original residual Hom part. -/
noncomputable abbrev complexRightSourcePartModule :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    Module ℂ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) :=
  rightSourcePartModule ℂ hR hS hY hSZ

/-- The actual complex-linear original subtype inclusion. -/
noncomputable abbrev complexRightSourcePartInclusion :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := complexRightSourcePartModule hR hS hY hSZ
    nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) →ₗ[ℂ] NonUnitalModuleHom Sᵐᵒᵖ Y Z :=
  rightSourcePartInclusion ℂ hR hS hY hSZ

theorem complexRightSourcePartInclusion_toAddMonoidHom :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (complexRightSourcePartInclusion hR hS hY hSZ).toAddMonoidHom =
      (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom := rfl

theorem complexRightSourcePartInclusion_function :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (complexRightSourcePartInclusion hR hS hY hSZ :
      nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) → NonUnitalModuleHom Sᵐᵒᵖ Y Z) =
      Subtype.val := rfl

@[simp] theorem complexRightSourcePartInclusion_apply :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z),
      complexRightSourcePartInclusion hR hS hY hSZ f = f.val := fun _ => rfl

@[simp] theorem complexRightSourcePart_smul_apply (c : ℂ) :
    letI := NondegenerateScalars.module ℂ hS.op hSZ
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := complexRightSourcePartModule hR hS hY hSZ
    ∀ (f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) (y : Y),
      (c • f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).val y = c • f.val y :=
  rightSourcePart_smul_apply ℂ hR hS hY hSZ c

variable [Module ℂ R] (hSY : IsNondegenerate Sᵐᵒᵖ Y)
  (hc : RightSourceCompatible ℂ hS hSY (R := R))

/-- The actual complex residual action on the exact original part. -/
noncomputable abbrev complexRightSourcePartActionHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := complexRightSourcePartModule hR hS hY hSZ
    Rᵐᵒᵖ →ₙₐ[ℂ] Module.End ℂ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) :=
  rightSourcePartActionHom ℂ hR hS hY hSZ hSY hc

theorem complexRightSourcePartActionHom_toAddMonoidHom (r : R) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (complexRightSourcePartActionHom hR hS hY hSZ hSY hc (op r)).toAddMonoidHom =
      NonUnitalModule.toEndHom
        (inferInstance : NonUnitalModule Rᵐᵒᵖ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))) (op r) := rfl

theorem complexRightSourcePartActionHom_function (r : R) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (complexRightSourcePartActionHom hR hS hY hSZ hSY hc (op r) :
      nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) →
      nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) = (op r • ·) := rfl

theorem complexRightSourcePartActionHom_subtype_toAddMonoidHom (r : R) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom.comp
        (complexRightSourcePartActionHom hR hS hY hSZ hSY hc (op r)).toAddMonoidHom =
      (NonUnitalBimoduleHomActions.precomposeAddHom (hY.leftActionHom r)).comp
        (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom := rfl

@[simp] theorem complexRightSourcePartActionHom_apply (r : R) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ (f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) (y : Y),
      (complexRightSourcePartActionHom hR hS hY hSZ hSY hc (op r) f).val y = f.val (r • y) :=
  fun _ _ => rfl

theorem complexRightSourcePartActionHom_ofLinearEndHom :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := complexRightSourcePartModule hR hS hY hSZ
    NonUnitalModule.ofLinearEndHom (complexRightSourcePartActionHom hR hS hY hSZ hSY hc) =
      (inferInstance : NonUnitalModule Rᵐᵒᵖ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))) :=
  rightSourcePartActionHom_ofLinearEndHom ℂ hR hS hY hSZ hSY hc

variable [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]

include hSY hc in
/-- Actual recovered and inherited complex Modules are equal. -/
theorem complexRightSourcePartRecoveredModule_eq :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    NondegenerateScalars.module ℂ hR.op
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op) =
      complexRightSourcePartModule hR hS hY hSZ :=
  rightSourcePartRecoveredModule_eq ℂ hR hS hY hSZ hSY hc

include hSY hc in
/-- Equality of both complex scalar actions on every original part element. -/
theorem complexRightSourcePart_recovered_smul_eq (c : ℂ) :
    letI := NondegenerateModuleHomScalars.homModule ℂ hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z),
      (letI := NondegenerateScalars.module ℂ hR.op
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op); c • f) =
      (letI := complexRightSourcePartModule hR hS hY hSZ; c • f) :=
  rightSourcePart_recovered_smul_eq ℂ hR hS hY hSZ hSY hc c

end RightComplexParts

end Langlands.Algebra.NonUnitalBimoduleHomScalars
