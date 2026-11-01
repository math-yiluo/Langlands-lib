import Langlands.Algebra.NonUnitalBimoduleHomScalars

/-!
# Inherited coefficients on exact nondegenerate parts of residual Hom spaces

Internal sufficient-input adapters for Renard I.2.1–I.2.3. The original
nondegenerate subtype, additive group and residual action are retained.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalBimoduleHomScalars

universe uK uA uV uR uS uX uY uZ

namespace CompatiblePart

variable (k : Type uK) {A : Type uA} {V : Type uV}
  [CommRing k] [NonUnitalRing A]
  [AddCommGroup V] [NonUnitalModule A V] [Module k V]

/-- A fixing idempotent still fixes the scaled vector, with the same witness. -/
theorem fixed_smul [SMulCommClass k A V] (c : k) (e : Idempotent A)
    {v : V} (hv : (e : A) • v = v) : (e : A) • (c • v) = c • v := by
  rw [← smul_comm c (e : A) v, hv]

/-- The exact original nondegenerate part is closed under ambient coefficients. -/
theorem smul_mem [SMulCommClass k A V] (hA : IsIdempotented A) (c : k)
    {v : V} (hv : v ∈ nondegeneratePart hA V) : c • v ∈ nondegeneratePart hA V := by
  obtain ⟨e, he⟩ := hv
  exact ⟨e, fixed_smul k c e he⟩

/-- Coefficients inherited on exactly the original subtype additive group. -/
noncomputable abbrev module [SMulCommClass k A V] (hA : IsIdempotented A) :
    Module k (nondegeneratePart hA V) where
  smul c v := ⟨c • v.val, smul_mem k hA c v.property⟩
  one_smul v := Subtype.ext (one_smul k v.val)
  mul_smul c d v := Subtype.ext (mul_smul c d v.val)
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c v w := Subtype.ext (smul_add c v.val w.val)
  add_smul c d v := Subtype.ext (add_smul c d v.val)
  zero_smul v := Subtype.ext (zero_smul k v.val)

@[simp] theorem smul_val [SMulCommClass k A V] (hA : IsIdempotented A)
    (c : k) (v : nondegeneratePart hA V) :
    letI := module k hA (V := V)
    ((c • v : nondegeneratePart hA V) : V) = c • (v : V) := rfl

/-- Complete function identity for inherited scalar multiplication after inclusion. -/
theorem smul_val_function [SMulCommClass k A V] (hA : IsIdempotented A) (c : k) :
    letI := module k hA (V := V)
    (fun v : nondegeneratePart hA V => ((c • v : nondegeneratePart hA V) : V)) =
      fun v : nondegeneratePart hA V => c • (v : V) := rfl

/-- The scalar inclusion identity as an equality of complete additive maps. -/
theorem smul_subtype_toAddMonoidHom [SMulCommClass k A V]
    (hA : IsIdempotented A) (c : k) :
    letI := module k hA (V := V)
    (nondegeneratePart hA V).subtype.toAddMonoidHom.comp
        (c • AddMonoidHom.id (nondegeneratePart hA V)) =
      (c • AddMonoidHom.id V).comp (nondegeneratePart hA V).subtype.toAddMonoidHom := rfl

/-- The actual coefficient-linear inclusion, with the published original additive map. -/
noncomputable def inclusion [SMulCommClass k A V] (hA : IsIdempotented A) :
    letI := module k hA (V := V)
    nondegeneratePart hA V →ₗ[k] V :=
  letI := module k hA (V := V)
  { toAddHom := (nondegeneratePart hA V).subtype.toAddMonoidHom.toAddHom
    map_smul' _ _ := rfl }

theorem inclusion_toAddMonoidHom [SMulCommClass k A V] (hA : IsIdempotented A) :
    (inclusion k hA (V := V)).toAddMonoidHom =
      (nondegeneratePart hA V).subtype.toAddMonoidHom := rfl

theorem inclusion_function [SMulCommClass k A V] (hA : IsIdempotented A) :
    (inclusion k hA (V := V) : nondegeneratePart hA V → V) = Subtype.val := rfl

@[simp] theorem inclusion_apply [SMulCommClass k A V] (hA : IsIdempotented A)
    (v : nondegeneratePart hA V) : inclusion k hA v = v.val := rfl

/-- The original inherited action is retained on the exact subtype. -/
theorem action_val (hA : IsIdempotented A) (a : A) (v : nondegeneratePart hA V) :
    ((a • v : nondegeneratePart hA V) : V) = a • (v : V) := rfl

variable [Module k A]

/-- Ambient coefficient compatibility restricts to the original subtype action. -/
theorem isScalarTower [SMulCommClass k A V] [IsScalarTower k A V]
    (hA : IsIdempotented A) :
    letI := module k hA (V := V)
    IsScalarTower k A (nondegeneratePart hA V) :=
  letI := module k hA (V := V)
  ⟨fun c a v => Subtype.ext (smul_assoc c a v.val)⟩

omit [Module k A] in
/-- Ambient commutation restricts to the original subtype action. -/
theorem smulCommClass [SMulCommClass k A V] (hA : IsIdempotented A) :
    letI := module k hA (V := V)
    SMulCommClass k A (nondegeneratePart hA V) :=
  letI := module k hA (V := V)
  ⟨fun c a v => Subtype.ext (smul_comm c a v.val)⟩

/-- The compatible coefficient-linear action of the original ring on its exact part. -/
noncomputable def actionHom [SMulCommClass k A V] [IsScalarTower k A V]
    (hA : IsIdempotented A) :
    letI := module k hA (V := V)
    A →ₙₐ[k] Module.End k (nondegeneratePart hA V) :=
  letI := module k hA (V := V)
  letI := isScalarTower k hA (V := V)
  letI := smulCommClass k hA (V := V)
  NonUnitalModule.toLinearEndHom k

@[simp] theorem actionHom_apply [SMulCommClass k A V] [IsScalarTower k A V]
    (hA : IsIdempotented A) (a : A) (v : nondegeneratePart hA V) :
    actionHom k hA a v = a • v := rfl

/-- Whole original-action equality, using the inherited original subtype action. -/
theorem ofLinearEndHom_actionHom [SMulCommClass k A V] [IsScalarTower k A V]
    (hA : IsIdempotented A) :
    letI := module k hA (V := V)
    NonUnitalModule.ofLinearEndHom (actionHom k hA (V := V)) =
      (inferInstance : NonUnitalModule A (nondegeneratePart hA V)) :=
  letI := module k hA (V := V)
  NonUnitalModule.ext (fun _ _ => rfl)

/-- Each linear scalar endomorphism has exactly the inherited additive endomorphism. -/
theorem actionHom_toAddMonoidHom [SMulCommClass k A V] [IsScalarTower k A V]
    (hA : IsIdempotented A) (a : A) :
    (actionHom k hA (V := V) a).toAddMonoidHom =
      NonUnitalModule.toEndHom
        (inferInstance : NonUnitalModule A (nondegeneratePart hA V)) a := rfl

/-- Entire action function, with its original subtype action. -/
theorem actionHom_function [SMulCommClass k A V] [IsScalarTower k A V]
    (hA : IsIdempotented A) (a : A) :
    (actionHom k hA (V := V) a : nondegeneratePart hA V → nondegeneratePart hA V) =
      (a • ·) := rfl

/-- Scalar recovery equals the inherited Module, using the exact intrinsic nondegeneracy proof. -/
theorem recoveredModule_eq [IsScalarTower k A A] [SMulCommClass k A A]
    [SMulCommClass k A V] [IsScalarTower k A V] (hA : IsIdempotented A) :
    NondegenerateScalars.module k hA (nondegeneratePart_isNondegenerate (M := V) hA) =
      module k hA (V := V) := by
  let := module k hA (V := V)
  let := isScalarTower k hA (V := V)
  exact NondegenerateScalars.module_eq_of_compatible k hA (nondegeneratePart_isNondegenerate hA)

/-- Equality of recovered and inherited scalar actions on every actual part element. -/
theorem recovered_smul_eq [IsScalarTower k A A] [SMulCommClass k A A]
    [SMulCommClass k A V] [IsScalarTower k A V] (hA : IsIdempotented A)
    (c : k) (v : nondegeneratePart hA V) :
    (letI := NondegenerateScalars.module k hA
      (nondegeneratePart_isNondegenerate (M := V) hA); c • v) =
      (letI := module k hA (V := V); c • v) := by
  rw [recoveredModule_eq k hA]

end CompatiblePart

section LeftParts

variable (k : Type uK) {R : Type uR} {S : Type uS} {X : Type uX} {Z : Type uZ}
  [CommRing k] [NonUnitalRing R] [NonUnitalRing S]
  [Module k R]
  [IsScalarTower k R R]
  [SMulCommClass k R R]
  [AddCommGroup X] [AddCommGroup Z]
  [NonUnitalModule R X] [NonUnitalModule Sᵐᵒᵖ X] [NonUnitalModule R Z]
  (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hX : ActionsCommute R S X) (hRZ : IsNondegenerate R Z)

/-- Coefficient scaling preserves the very same fixing idempotent. -/
theorem sourcePart_fixed_smul (c : k) (e : Idempotent S) (f : NonUnitalModuleHom R X Z) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (e : S) • f = f → (e : S) • (c • f) = c • f := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  exact CompatiblePart.fixed_smul k c e

/-- The exact original residual Hom part is closed under pointwise coefficients. -/
theorem sourcePart_smul_mem (c : k) (f : NonUnitalModuleHom R X Z) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    f ∈ nondegeneratePart hS (NonUnitalModuleHom R X Z) → c • f ∈ nondegeneratePart hS (NonUnitalModuleHom R X Z) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  exact CompatiblePart.smul_mem k hS c

/-- Pointwise coefficients on the unchanged original nondegenerate subtype. -/
noncomputable abbrev sourcePartModule :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    Module k (nondegeneratePart hS (NonUnitalModuleHom R X Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  exact CompatiblePart.module k hS

/-- Full scalar function after the original subtype inclusion. -/
theorem sourcePart_smul_val_function (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    (fun f : nondegeneratePart hS (NonUnitalModuleHom R X Z) => ((c • f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) : NonUnitalModuleHom R X Z)) =
      fun f : nondegeneratePart hS (NonUnitalModuleHom R X Z) => c • (f : NonUnitalModuleHom R X Z) := rfl

/-- Scalar inclusion identity as an equality of complete additive maps. -/
theorem sourcePart_smul_subtype_toAddMonoidHom (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom.comp
        (c • AddMonoidHom.id (nondegeneratePart hS (NonUnitalModuleHom R X Z))) =
      (c • AddMonoidHom.id (NonUnitalModuleHom R X Z)).comp
        (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom := rfl

@[simp] theorem sourcePart_smul_val (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    ∀ f : nondegeneratePart hS (NonUnitalModuleHom R X Z),
      ((c • f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) : NonUnitalModuleHom R X Z) = c • (f : NonUnitalModuleHom R X Z) := fun _ => rfl

/-- The inherited coefficient formula at every original source vector. -/
@[simp] theorem sourcePart_smul_apply (c : k) :
    letI := NondegenerateScalars.module k hR hRZ
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    ∀ (f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) (x : X),
      (c • f : nondegeneratePart hS (NonUnitalModuleHom R X Z)).val x = c • f.val x := fun _ _ => rfl

/-- The original subtype inclusion, as an actual coefficient-linear map. -/
noncomputable def sourcePartInclusion :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    (nondegeneratePart hS (NonUnitalModuleHom R X Z)) →ₗ[k] (NonUnitalModuleHom R X Z) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  exact CompatiblePart.inclusion k hS

theorem sourcePartInclusion_toAddMonoidHom :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (sourcePartInclusion k hR hS hX hRZ).toAddMonoidHom =
      (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom := rfl

theorem sourcePartInclusion_function :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (sourcePartInclusion k hR hS hX hRZ : (nondegeneratePart hS (NonUnitalModuleHom R X Z)) → (NonUnitalModuleHom R X Z)) = Subtype.val := rfl

@[simp] theorem sourcePartInclusion_apply :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ f : nondegeneratePart hS (NonUnitalModuleHom R X Z), sourcePartInclusion k hR hS hX hRZ f = f.val := fun _ => rfl

/-- The original residual action on the part retains its precomposition formula. -/
@[simp] theorem sourcePart_action_val (s : S) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ f : nondegeneratePart hS (NonUnitalModuleHom R X Z),
      ((s • f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) : NonUnitalModuleHom R X Z) = s • (f : NonUnitalModuleHom R X Z) := fun _ => rfl

@[simp] theorem sourcePart_action_apply (s : S) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ (f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) (x : X),
      (s • f : nondegeneratePart hS (NonUnitalModuleHom R X Z)).val x = f.val (MulOpposite.op s • x) := fun _ _ => rfl

variable [Module k S]

/-- The required source compatibility intrinsically restricts to the original part. -/
theorem sourcePartIsScalarTower (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    IsScalarTower k S (nondegeneratePart hS (NonUnitalModuleHom R X Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  let := sourceIsScalarTower k hR hX hRZ hRX hc
  exact CompatiblePart.isScalarTower k hS

omit [Module k S] in
/-- Pointwise coefficients commute with the inherited original residual action. -/
theorem sourcePartSmulCommClass :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    SMulCommClass k S (nondegeneratePart hS (NonUnitalModuleHom R X Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  exact CompatiblePart.smulCommClass k hS

/-- Coefficient-linear residual action on exactly the original part. -/
noncomputable def sourcePartActionHom (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    S →ₙₐ[k] Module.End k (nondegeneratePart hS (NonUnitalModuleHom R X Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  let := sourceIsScalarTower k hR hX hRZ hRX hc
  exact CompatiblePart.actionHom k hS

/-- Forgetting coefficients recovers the entire inherited original action. -/
theorem sourcePartActionHom_ofLinearEndHom (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    letI := sourcePartModule k hR hS hX hRZ
    NonUnitalModule.ofLinearEndHom (sourcePartActionHom k hR hS hX hRZ hRX hc) =
      (inferInstance : NonUnitalModule S (nondegeneratePart hS (NonUnitalModuleHom R X Z))) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  let := sourceIsScalarTower k hR hX hRZ hRX hc
  exact CompatiblePart.ofLinearEndHom_actionHom k hS

/-- Entire additive endomorphism at each residual scalar. -/
theorem sourcePartActionHom_toAddMonoidHom (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (sourcePartActionHom k hR hS hX hRZ hRX hc s).toAddMonoidHom =
      NonUnitalModule.toEndHom
        (inferInstance : NonUnitalModule S (nondegeneratePart hS (NonUnitalModuleHom R X Z))) s := rfl

/-- Entire function at each residual scalar. -/
theorem sourcePartActionHom_function (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (sourcePartActionHom k hR hS hX hRZ hRX hc s :
      (nondegeneratePart hS (NonUnitalModuleHom R X Z)) → (nondegeneratePart hS (NonUnitalModuleHom R X Z))) = (s • ·) := rfl

/-- Full underlying additive map after inclusion is the ambient precomposition. -/
theorem sourcePartActionHom_subtype_toAddMonoidHom (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom.comp
        (sourcePartActionHom k hR hS hX hRZ hRX hc s).toAddMonoidHom =
      (NonUnitalBimoduleHomActions.precomposeAddHom
        (hX.rightActionHom (MulOpposite.op s))).comp
          (nondegeneratePart hS (NonUnitalModuleHom R X Z)).subtype.toAddMonoidHom := rfl

@[simp] theorem sourcePartActionHom_apply (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ (f : nondegeneratePart hS (NonUnitalModuleHom R X Z)) (x : X),
      (sourcePartActionHom k hR hS hX hRZ hRX hc s f).val x =
        f.val (MulOpposite.op s • x) := fun _ _ => rfl

variable [IsScalarTower k S S]
  [SMulCommClass k S S]

/-- Recovered coefficients using the exact intrinsic nondegeneracy proof equal the inherited Module. -/
theorem sourcePartRecoveredModule_eq (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    NondegenerateScalars.module k hS
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom R X Z) hS) =
      sourcePartModule k hR hS hX hRZ := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  let := sourceIsScalarTower k hR hX hRZ hRX hc
  exact CompatiblePart.recoveredModule_eq k hS

/-- Equality of both coefficient actions on every element of the exact original part. -/
theorem sourcePart_recovered_smul_eq (hRX : IsNondegenerate R X)
    (hc : SourceCompatible k hR hRX (S := S)) (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ f : nondegeneratePart hS (NonUnitalModuleHom R X Z),
      (letI := NondegenerateScalars.module k hS
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom R X Z) hS); c • f) =
      (letI := sourcePartModule k hR hS hX hRZ; c • f) := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  let := sourceSmulCommClass k hR hX hRZ
  let := sourceIsScalarTower k hR hX hRZ hRX hc
  exact CompatiblePart.recovered_smul_eq k hS c

end LeftParts

section RightParts

variable (k : Type uK) {R : Type uR} {S : Type uS} {Y : Type uY} {Z : Type uZ}
  [CommRing k] [NonUnitalRing R] [NonUnitalRing S]
  [Module k S]
  [IsScalarTower k S S]
  [SMulCommClass k S S]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hR : IsIdempotented R) (hS : IsIdempotented S)
  (hY : ActionsCommute R S Y) (hSZ : IsNondegenerate Sᵐᵒᵖ Z)

/-- Coefficient scaling preserves the very same fixing idempotent. -/
theorem rightSourcePart_fixed_smul (c : k) (e : Idempotent Rᵐᵒᵖ) (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (e : Rᵐᵒᵖ) • f = f → (e : Rᵐᵒᵖ) • (c • f) = c • f := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  exact CompatiblePart.fixed_smul k c e

/-- The exact original residual Hom part is closed under pointwise coefficients. -/
theorem rightSourcePart_smul_mem (c : k) (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    f ∈ nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) → c • f ∈ nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  exact CompatiblePart.smul_mem k hR.op c

/-- Pointwise coefficients on the unchanged original nondegenerate subtype. -/
noncomputable abbrev rightSourcePartModule :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    Module k (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  exact CompatiblePart.module k hR.op

/-- Full scalar function after the original subtype inclusion. -/
theorem rightSourcePart_smul_val_function (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    (fun f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) => ((c • f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) : NonUnitalModuleHom Sᵐᵒᵖ Y Z)) =
      fun f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) => c • (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) := rfl

/-- Scalar inclusion identity as an equality of complete additive maps. -/
theorem rightSourcePart_smul_subtype_toAddMonoidHom (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom.comp
        (c • AddMonoidHom.id (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))) =
      (c • AddMonoidHom.id (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).comp
        (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom := rfl

@[simp] theorem rightSourcePart_smul_val (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    ∀ f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z),
      ((c • f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) : NonUnitalModuleHom Sᵐᵒᵖ Y Z) = c • (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) := fun _ => rfl

/-- The inherited coefficient formula at every original source vector. -/
@[simp] theorem rightSourcePart_smul_apply (c : k) :
    letI := NondegenerateScalars.module k hS.op hSZ
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    ∀ (f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) (y : Y),
      (c • f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).val y = c • f.val y := fun _ _ => rfl

/-- The original subtype inclusion, as an actual coefficient-linear map. -/
noncomputable def rightSourcePartInclusion :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) →ₗ[k] (NonUnitalModuleHom Sᵐᵒᵖ Y Z) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  exact CompatiblePart.inclusion k hR.op

theorem rightSourcePartInclusion_toAddMonoidHom :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (rightSourcePartInclusion k hR hS hY hSZ).toAddMonoidHom =
      (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom := rfl

theorem rightSourcePartInclusion_function :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (rightSourcePartInclusion k hR hS hY hSZ : (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) → (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) = Subtype.val := rfl

@[simp] theorem rightSourcePartInclusion_apply :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z), rightSourcePartInclusion k hR hS hY hSZ f = f.val := fun _ => rfl

/-- The original residual action on the part retains its precomposition formula. -/
@[simp] theorem rightSourcePart_action_val (r : R) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z),
      ((MulOpposite.op r • f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) : NonUnitalModuleHom Sᵐᵒᵖ Y Z) = MulOpposite.op r • (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) := fun _ => rfl

@[simp] theorem rightSourcePart_action_apply (r : R) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ (f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) (y : Y),
      (MulOpposite.op r • f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).val y = f.val (r • y) := fun _ _ => rfl

variable [Module k R]

/-- The required source compatibility intrinsically restricts to the original part. -/
theorem rightSourcePartIsScalarTower (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    IsScalarTower k Rᵐᵒᵖ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  let := rightSourceIsScalarTower k hS hY hSZ hSY hc
  exact CompatiblePart.isScalarTower k hR.op

omit [Module k R] in
/-- Pointwise coefficients commute with the inherited original residual action. -/
theorem rightSourcePartSmulCommClass :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    SMulCommClass k Rᵐᵒᵖ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  exact CompatiblePart.smulCommClass k hR.op

/-- Coefficient-linear residual action on exactly the original part. -/
noncomputable def rightSourcePartActionHom (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    Rᵐᵒᵖ →ₙₐ[k] Module.End k (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  let := rightSourceIsScalarTower k hS hY hSZ hSY hc
  exact CompatiblePart.actionHom k hR.op

/-- Forgetting coefficients recovers the entire inherited original action. -/
theorem rightSourcePartActionHom_ofLinearEndHom (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    letI := rightSourcePartModule k hR hS hY hSZ
    NonUnitalModule.ofLinearEndHom (rightSourcePartActionHom k hR hS hY hSZ hSY hc) =
      (inferInstance : NonUnitalModule Rᵐᵒᵖ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  let := rightSourceIsScalarTower k hS hY hSZ hSY hc
  exact CompatiblePart.ofLinearEndHom_actionHom k hR.op

/-- Entire additive endomorphism at each residual scalar. -/
theorem rightSourcePartActionHom_toAddMonoidHom (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (rightSourcePartActionHom k hR hS hY hSZ hSY hc (MulOpposite.op r)).toAddMonoidHom =
      NonUnitalModule.toEndHom
        (inferInstance : NonUnitalModule Rᵐᵒᵖ (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))) (MulOpposite.op r) := rfl

/-- Entire function at each residual scalar. -/
theorem rightSourcePartActionHom_function (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (rightSourcePartActionHom k hR hS hY hSZ hSY hc (MulOpposite.op r) :
      (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) → (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))) = (MulOpposite.op r • ·) := rfl

/-- Full underlying additive map after inclusion is the ambient precomposition. -/
theorem rightSourcePartActionHom_subtype_toAddMonoidHom (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom.comp
        (rightSourcePartActionHom k hR hS hY hSZ hSY hc (MulOpposite.op r)).toAddMonoidHom =
      (NonUnitalBimoduleHomActions.precomposeAddHom
        (hY.leftActionHom r)).comp
          (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)).subtype.toAddMonoidHom := rfl

@[simp] theorem rightSourcePartActionHom_apply (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ (f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) (y : Y),
      (rightSourcePartActionHom k hR hS hY hSZ hSY hc (MulOpposite.op r) f).val y =
        f.val (r • y) := fun _ _ => rfl

variable [IsScalarTower k R R]
  [SMulCommClass k R R]

/-- Recovered coefficients using the exact intrinsic nondegeneracy proof equal the inherited Module. -/
theorem rightSourcePartRecoveredModule_eq (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    NondegenerateScalars.module k hR.op
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op) =
      rightSourcePartModule k hR hS hY hSZ := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  let := rightSourceIsScalarTower k hS hY hSZ hSY hc
  exact CompatiblePart.recoveredModule_eq k hR.op

/-- Equality of both coefficient actions on every element of the exact original part. -/
theorem rightSourcePart_recovered_smul_eq (hSY : IsNondegenerate Sᵐᵒᵖ Y)
    (hc : RightSourceCompatible k hS hSY (R := R)) (c : k) :
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z),
      (letI := NondegenerateScalars.module k hR.op
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op); c • f) =
      (letI := rightSourcePartModule k hR hS hY hSZ; c • f) := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  let := rightSourceSmulCommClass k hS hY hSZ
  let := rightSourceIsScalarTower k hS hY hSZ hSY hc
  exact CompatiblePart.recovered_smul_eq k hR.op c

end RightParts

end Langlands.Algebra.NonUnitalBimoduleHomScalars
