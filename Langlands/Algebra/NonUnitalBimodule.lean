import Langlands.Algebra.NonUnitalModuleAdditive
import Langlands.Algebra.RegularModuleHom

/-!
# Commuting original nonunital bimodules

Renard (9 July 2026), I.2.2–I.2.3, printed pp.15–18/PDF21–24: a left `A`-action
and a right `B`-action on one additive group, the right action being a left action
of `Bᵐᵒᵖ`, which commute. Neither a unit law nor nondegeneracy is imposed; the
two nondegeneracy conditions form a separate predicate.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra

universe uA uB uM uN uP

section Commute

variable (A : Type uA) (B : Type uB) (M : Type uM)
  [NonUnitalRing A] [NonUnitalRing B] [AddCommGroup M]
  [NonUnitalModule A M] [NonUnitalModule Bᵐᵒᵖ M]

/-- The specified left `A`-action and right `B`-action commute. -/
def ActionsCommute : Prop :=
  ∀ (a : A) (b : B) (m : M), a • (op b • m) = op b • (a • m)

/-- Two-sided nondegeneracy, the conjunction of the published one-sided predicates. -/
def IsNondegenerateBimodule : Prop :=
  IsNondegenerate A M ∧ IsRightNondegenerate B M

/-- The commutation equation is exactly the existing commuting-action class. -/
theorem actionsCommute_iff_smulCommClass :
    ActionsCommute A B M ↔ SMulCommClass A Bᵐᵒᵖ M :=
  ⟨fun h => ⟨fun a b m => h a b.unop m⟩, fun h a b m => h.smul_comm a (op b) m⟩

/-- The same equivalence with the two scalar types in the other order. -/
theorem actionsCommute_iff_smulCommClass' :
    ActionsCommute A B M ↔ SMulCommClass Bᵐᵒᵖ A M :=
  ⟨fun h => ⟨fun b a m => (h a b.unop m).symm⟩,
    fun h a b m => (h.smul_comm (op b) a m).symm⟩

end Commute

namespace ActionsCommute

variable {A : Type uA} {B : Type uB} {M : Type uM}
  [NonUnitalRing A] [NonUnitalRing B] [AddCommGroup M]
  [hA : NonUnitalModule A M] [hB : NonUnitalModule Bᵐᵒᵖ M]

/-- Adapter to the existing commuting-action class. -/
theorem smulCommClass (h : ActionsCommute A B M) : SMulCommClass A Bᵐᵒᵖ M :=
  (actionsCommute_iff_smulCommClass A B M).mp h

/-- Adapter to the existing commuting-action class, other scalar order. -/
theorem smulCommClass' (h : ActionsCommute A B M) : SMulCommClass Bᵐᵒᵖ A M :=
  (actionsCommute_iff_smulCommClass' A B M).mp h

/-- Adapter from the existing commuting-action class. -/
theorem of_smulCommClass [SMulCommClass A Bᵐᵒᵖ M] : ActionsCommute A B M :=
  (actionsCommute_iff_smulCommClass A B M).mpr inferInstance

/-- Adapter from the existing commuting-action class, other scalar order. -/
theorem of_smulCommClass' [SMulCommClass Bᵐᵒᵖ A M] : ActionsCommute A B M :=
  (actionsCommute_iff_smulCommClass' A B M).mpr inferInstance

/-- The commutation equation for an opposite scalar. -/
theorem smul_comm (h : ActionsCommute A B M) (a : A) (b : Bᵐᵒᵖ) (m : M) :
    a • (b • m) = b • (a • m) :=
  h a b.unop m

variable (h : ActionsCommute A B M)

/-- The action of `a` as an actual original right `B`-linear endomorphism. -/
def leftActionHom (a : A) : NonUnitalModuleHom Bᵐᵒᵖ M M where
  toAddMonoidHom := NonUnitalModule.toEndHom hA a
  map_smul' b m := h.smul_comm a b m

/-- The action of `b` as an actual original left `A`-linear endomorphism. -/
def rightActionHom (b : Bᵐᵒᵖ) : NonUnitalModuleHom A M M where
  toAddMonoidHom := NonUnitalModule.toEndHom hB b
  map_smul' a m := (h.smul_comm a b m).symm

@[simp] theorem leftActionHom_apply (a : A) (m : M) : h.leftActionHom a m = a • m := rfl

@[simp] theorem rightActionHom_apply (b : Bᵐᵒᵖ) (m : M) : h.rightActionHom b m = b • m := rfl

/-- The whole underlying additive map is the published endomorphism of the left action. -/
theorem leftActionHom_toAddMonoidHom (a : A) :
    (h.leftActionHom a).toAddMonoidHom = NonUnitalModule.toEndHom hA a := rfl

/-- The whole underlying additive map is the published endomorphism of the right action. -/
theorem rightActionHom_toAddMonoidHom (b : Bᵐᵒᵖ) :
    (h.rightActionHom b).toAddMonoidHom = NonUnitalModule.toEndHom hB b := rfl

theorem leftActionHom_zero : h.leftActionHom 0 = 0 := by
  ext m
  exact NonUnitalModule.zero_smul m

theorem rightActionHom_zero : h.rightActionHom 0 = 0 := by
  ext m
  exact NonUnitalModule.zero_smul m

theorem leftActionHom_add (a a' : A) :
    h.leftActionHom (a + a') = h.leftActionHom a + h.leftActionHom a' := by
  ext m
  exact NonUnitalModule.add_smul a a' m

theorem rightActionHom_add (b b' : Bᵐᵒᵖ) :
    h.rightActionHom (b + b') = h.rightActionHom b + h.rightActionHom b' := by
  ext m
  exact NonUnitalModule.add_smul b b' m

/-- Scalar multiplication becomes composition of the original Hom interface. -/
theorem leftActionHom_mul (a a' : A) :
    h.leftActionHom (a * a') = (h.leftActionHom a).comp (h.leftActionHom a') := by
  ext m
  exact mul_smul a a' m

/-- Multiplication in `Bᵐᵒᵖ` becomes composition in the same order. -/
theorem rightActionHom_mul (b b' : Bᵐᵒᵖ) :
    h.rightActionHom (b * b') = (h.rightActionHom b).comp (h.rightActionHom b') := by
  ext m
  exact mul_smul b b' m

/-- In right-action notation, multiplication in `B` composes in the reverse order. -/
theorem rightActionHom_op_mul (b b' : B) :
    h.rightActionHom (op (b * b')) =
      (h.rightActionHom (op b')).comp (h.rightActionHom (op b)) := by
  ext m
  exact right_mul_smul b b' m

/-- The additive scalar-to-Hom map of the left action. -/
def leftActionAddHom : A →+ NonUnitalModuleHom Bᵐᵒᵖ M M where
  toFun := h.leftActionHom
  map_zero' := h.leftActionHom_zero
  map_add' := h.leftActionHom_add

/-- The additive scalar-to-Hom map of the right action. -/
def rightActionAddHom : Bᵐᵒᵖ →+ NonUnitalModuleHom A M M where
  toFun := h.rightActionHom
  map_zero' := h.rightActionHom_zero
  map_add' := h.rightActionHom_add

@[simp] theorem leftActionAddHom_apply (a : A) : h.leftActionAddHom a = h.leftActionHom a := rfl

@[simp] theorem rightActionAddHom_apply (b : Bᵐᵒᵖ) :
    h.rightActionAddHom b = h.rightActionHom b := rfl

/-- Forgetting linearity after the scalar-to-Hom map gives the published endomorphism map. -/
theorem toAddMonoidHomAddHom_comp_leftActionAddHom :
    NonUnitalModuleHom.toAddMonoidHomAddHom.comp h.leftActionAddHom =
      (NonUnitalModule.toEndHom hA).toAddMonoidHom := rfl

/-- Forgetting linearity after the scalar-to-Hom map gives the published endomorphism map. -/
theorem toAddMonoidHomAddHom_comp_rightActionAddHom :
    NonUnitalModuleHom.toAddMonoidHomAddHom.comp h.rightActionAddHom =
      (NonUnitalModule.toEndHom hB).toAddMonoidHom := rfl

end ActionsCommute

section Degenerate

variable {A : Type uA} {B : Type uB} {M : Type uM}
  [NonUnitalRing A] [NonUnitalRing B] [AddCommGroup M]

/-- The original zero left action commutes with every right action. -/
theorem actionsCommute_zero_left [NonUnitalModule Bᵐᵒᵖ M] :
    @ActionsCommute A B M _ _ _ NonUnitalModule.zero _ :=
  fun _ b _ => (smul_zero (op b)).symm

/-- The original zero right action commutes with every left action. -/
theorem actionsCommute_zero_right [NonUnitalModule A M] :
    @ActionsCommute A B M _ _ _ _ NonUnitalModule.zero :=
  fun a _ _ => smul_zero a

/-- On a trivial carrier any two actions commute. -/
theorem actionsCommute_of_subsingleton [Subsingleton M] [NonUnitalModule A M]
    [NonUnitalModule Bᵐᵒᵖ M] : ActionsCommute A B M :=
  fun _ _ _ => Subsingleton.elim _ _

/-- On a trivial carrier any two actions are nondegenerate, the idempotent `0` fixing it. -/
theorem isNondegenerateBimodule_of_subsingleton [Subsingleton M] [NonUnitalModule A M]
    [NonUnitalModule Bᵐᵒᵖ M] : IsNondegenerateBimodule A B M :=
  ⟨fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩,
    fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩⟩

/-- The zero action on a nonzero group is degenerate, for every scalar ring. -/
theorem not_isNondegenerate_zero [Nontrivial M] :
    ¬ @IsNondegenerate A M _ _ NonUnitalModule.zero := by
  intro hM
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨e, he⟩ := hM m
  exact hm he.symm

/-- Commutation does not imply two-sided nondegeneracy: zero actions on a nonzero group. -/
theorem exists_actionsCommute_not_isNondegenerateBimodule [Nontrivial M] :
    ∃ (hA : NonUnitalModule A M) (hB : NonUnitalModule Bᵐᵒᵖ M),
      @ActionsCommute A B M _ _ _ hA hB ∧
        ¬ @IsNondegenerateBimodule A B M _ _ _ hA hB :=
  ⟨NonUnitalModule.zero, NonUnitalModule.zero,
    @actionsCommute_zero_left A B M _ _ _ NonUnitalModule.zero,
    fun h => not_isNondegenerate_zero h.1⟩

end Degenerate

section Hom

variable (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)
  [NonUnitalRing A] [NonUnitalRing B] [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule A M] [NonUnitalModule Bᵐᵒᵖ M]
  [NonUnitalModule A N] [NonUnitalModule Bᵐᵒᵖ N]

/-- The actual additive subgroup of maps intertwining both specified actions. -/
def bimoduleHomGroup : AddSubgroup (M →+ N) where
  carrier := {f | (∀ (a : A) (m : M), f (a • m) = a • f m) ∧
    ∀ (b : Bᵐᵒᵖ) (m : M), f (b • m) = b • f m}
  zero_mem' := ⟨fun a _ => (smul_zero a).symm, fun b _ => (smul_zero b).symm⟩
  add_mem' := by
    rintro f g ⟨hfA, hfB⟩ ⟨hgA, hgB⟩
    refine ⟨fun a m => ?_, fun b m => ?_⟩
    · change f (a • m) + g (a • m) = a • (f m + g m)
      rw [hfA, hgA, smul_add]
    · change f (b • m) + g (b • m) = b • (f m + g m)
      rw [hfB, hgB, smul_add]
  neg_mem' := by
    rintro f ⟨hfA, hfB⟩
    refine ⟨fun a m => ?_, fun b m => ?_⟩
    · change -f (a • m) = a • (-f m)
      rw [hfA, smul_neg]
    · change -f (b • m) = b • (-f m)
      rw [hfB, smul_neg]

theorem mem_bimoduleHomGroup (f : M →+ N) :
    f ∈ bimoduleHomGroup A B M N ↔
      (∀ (a : A) (m : M), f (a • m) = a • f m) ∧
        ∀ (b : Bᵐᵒᵖ) (m : M), f (b • m) = b • f m :=
  Iff.rfl

/-- Bimodule intertwiners, with the pointwise group inherited from `M →+ N`. -/
abbrev NonUnitalBimoduleHom := ↥(bimoduleHomGroup A B M N)

end Hom

namespace NonUnitalBimoduleHom

variable {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN} {P : Type uP}
  [NonUnitalRing A] [NonUnitalRing B] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule A M] [NonUnitalModule Bᵐᵒᵖ M]
  [NonUnitalModule A N] [NonUnitalModule Bᵐᵒᵖ N]
  [NonUnitalModule A P] [NonUnitalModule Bᵐᵒᵖ P]

instance : CoeFun (NonUnitalBimoduleHom A B M N) (fun _ => M → N) :=
  ⟨fun f => f.val⟩

@[ext] theorem ext {f g : NonUnitalBimoduleHom A B M N} (h : ∀ m, f m = g m) : f = g :=
  Subtype.ext (AddMonoidHom.ext h)

@[simp] theorem zero_apply (m : M) : (0 : NonUnitalBimoduleHom A B M N) m = 0 := rfl

@[simp] theorem add_apply (f g : NonUnitalBimoduleHom A B M N) (m : M) :
    (f + g) m = f m + g m := rfl

@[simp] theorem neg_apply (f : NonUnitalBimoduleHom A B M N) (m : M) :
    (-f) m = -f m := rfl

@[simp] theorem sub_apply (f g : NonUnitalBimoduleHom A B M N) (m : M) :
    (f - g) m = f m - g m := rfl

@[simp] theorem map_zero (f : NonUnitalBimoduleHom A B M N) : f 0 = 0 :=
  f.val.map_zero

@[simp] theorem map_add (f : NonUnitalBimoduleHom A B M N) (m n : M) :
    f (m + n) = f m + f n :=
  f.val.map_add m n

theorem map_smul_left (f : NonUnitalBimoduleHom A B M N) (a : A) (m : M) :
    f (a • m) = a • f m :=
  f.property.1 a m

theorem map_smul_right (f : NonUnitalBimoduleHom A B M N) (b : Bᵐᵒᵖ) (m : M) :
    f (b • m) = b • f m :=
  f.property.2 b m

/-- The right intertwining equation in right-action notation. -/
theorem map_op_smul (f : NonUnitalBimoduleHom A B M N) (b : B) (m : M) :
    f (op b • m) = op b • f m :=
  f.property.2 (op b) m

/-- An additive map intertwining both actions. -/
def mk' (f : M →+ N) (hA : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hB : ∀ (b : Bᵐᵒᵖ) (m : M), f (b • m) = b • f m) : NonUnitalBimoduleHom A B M N :=
  ⟨f, hA, hB⟩

@[simp] theorem mk'_val (f : M →+ N) (hA : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hB : ∀ (b : Bᵐᵒᵖ) (m : M), f (b • m) = b • f m) :
    (mk' f hA hB : NonUnitalBimoduleHom A B M N).val = f := rfl

/-- The inclusion into actual additive maps, as an additive homomorphism. -/
def toAddMonoidHom : NonUnitalBimoduleHom A B M N →+ (M →+ N) :=
  (bimoduleHomGroup A B M N).subtype

@[simp] theorem toAddMonoidHom_apply (f : NonUnitalBimoduleHom A B M N) :
    toAddMonoidHom f = f.val := rfl

variable (A B M) in
/-- Identity bimodule intertwiner. -/
def id : NonUnitalBimoduleHom A B M M :=
  ⟨AddMonoidHom.id M, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Composition of bimodule intertwiners. -/
def comp (g : NonUnitalBimoduleHom A B N P) (f : NonUnitalBimoduleHom A B M N) :
    NonUnitalBimoduleHom A B M P :=
  ⟨g.val.comp f.val, fun a m => by
      change g (f (a • m)) = a • g (f m)
      rw [map_smul_left, map_smul_left],
    fun b m => by
      change g (f (b • m)) = b • g (f m)
      rw [map_smul_right, map_smul_right]⟩

@[simp] theorem id_apply (m : M) : id A B M m = m := rfl

@[simp] theorem comp_apply (g : NonUnitalBimoduleHom A B N P)
    (f : NonUnitalBimoduleHom A B M N) (m : M) : comp g f m = g (f m) := rfl

theorem id_val : (id A B M).val = AddMonoidHom.id M := rfl

theorem comp_val (g : NonUnitalBimoduleHom A B N P) (f : NonUnitalBimoduleHom A B M N) :
    (comp g f).val = g.val.comp f.val := rfl

theorem id_comp (f : NonUnitalBimoduleHom A B M N) : comp (id A B N) f = f := rfl

theorem comp_id (f : NonUnitalBimoduleHom A B M N) : comp f (id A B M) = f := rfl

theorem comp_assoc {Q : Type*} [AddCommGroup Q] [NonUnitalModule A Q] [NonUnitalModule Bᵐᵒᵖ Q]
    (h : NonUnitalBimoduleHom A B P Q) (g : NonUnitalBimoduleHom A B N P)
    (f : NonUnitalBimoduleHom A B M N) : comp (comp h g) f = comp h (comp g f) := rfl

/-- Postcomposition distributes over sums. -/
theorem comp_add (g : NonUnitalBimoduleHom A B N P) (f f' : NonUnitalBimoduleHom A B M N) :
    g.comp (f + f') = g.comp f + g.comp f' := by
  ext m
  exact g.map_add (f m) (f' m)

/-- Precomposition distributes over sums. -/
theorem add_comp (g g' : NonUnitalBimoduleHom A B N P) (f : NonUnitalBimoduleHom A B M N) :
    (g + g').comp f = g.comp f + g'.comp f := by
  ext m
  rfl

/-- The underlying original left `A`-module Hom, with the whole additive map. -/
def toLeftHom (f : NonUnitalBimoduleHom A B M N) : NonUnitalModuleHom A M N where
  toAddMonoidHom := f.val
  map_smul' := f.property.1

/-- The underlying original right `B`-module Hom, with the whole additive map. -/
def toRightHom (f : NonUnitalBimoduleHom A B M N) : NonUnitalModuleHom Bᵐᵒᵖ M N where
  toAddMonoidHom := f.val
  map_smul' := f.property.2

@[simp] theorem toLeftHom_toAddMonoidHom (f : NonUnitalBimoduleHom A B M N) :
    f.toLeftHom.toAddMonoidHom = f.val := rfl

@[simp] theorem toRightHom_toAddMonoidHom (f : NonUnitalBimoduleHom A B M N) :
    f.toRightHom.toAddMonoidHom = f.val := rfl

@[simp] theorem toLeftHom_apply (f : NonUnitalBimoduleHom A B M N) (m : M) :
    f.toLeftHom m = f m := rfl

@[simp] theorem toRightHom_apply (f : NonUnitalBimoduleHom A B M N) (m : M) :
    f.toRightHom m = f m := rfl

theorem toLeftHom_injective :
    Function.Injective (toLeftHom : NonUnitalBimoduleHom A B M N → NonUnitalModuleHom A M N) :=
  fun _ _ h => ext fun m => congrArg (fun k : NonUnitalModuleHom A M N => k m) h

theorem toRightHom_injective :
    Function.Injective
      (toRightHom : NonUnitalBimoduleHom A B M N → NonUnitalModuleHom Bᵐᵒᵖ M N) :=
  fun _ _ h => ext fun m => congrArg (fun k : NonUnitalModuleHom Bᵐᵒᵖ M N => k m) h

/-- A pair of published original Homs with the same additive map is a bimodule Hom. -/
def ofHoms (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom Bᵐᵒᵖ M N)
    (h : f.toAddMonoidHom = g.toAddMonoidHom) : NonUnitalBimoduleHom A B M N :=
  ⟨f.toAddMonoidHom, f.map_smul', h ▸ g.map_smul'⟩

@[simp] theorem ofHoms_val (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom Bᵐᵒᵖ M N)
    (h : f.toAddMonoidHom = g.toAddMonoidHom) : (ofHoms f g h).val = f.toAddMonoidHom := rfl

theorem toLeftHom_ofHoms (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom Bᵐᵒᵖ M N)
    (h : f.toAddMonoidHom = g.toAddMonoidHom) : (ofHoms f g h).toLeftHom = f := rfl

theorem toRightHom_ofHoms (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom Bᵐᵒᵖ M N)
    (h : f.toAddMonoidHom = g.toAddMonoidHom) : (ofHoms f g h).toRightHom = g := by
  cases g
  cases h
  rfl

/-- The left projection is an additive homomorphism. -/
def toLeftHomAddHom : NonUnitalBimoduleHom A B M N →+ NonUnitalModuleHom A M N where
  toFun := toLeftHom
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The right projection is an additive homomorphism. -/
def toRightHomAddHom : NonUnitalBimoduleHom A B M N →+ NonUnitalModuleHom Bᵐᵒᵖ M N where
  toFun := toRightHom
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem toLeftHomAddHom_apply (f : NonUnitalBimoduleHom A B M N) :
    toLeftHomAddHom f = f.toLeftHom := rfl

@[simp] theorem toRightHomAddHom_apply (f : NonUnitalBimoduleHom A B M N) :
    toRightHomAddHom f = f.toRightHom := rfl

/-- The additive projections followed by forgetting the action are the inclusion. -/
theorem toAddMonoidHomAddHom_comp_toLeftHomAddHom :
    NonUnitalModuleHom.toAddMonoidHomAddHom.comp
        (toLeftHomAddHom : NonUnitalBimoduleHom A B M N →+ _) = toAddMonoidHom := rfl

theorem toAddMonoidHomAddHom_comp_toRightHomAddHom :
    NonUnitalModuleHom.toAddMonoidHomAddHom.comp
        (toRightHomAddHom : NonUnitalBimoduleHom A B M N →+ _) = toAddMonoidHom := rfl

@[simp] theorem toLeftHom_id : (id A B M).toLeftHom = NonUnitalModuleHom.id A M := rfl

@[simp] theorem toRightHom_id : (id A B M).toRightHom = NonUnitalModuleHom.id Bᵐᵒᵖ M := rfl

@[simp] theorem toLeftHom_comp (g : NonUnitalBimoduleHom A B N P)
    (f : NonUnitalBimoduleHom A B M N) :
    (comp g f).toLeftHom = g.toLeftHom.comp f.toLeftHom := rfl

@[simp] theorem toRightHom_comp (g : NonUnitalBimoduleHom A B N P)
    (f : NonUnitalBimoduleHom A B M N) :
    (comp g f).toRightHom = g.toRightHom.comp f.toRightHom := rfl

end NonUnitalBimoduleHom

namespace NonUnitalModule

/-- The specified right regular action `op b • m = m * b`; not a global instance. -/
abbrev rightRegular (A : Type uA) [NonUnitalRing A] : NonUnitalModule Aᵐᵒᵖ A where
  smul b m := m * b.unop
  smul_zero b := zero_mul b.unop
  smul_add b m n := add_mul m n b.unop
  mul_smul b c m := (mul_assoc m c.unop b.unop).symm
  add_smul b c m := mul_add m b.unop c.unop
  zero_smul m := mul_zero m

/-- The exact right-regular formula for the explicitly selected action. -/
theorem rightRegular_smul (A : Type uA) [NonUnitalRing A] (b m : A) :
    @HSMul.hSMul Aᵐᵒᵖ A A (@instHSMul Aᵐᵒᵖ A (@actionSMul Aᵐᵒᵖ A _ _ (rightRegular A)))
      (op b) m = m * b := rfl

/-- The exact published left-regular formula for the explicitly selected action. -/
theorem regular_smul (A : Type uA) [NonUnitalRing A] (a m : A) :
    @HSMul.hSMul A A A (@instHSMul A A (@actionSMul A A _ _ (regular A))) a m = a * m := rfl

/-- The published left-regular and the right-regular actions commute (associativity). -/
theorem regular_actionsCommute (A : Type uA) [NonUnitalRing A] :
    @ActionsCommute A A A _ _ _ (regular A) (rightRegular A) :=
  fun a b m => (mul_assoc a m b).symm

end NonUnitalModule

/-- Actual commuting bimodules; one carrier universe, independent of both ring universes. -/
structure NonUnitalBimoduleCat (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    where
  carrier : Type uM
  [isAddCommGroup : AddCommGroup carrier]
  [isLeftModule : NonUnitalModule A carrier]
  [isRightModule : NonUnitalModule Bᵐᵒᵖ carrier]
  actionsCommute : ActionsCommute A B carrier

attribute [instance] NonUnitalBimoduleCat.isAddCommGroup NonUnitalBimoduleCat.isLeftModule
  NonUnitalBimoduleCat.isRightModule

namespace NonUnitalBimoduleCat

variable (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]

instance : CoeSort (NonUnitalBimoduleCat.{uA, uB, uM} A B) (Type uM) :=
  ⟨NonUnitalBimoduleCat.carrier⟩

/-- Bundle two specified commuting actions. -/
abbrev of (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] [NonUnitalModule Bᵐᵒᵖ M]
    (h : ActionsCommute A B M) : NonUnitalBimoduleCat.{uA, uB, uM} A B :=
  ⟨M, h⟩

/-- The regular bimodule: the published left-regular and the right-regular actions. -/
abbrev regular (A : Type uA) [NonUnitalRing A] : NonUnitalBimoduleCat.{uA, uA, uA} A A :=
  @of A A _ _ A _ (NonUnitalModule.regular A) (NonUnitalModule.rightRegular A)
    (NonUnitalModule.regular_actionsCommute A)

variable {A B}

instance smulCommClass (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    SMulCommClass A Bᵐᵒᵖ M :=
  M.actionsCommute.smulCommClass

instance smulCommClass' (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    SMulCommClass Bᵐᵒᵖ A M :=
  M.actionsCommute.smulCommClass'

variable (A B)

instance category : Category (NonUnitalBimoduleCat.{uA, uB, uM} A B) where
  Hom M N := NonUnitalBimoduleHom A B M N
  id M := NonUnitalBimoduleHom.id A B M
  comp f g := NonUnitalBimoduleHom.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem hom_def (M N : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    (M ⟶ N) = NonUnitalBimoduleHom A B M N := rfl

theorem id_def (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    𝟙 M = NonUnitalBimoduleHom.id A B M := rfl

theorem comp_def {M N P : NonUnitalBimoduleCat.{uA, uB, uM} A B} (f : M ⟶ N) (g : N ⟶ P) :
    f ≫ g = NonUnitalBimoduleHom.comp g f := rfl

/-- The preadditive structure inherited from the intertwiner subgroup. -/
instance preadditive : Preadditive (NonUnitalBimoduleCat.{uA, uB, uM} A B) where
  homGroup M N := inferInstanceAs (AddCommGroup (NonUnitalBimoduleHom A B M N))
  add_comp _ _ _ f f' g := NonUnitalBimoduleHom.comp_add g f f'
  comp_add _ _ _ f g g' := NonUnitalBimoduleHom.add_comp g g' f

/-- The category's Hom group is definitionally the inherited subgroup group. -/
theorem homGroup_eq (M N : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    (preadditive A B).homGroup M N = (bimoduleHomGroup A B M N).toAddCommGroup := rfl

/-- Forgetting the right action: the original left `A`-module. -/
def forgetToLeft : NonUnitalBimoduleCat.{uA, uB, uM} A B ⥤ NonUnitalModuleCat.{uA, uM} A where
  obj M := NonUnitalModuleCat.of A M
  map f := NonUnitalBimoduleHom.toLeftHom f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the left action: the original right `B`-module. -/
def forgetToRight :
    NonUnitalBimoduleCat.{uA, uB, uM} A B ⥤ RightNonUnitalModuleCat.{uB, uM} B where
  obj M := NonUnitalModuleCat.of Bᵐᵒᵖ M
  map f := NonUnitalBimoduleHom.toRightHom f
  map_id _ := rfl
  map_comp _ _ := rfl

variable {A B}

@[simp] theorem forgetToLeft_obj (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    (forgetToLeft A B).obj M = NonUnitalModuleCat.of A M := rfl

@[simp] theorem forgetToRight_obj (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    (forgetToRight A B).obj M = NonUnitalModuleCat.of Bᵐᵒᵖ M := rfl

theorem forgetToLeft_obj_carrier (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    ((forgetToLeft A B).obj M).carrier = M.carrier := rfl

theorem forgetToRight_obj_carrier (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    ((forgetToRight A B).obj M).carrier = M.carrier := rfl

/-- The image keeps the specified additive group. -/
theorem forgetToLeft_obj_isAddCommGroup (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    ((forgetToLeft A B).obj M).isAddCommGroup = M.isAddCommGroup := rfl

theorem forgetToRight_obj_isAddCommGroup (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    ((forgetToRight A B).obj M).isAddCommGroup = M.isAddCommGroup := rfl

/-- The image carries exactly the specified left action. -/
theorem forgetToLeft_obj_isModule (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    ((forgetToLeft A B).obj M).isModule = M.isLeftModule := rfl

/-- The image carries exactly the specified right action. -/
theorem forgetToRight_obj_isModule (M : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    ((forgetToRight A B).obj M).isModule = M.isRightModule := rfl

theorem forgetToLeft_map {M N : NonUnitalBimoduleCat.{uA, uB, uM} A B} (f : M ⟶ N) :
    (forgetToLeft A B).map f = NonUnitalBimoduleHom.toLeftHom f := rfl

theorem forgetToRight_map {M N : NonUnitalBimoduleCat.{uA, uB, uM} A B} (f : M ⟶ N) :
    (forgetToRight A B).map f = NonUnitalBimoduleHom.toRightHom f := rfl

/-- The image of a morphism has the whole original additive map. -/
theorem forgetToLeft_map_toAddMonoidHom {M N : NonUnitalBimoduleCat.{uA, uB, uM} A B}
    (f : NonUnitalBimoduleHom A B M N) :
    NonUnitalModuleHom.toAddMonoidHom ((forgetToLeft A B).map f) = f.val := rfl

theorem forgetToRight_map_toAddMonoidHom {M N : NonUnitalBimoduleCat.{uA, uB, uM} A B}
    (f : NonUnitalBimoduleHom A B M N) :
    NonUnitalModuleHom.toAddMonoidHom ((forgetToRight A B).map f) = f.val := rfl

variable (A B)

instance forgetToLeft_additive : (forgetToLeft.{uA, uB, uM} A B).Additive where
  map_add := rfl

instance forgetToRight_additive : (forgetToRight.{uA, uB, uM} A B).Additive where
  map_add := rfl

instance forgetToLeft_faithful : (forgetToLeft.{uA, uB, uM} A B).Faithful where
  map_injective h := NonUnitalBimoduleHom.toLeftHom_injective h

instance forgetToRight_faithful : (forgetToRight.{uA, uB, uM} A B).Faithful where
  map_injective h := NonUnitalBimoduleHom.toRightHom_injective h

variable {A B}

/-- On Hom groups the left forgetful functor is the additive left projection. -/
theorem forgetToLeft_mapAddHom (M N : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    (forgetToLeft A B).mapAddHom (X := M) (Y := N) =
      NonUnitalBimoduleHom.toLeftHomAddHom := rfl

/-- On Hom groups the right forgetful functor is the additive right projection. -/
theorem forgetToRight_mapAddHom (M N : NonUnitalBimoduleCat.{uA, uB, uM} A B) :
    (forgetToRight A B).mapAddHom (X := M) (Y := N) =
      NonUnitalBimoduleHom.toRightHomAddHom := rfl

end NonUnitalBimoduleCat

/-! Complete unapplied interfaces at independent ring and carrier universes. -/

section Interfaces

example : (A : Type uA) → (B : Type uB) → (M : Type uM) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] → Prop :=
  ActionsCommute.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → (M : Type uM) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] → Prop :=
  IsNondegenerateBimodule.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → (M : Type uM) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    (ActionsCommute A B M ↔ SMulCommClass A Bᵐᵒᵖ M) :=
  actionsCommute_iff_smulCommClass.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → (M : Type uM) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    (ActionsCommute A B M ↔ SMulCommClass Bᵐᵒᵖ A M) :=
  actionsCommute_iff_smulCommClass'.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} → {M : Type uM} →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] → ActionsCommute A B M →
    A → NonUnitalModuleHom Bᵐᵒᵖ M M :=
  @ActionsCommute.leftActionHom.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} → {M : Type uM} →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] → ActionsCommute A B M →
    Bᵐᵒᵖ → NonUnitalModuleHom A M M :=
  @ActionsCommute.rightActionHom.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} → {M : Type uM} →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] → ActionsCommute A B M →
    A →+ NonUnitalModuleHom Bᵐᵒᵖ M M :=
  @ActionsCommute.leftActionAddHom.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} → {M : Type uM} →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] → ActionsCommute A B M →
    Bᵐᵒᵖ →+ NonUnitalModuleHom A M M :=
  @ActionsCommute.rightActionAddHom.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → (M : Type uM) → (N : Type uN) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    [NonUnitalModule A N] → [NonUnitalModule Bᵐᵒᵖ N] → AddSubgroup (M →+ N) :=
  bimoduleHomGroup.{uA, uB, uM, uN}

example : (A : Type uA) → (B : Type uB) → (M : Type uM) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] → NonUnitalBimoduleHom A B M M :=
  NonUnitalBimoduleHom.id.{uA, uB, uM}

example : {A : Type uA} → {B : Type uB} → {M : Type uM} → {N : Type uN} → {P : Type uP} →
    [NonUnitalRing A] → [NonUnitalRing B] →
    [AddCommGroup M] → [AddCommGroup N] → [AddCommGroup P] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    [NonUnitalModule A N] → [NonUnitalModule Bᵐᵒᵖ N] →
    [NonUnitalModule A P] → [NonUnitalModule Bᵐᵒᵖ P] →
    NonUnitalBimoduleHom A B N P → NonUnitalBimoduleHom A B M N →
      NonUnitalBimoduleHom A B M P :=
  @NonUnitalBimoduleHom.comp.{uA, uB, uM, uN, uP}

example : {A : Type uA} → {B : Type uB} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    [NonUnitalModule A N] → [NonUnitalModule Bᵐᵒᵖ N] →
    NonUnitalBimoduleHom A B M N →+ NonUnitalModuleHom A M N :=
  @NonUnitalBimoduleHom.toLeftHomAddHom.{uA, uB, uM, uN}

example : {A : Type uA} → {B : Type uB} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    [NonUnitalModule A N] → [NonUnitalModule Bᵐᵒᵖ N] →
    NonUnitalBimoduleHom A B M N →+ NonUnitalModuleHom Bᵐᵒᵖ M N :=
  @NonUnitalBimoduleHom.toRightHomAddHom.{uA, uB, uM, uN}

example : (A : Type uA) → [NonUnitalRing A] → NonUnitalModule Aᵐᵒᵖ A :=
  NonUnitalModule.rightRegular.{uA}

example : (A : Type uA) → (B : Type uB) → [NonUnitalRing A] → [NonUnitalRing B] →
    Preadditive (NonUnitalBimoduleCat.{uA, uB, uM} A B) :=
  NonUnitalBimoduleCat.preadditive.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → [NonUnitalRing A] → [NonUnitalRing B] →
    NonUnitalBimoduleCat.{uA, uB, uM} A B ⥤ NonUnitalModuleCat.{uA, uM} A :=
  NonUnitalBimoduleCat.forgetToLeft.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → [NonUnitalRing A] → [NonUnitalRing B] →
    NonUnitalBimoduleCat.{uA, uB, uM} A B ⥤ RightNonUnitalModuleCat.{uB, uM} B :=
  NonUnitalBimoduleCat.forgetToRight.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → [NonUnitalRing A] → [NonUnitalRing B] →
    (NonUnitalBimoduleCat.forgetToLeft.{uA, uB, uM} A B).Additive :=
  NonUnitalBimoduleCat.forgetToLeft_additive.{uA, uB, uM}

example : (A : Type uA) → (B : Type uB) → [NonUnitalRing A] → [NonUnitalRing B] →
    (NonUnitalBimoduleCat.forgetToRight.{uA, uB, uM} A B).Additive :=
  NonUnitalBimoduleCat.forgetToRight_additive.{uA, uB, uM}

example (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B] :
    Preadditive (NonUnitalBimoduleCat.{uA, uB, uM} A B) := inferInstance

example (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B] :
    (NonUnitalBimoduleCat.forgetToLeft.{uA, uB, uM} A B).Additive := inferInstance

example (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B] :
    (NonUnitalBimoduleCat.forgetToRight.{uA, uB, uM} A B).Additive := inferInstance

/-! Both unequal ring/carrier directions, with the two rings also of different sizes. -/

example : (A : Type) → (B : Type) → [NonUnitalRing A] → [NonUnitalRing B] →
    Preadditive (NonUnitalBimoduleCat.{0, 0, 1} A B) :=
  NonUnitalBimoduleCat.preadditive.{0, 0, 1}

example : (A : Type 1) → (B : Type 1) → [NonUnitalRing A] → [NonUnitalRing B] →
    Preadditive (NonUnitalBimoduleCat.{1, 1, 0} A B) :=
  NonUnitalBimoduleCat.preadditive.{1, 1, 0}

example : (A : Type) → (B : Type 1) → [NonUnitalRing A] → [NonUnitalRing B] →
    Preadditive (NonUnitalBimoduleCat.{0, 1, 0} A B) :=
  NonUnitalBimoduleCat.preadditive.{0, 1, 0}

example : (A : Type 1) → (B : Type) → [NonUnitalRing A] → [NonUnitalRing B] →
    Preadditive (NonUnitalBimoduleCat.{1, 0, 1} A B) :=
  NonUnitalBimoduleCat.preadditive.{1, 0, 1}

example : (A : Type) → (B : Type 1) → [NonUnitalRing A] → [NonUnitalRing B] →
    (NonUnitalBimoduleCat.forgetToLeft.{0, 1, 0} A B).Additive :=
  NonUnitalBimoduleCat.forgetToLeft_additive.{0, 1, 0}

example : (A : Type 1) → (B : Type) → [NonUnitalRing A] → [NonUnitalRing B] →
    (NonUnitalBimoduleCat.forgetToLeft.{1, 0, 1} A B).Additive :=
  NonUnitalBimoduleCat.forgetToLeft_additive.{1, 0, 1}

example : (A : Type) → (B : Type 1) → [NonUnitalRing A] → [NonUnitalRing B] →
    (NonUnitalBimoduleCat.forgetToRight.{0, 1, 0} A B).Additive :=
  NonUnitalBimoduleCat.forgetToRight_additive.{0, 1, 0}

example : (A : Type 1) → (B : Type) → [NonUnitalRing A] → [NonUnitalRing B] →
    (NonUnitalBimoduleCat.forgetToRight.{1, 0, 1} A B).Additive :=
  NonUnitalBimoduleCat.forgetToRight_additive.{1, 0, 1}

/-- Source and target carriers of intertwiners in different universes, both directions. -/
example : (A : Type) → (B : Type 1) → (M : Type) → (N : Type 1) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    [NonUnitalModule A N] → [NonUnitalModule Bᵐᵒᵖ N] → AddSubgroup (M →+ N) :=
  bimoduleHomGroup.{0, 1, 0, 1}

example : (A : Type 1) → (B : Type) → (M : Type 1) → (N : Type) →
    [NonUnitalRing A] → [NonUnitalRing B] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule Bᵐᵒᵖ M] →
    [NonUnitalModule A N] → [NonUnitalModule Bᵐᵒᵖ N] → AddSubgroup (M →+ N) :=
  bimoduleHomGroup.{1, 0, 1, 0}

/-! Competing actions and additive structures on identical carriers, including `A = B = M`. -/

/-- The regular bimodule keeps the published left-regular action. -/
example (A : Type uA) [NonUnitalRing A] :
    ((NonUnitalBimoduleCat.forgetToLeft A A).obj (NonUnitalBimoduleCat.regular A)).isModule =
      NonUnitalModule.regular A := rfl

/-- The regular bimodule keeps the right-regular action. -/
example (A : Type uA) [NonUnitalRing A] :
    ((NonUnitalBimoduleCat.forgetToRight A A).obj (NonUnitalBimoduleCat.regular A)).isModule =
      NonUnitalModule.rightRegular A := rfl

/-- Its selected right action is `op b • m = m * b`. -/
example (A : Type uA) [NonUnitalRing A] (b m : A) :
    @HSMul.hSMul Aᵐᵒᵖ A A (@instHSMul Aᵐᵒᵖ A (@NonUnitalModule.actionSMul Aᵐᵒᵖ A _ _
      (NonUnitalBimoduleCat.regular A).isRightModule)) (op b) m = m * b := rfl

/-- On `A = B = M` the zero actions give a competing bimodule on the same carrier. -/
example (A : Type uA) [NonUnitalRing A] :
    ((NonUnitalBimoduleCat.forgetToLeft A A).obj
      (@NonUnitalBimoduleCat.of A A _ _ A _ NonUnitalModule.zero NonUnitalModule.zero
        (@actionsCommute_zero_left A A A _ _ _ NonUnitalModule.zero))).isModule =
      NonUnitalModule.zero := rfl

/-- Mixed selection on `A = B = M`: the left-regular action with the zero right action. -/
example (A : Type uA) [NonUnitalRing A] :
    ((NonUnitalBimoduleCat.forgetToRight A A).obj
      (@NonUnitalBimoduleCat.of A A _ _ A _ (NonUnitalModule.regular A) NonUnitalModule.zero
        (@actionsCommute_zero_right A A A _ _ _ (NonUnitalModule.regular A)))).isModule =
      NonUnitalModule.zero := rfl

/-- Mixed selection on `A = B = M`: the zero left action with the right-regular action. -/
example (A : Type uA) [NonUnitalRing A] :
    ((NonUnitalBimoduleCat.forgetToLeft A A).obj
      (@NonUnitalBimoduleCat.of A A _ _ A _ NonUnitalModule.zero (NonUnitalModule.rightRegular A)
        (@actionsCommute_zero_left A A A _ _ _ (NonUnitalModule.rightRegular A)))).isModule =
      NonUnitalModule.zero := rfl

/-- An arbitrary additive group on the carrier `A`, unrelated to the ring addition, is kept. -/
example (A : Type uA) [NonUnitalRing A] (G : AddCommGroup A) :
    ((NonUnitalBimoduleCat.forgetToLeft A A).obj
      (@NonUnitalBimoduleCat.of A A _ _ A G NonUnitalModule.zero NonUnitalModule.zero
        (@actionsCommute_zero_left A A A _ _ G NonUnitalModule.zero))).isAddCommGroup = G := rfl

/-- The same for the right forgetful functor and arbitrary rings. -/
example (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B] (M : Type uM)
    (G : AddCommGroup M) :
    ((NonUnitalBimoduleCat.forgetToRight A B).obj
      (@NonUnitalBimoduleCat.of A B _ _ M G NonUnitalModule.zero NonUnitalModule.zero
        (@actionsCommute_zero_left A B M _ _ G NonUnitalModule.zero))).isAddCommGroup = G := rfl

/-- Intertwiners for an explicitly selected additive group and actions. -/
example (A : Type uA) [NonUnitalRing A] (G : AddCommGroup A) :=
  @bimoduleHomGroup A A A A _ _ G G NonUnitalModule.zero NonUnitalModule.zero
    NonUnitalModule.zero NonUnitalModule.zero

/-! Zero actions on nonzero groups, zero rings and trivial carriers. -/

/-- Zero actions on `ℤ` commute but are degenerate, over arbitrary rings. -/
example (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B] :
    ∃ (hA : NonUnitalModule A ℤ) (hB : NonUnitalModule Bᵐᵒᵖ ℤ),
      @ActionsCommute A B ℤ _ _ _ hA hB ∧ ¬ @IsNondegenerateBimodule A B ℤ _ _ _ hA hB :=
  exists_actionsCommute_not_isNondegenerateBimodule

/-- Zero actions of the unital ring `ℤ` on `ℤ` form a bimodule; no unit law is imposed. -/
example : NonUnitalBimoduleCat.{0, 0, 0} ℤ ℤ :=
  @NonUnitalBimoduleCat.of ℤ ℤ _ _ ℤ _ NonUnitalModule.zero NonUnitalModule.zero
    (@actionsCommute_zero_left ℤ ℤ ℤ _ _ _ NonUnitalModule.zero)

/-- Zero rings, at arbitrary universes. -/
example : Preadditive (NonUnitalBimoduleCat.{uA, uB, uM} PUnit.{uA + 1} PUnit.{uB + 1}) :=
  inferInstance

/-- A bimodule over zero rings on the nonzero group `ℤ`. -/
example : NonUnitalBimoduleCat.{uA, uB, 0} PUnit.{uA + 1} PUnit.{uB + 1} :=
  @NonUnitalBimoduleCat.of PUnit PUnit _ _ ℤ _ NonUnitalModule.zero NonUnitalModule.zero
    (@actionsCommute_zero_left PUnit PUnit ℤ _ _ _ NonUnitalModule.zero)

/-- A trivial carrier: any two actions commute and are nondegenerate. -/
example (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    (hA : NonUnitalModule A PUnit.{uM + 1}) (hB : NonUnitalModule Bᵐᵒᵖ PUnit.{uM + 1}) :
    @ActionsCommute A B PUnit _ _ _ hA hB ∧ @IsNondegenerateBimodule A B PUnit _ _ _ hA hB :=
  ⟨actionsCommute_of_subsingleton, isNondegenerateBimodule_of_subsingleton⟩

example (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B] :
    NonUnitalBimoduleCat.{uA, uB, uM} A B :=
  @NonUnitalBimoduleCat.of A B _ _ PUnit _ NonUnitalModule.zero NonUnitalModule.zero
    (@actionsCommute_of_subsingleton A B PUnit _ _ _ _ NonUnitalModule.zero NonUnitalModule.zero)

end Interfaces

end Langlands.Algebra
