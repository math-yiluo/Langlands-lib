import Langlands.Algebra.IntegerUnitizationCategory
import Langlands.Algebra.IntegerNonUnitalSubmodule
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Categorical subobjects of additive nonunital modules

Derived implementation content for Renard's module conventions, printed pp. 5–6, and the
subobjects of A.I.2, printed p. 248. The original action is kept and has no unit law.

`subobjectOrderIso M` identifies `Subobject M` with the stable additive subgroups of `M`. It
transports subobjects along the published integer-unitization equivalence, applies Mathlib's
`ModuleCat.subobjectModule`, and returns through `NonUnitalSubmodule.intUnitizedOrderIso`.
A monomorphism class goes to the range, and a submodule to the class of `S.subtype`.
`evenZeroSubmodule` checks this on the even integers with the zero action.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Algebra.NonUnitalModuleCat

universe u v

variable {A : Type u} [NonUnitalRing A]

section Mono

variable {M N : NonUnitalModuleCat.{u, v} A}

/-- Monomorphisms of the existing category are exactly the injective additive intertwiners. -/
theorem mono_iff_injective (f : M ⟶ N) :
    Mono f ↔ Function.Injective (NonUnitalModuleHom.toAddMonoidHom (A := A) (M := M) (N := N) f) := by
  constructor
  · intro hf
    have h : Mono ((IntegerUnitization.equivalence A).functor.map f) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 h
  · intro hf
    exact ⟨fun g h w => NonUnitalModuleHom.ext fun x =>
      hf (congrArg (fun k => NonUnitalModuleHom.toAddMonoidHom k x) w)⟩

end Mono

section Subobject

variable {M : NonUnitalModuleCat.{u, v} A}

/-- The existing subtype inclusion, as a morphism from the bundled submodule. -/
def subtypeHom (S : NonUnitalSubmodule A M) : NonUnitalModuleCat.of A S ⟶ M := S.subtype

theorem subtypeHom_eq_subtype (S : NonUnitalSubmodule A M) :
    subtypeHom S = (S.subtype : NonUnitalModuleCat.of A S ⟶ M) := rfl

@[simp] theorem subtypeHom_apply (S : NonUnitalSubmodule A M) (x : S) :
    NonUnitalModuleHom.toAddMonoidHom (A := A) (M := S) (N := M) (subtypeHom S) x = x := rfl

/-- The existing subtype inclusion is a monomorphism between the bundled modules. -/
theorem mono_subtype (S : NonUnitalSubmodule A M) :
    Mono (X := NonUnitalModuleCat.of A S) (Y := M) S.subtype :=
  (mono_iff_injective _).2 fun _ _ h => Subtype.ext h

instance mono_subtypeHom (S : NonUnitalSubmodule A M) : Mono (subtypeHom S) :=
  mono_subtype S

variable (M) in
/-- Categorical subobjects are the stable additive subgroups for the stored action. -/
noncomputable def subobjectOrderIso : Subobject M ≃o NonUnitalSubmodule A M :=
  ((Subobject.lowerEquivalence
      (MonoOver.congr M (IntegerUnitization.equivalence A))).toOrderIso.trans
    (ModuleCat.subobjectModule (IntegerUnitization.extendObj A M))).trans
    (NonUnitalSubmodule.intUnitizedOrderIso (A := A) (M := M)).symm

/-- The transported class of a monomorphism is the class of its extension. -/
theorem lowerEquivalence_congr_mk {N : NonUnitalModuleCat.{u, v} A} (f : N ⟶ M) [Mono f] :
    (Subobject.lowerEquivalence
      (MonoOver.congr M (IntegerUnitization.equivalence A))).functor.obj (Subobject.mk f) =
      Subobject.mk ((IntegerUnitization.equivalence A).functor.map f) := rfl

/-- The construction is the Mathlib module correspondence after transport. -/
theorem subobjectOrderIso_apply (P : Subobject M) :
    subobjectOrderIso M P = (NonUnitalSubmodule.intUnitizedOrderIso (A := A) (M := M)).symm
      (ModuleCat.subobjectModule (IntegerUnitization.extendObj A M)
        ((Subobject.lowerEquivalence
          (MonoOver.congr M (IntegerUnitization.equivalence A))).functor.obj P)) := rfl

/-- Membership in the image of a monomorphism class is membership in its range. -/
theorem mem_subobjectOrderIso_mk {N : NonUnitalModuleCat.{u, v} A} (f : N ⟶ M) [Mono f]
    (m : M) :
    m ∈ subobjectOrderIso M (Subobject.mk f) ↔
      ∃ n : N, NonUnitalModuleHom.toAddMonoidHom (A := A) (M := N) (N := M) f n = m := by
  let g := (IntegerUnitization.equivalence A).functor.map f
  have key : ∀ y : (IntegerUnitization.equivalence A).functor.obj M,
      y ∈ LinearMap.range (Subobject.mk g).arrow.hom ↔
        ∃ n : N, NonUnitalModuleHom.toAddMonoidHom (A := A) (M := N) (N := M) f n = y := by
    intro y
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Subobject.underlyingIso g).hom x,
        congrArg (fun k => k.hom x) (Subobject.underlyingIso_hom_comp_eq_mk g)⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(Subobject.underlyingIso g).inv n,
        congrArg (fun k => k.hom n) (Subobject.underlyingIso_arrow g)⟩
  exact key m

/-- The image of a monomorphism class has the range of the monomorphism as carrier. -/
theorem coe_subobjectOrderIso_mk {N : NonUnitalModuleCat.{u, v} A} (f : N ⟶ M) [Mono f] :
    (subobjectOrderIso M (Subobject.mk f) : Set M) =
      Set.range (NonUnitalModuleHom.toAddMonoidHom (A := A) (M := N) (N := M) f) :=
  Set.ext fun m => mem_subobjectOrderIso_mk f m

/-- Membership in the image of an arbitrary subobject is membership in the range of its arrow. -/
theorem mem_subobjectOrderIso (P : Subobject M) (m : M) :
    m ∈ subobjectOrderIso M P ↔
      ∃ n : (P : NonUnitalModuleCat.{u, v} A),
        NonUnitalModuleHom.toAddMonoidHom (A := A) (M := (P : NonUnitalModuleCat.{u, v} A))
          (N := M) P.arrow n = m := by
  conv_lhs => rw [← Subobject.mk_arrow P]
  exact mem_subobjectOrderIso_mk P.arrow m

/-- The class of the subtype inclusion is sent back to the submodule. -/
@[simp] theorem subobjectOrderIso_mk_subtypeHom (S : NonUnitalSubmodule A M) :
    subobjectOrderIso M (Subobject.mk (subtypeHom S)) = S :=
  SetLike.ext fun m => (mem_subobjectOrderIso_mk (subtypeHom S) m).trans
    ⟨fun ⟨n, hn⟩ => hn ▸ n.property, fun hm => ⟨⟨m, hm⟩, rfl⟩⟩

/-- The inverse sends a submodule to the class of its subtype inclusion. -/
@[simp] theorem subobjectOrderIso_symm_apply (S : NonUnitalSubmodule A M) :
    (subobjectOrderIso M).symm S = Subobject.mk (subtypeHom S) :=
  (subobjectOrderIso M).symm_apply_eq.2 (subobjectOrderIso_mk_subtypeHom S).symm

/-- Every subobject is the class of the subtype inclusion of its image. -/
@[simp] theorem mk_subtypeHom_subobjectOrderIso (P : Subobject M) :
    Subobject.mk (subtypeHom (subobjectOrderIso M P)) = P := by
  rw [← subobjectOrderIso_symm_apply, OrderIso.symm_apply_apply]

/-- Subtype inclusion classes are ordered by inclusion of submodules. -/
theorem mk_subtypeHom_le_mk_subtypeHom_iff {S T : NonUnitalSubmodule A M} :
    Subobject.mk (subtypeHom S) ≤ Subobject.mk (subtypeHom T) ↔ S ≤ T := by
  rw [← subobjectOrderIso_symm_apply, ← subobjectOrderIso_symm_apply,
    OrderIso.le_iff_le]

/-- The image order is the factorization order of subobjects. -/
theorem subobjectOrderIso_le_iff {P Q : Subobject M} :
    subobjectOrderIso M P ≤ subobjectOrderIso M Q ↔ P ≤ Q :=
  (subobjectOrderIso M).le_iff_le

/-- Factorization between monomorphism classes is inclusion of their ranges. -/
theorem subobject_mk_le_mk_iff {N₁ N₂ : NonUnitalModuleCat.{u, v} A}
    (f₁ : N₁ ⟶ M) (f₂ : N₂ ⟶ M) [Mono f₁] [Mono f₂] :
    Subobject.mk f₁ ≤ Subobject.mk f₂ ↔
      Set.range (NonUnitalModuleHom.toAddMonoidHom (A := A) (M := N₁) (N := M) f₁) ⊆
        Set.range (NonUnitalModuleHom.toAddMonoidHom (A := A) (M := N₂) (N := M) f₂) := by
  rw [← subobjectOrderIso_le_iff, ← SetLike.coe_subset_coe, coe_subobjectOrderIso_mk,
    coe_subobjectOrderIso_mk]

end Subobject

/-! The full unapplied types, with independent ring universe `u` and carrier universe `v`. -/

example : (A : Type u) → [NonUnitalRing A] → {M N : NonUnitalModuleCat.{u, v} A} →
    (f : M ⟶ N) →
      (Mono f ↔ Function.Injective
        (NonUnitalModuleHom.toAddMonoidHom (A := A) (M := M) (N := N) f)) :=
  @mono_iff_injective.{u, v}

example : (A : Type u) → [NonUnitalRing A] → {M : NonUnitalModuleCat.{u, v} A} →
    (S : NonUnitalSubmodule A M) → (NonUnitalModuleCat.of A S ⟶ M) := @subtypeHom.{u, v}

noncomputable example : (A : Type u) → [NonUnitalRing A] → (M : NonUnitalModuleCat.{u, v} A) →
    Subobject M ≃o NonUnitalSubmodule A M := @subobjectOrderIso.{u, v}

/-- The right-hand side uses exactly the stored additive group and stored action of `M`. -/
noncomputable example : (A : Type u) → [NonUnitalRing A] → (M : NonUnitalModuleCat.{u, v} A) →
    Subobject M ≃o
      @NonUnitalSubmodule A M _ M.isAddCommGroup M.isModule := @subobjectOrderIso.{u, v}

noncomputable example : (A : Type) → [NonUnitalRing A] → (M : NonUnitalModuleCat.{0, 1} A) →
    Subobject M ≃o NonUnitalSubmodule A M := @subobjectOrderIso.{0, 1}

noncomputable example : (A : Type 1) → [NonUnitalRing A] → (M : NonUnitalModuleCat.{1, 0} A) →
    Subobject M ≃o NonUnitalSubmodule A M := @subobjectOrderIso.{1, 0}

example : (A : Type u) → [NonUnitalRing A] → {M N : NonUnitalModuleCat.{u, v} A} →
    (f : N ⟶ M) → [Mono f] → (m : M) →
      (m ∈ subobjectOrderIso M (Subobject.mk f) ↔
        ∃ n : N, NonUnitalModuleHom.toAddMonoidHom (A := A) (M := N) (N := M) f n = m) :=
  @mem_subobjectOrderIso_mk.{u, v}

example : (A : Type u) → [NonUnitalRing A] → {M : NonUnitalModuleCat.{u, v} A} →
    (S : NonUnitalSubmodule A M) →
      (subobjectOrderIso M).symm S = Subobject.mk (subtypeHom S) :=
  @subobjectOrderIso_symm_apply.{u, v}

section ZeroAction

open IntegerUnitization

/-- The even integers, stable for the zero original action of the integers on themselves. -/
def evenZeroSubmodule :
    @NonUnitalSubmodule ℤ zeroIntObj _ zeroIntObj.isAddCommGroup zeroIntObj.isModule :=
  @NonUnitalSubmodule.mk ℤ zeroIntObj _ zeroIntObj.isAddCommGroup zeroIntObj.isModule
    (AddSubgroup.even ℤ) fun _ _ _ => Even.zero

@[simp] theorem mem_evenZeroSubmodule {m : zeroIntObj} :
    m ∈ evenZeroSubmodule ↔ Even m := Iff.rfl

theorem two_mem_evenZeroSubmodule : (2 : zeroIntObj) ∈ evenZeroSubmodule := even_two

/-- The even subgroup gives a proper categorical subobject of the zero-action module. -/
theorem mk_subtypeHom_evenZeroSubmodule_ne_top :
    Subobject.mk (subtypeHom (M := zeroIntObj) evenZeroSubmodule) ≠ ⊤ := by
  intro h
  have h1 : (1 : zeroIntObj) ∈ subobjectOrderIso zeroIntObj (Subobject.mk (𝟙 zeroIntObj)) :=
    (mem_subobjectOrderIso_mk _ _).2 ⟨1, rfl⟩
  rw [← Subobject.top_eq_id, ← h, subobjectOrderIso_mk_subtypeHom, mem_evenZeroSubmodule] at h1
  exact Int.not_even_one h1

/-- The original unit of the integers still acts by zero on the even subobject. -/
theorem evenZeroSubmodule_one_smul (x : evenZeroSubmodule) :
    (NonUnitalModuleCat.of ℤ evenZeroSubmodule).isModule.smul 1 x = 0 := rfl

/-- After integer unitization, the old unit still acts by zero. -/
theorem extend_evenZeroSubmodule_inr_one_smul (x : evenZeroSubmodule) :
    (extendObj ℤ (NonUnitalModuleCat.of ℤ evenZeroSubmodule)).isModule.smul
      (Unitization.inr (1 : ℤ)) x = 0 :=
  extendObj_inr_smul ℤ (NonUnitalModuleCat.of ℤ evenZeroSubmodule) 1 x

/-- After integer unitization, the new unit acts identically. -/
theorem extend_evenZeroSubmodule_one_smul (x : evenZeroSubmodule) :
    (extendObj ℤ (NonUnitalModuleCat.of ℤ evenZeroSubmodule)).isModule.smul
      (1 : Unitization ℤ ℤ) x = x :=
  (extendObj ℤ (NonUnitalModuleCat.of ℤ evenZeroSubmodule)).isModule.one_smul x

end ZeroAction

end Langlands.Algebra.NonUnitalModuleCat
