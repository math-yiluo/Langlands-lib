import Langlands.Algebra.IdempotentedRing
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Ring.Opposite

/-!
# Nonunital modules and their nondegenerate part

Renard (9 July 2026), Chapter I conventions and I.1.2, printed pp. 5–8.
The ambient action has no unit law, even when its scalar ring has a unit.
-/

namespace Langlands.Algebra

open CategoryTheory

universe u v w x

/-- An associative distributive ring action on an abelian group, without a unit law. -/
class NonUnitalModule (A : Type u) (M : Type v) [NonUnitalRing A] [AddCommGroup M]
    extends DistribSMul A M, SemigroupAction A M where
  add_smul (a b : A) (m : M) : (a + b) • m = a • m + b • m
  zero_smul (m : M) : (0 : A) • m = 0

namespace NonUnitalModule

/-- Prefer the specified action to an unrelated canonical action on the same carrier type. -/
instance (priority := 1200) actionSMul {A : Type u} {M : Type v} [NonUnitalRing A]
    [AddCommGroup M] [h : NonUnitalModule A M] : SMul A M := h.toDistribSMul.toSMul

variable {A : Type u} {M : Type v} [NonUnitalRing A] [AddCommGroup M]

/-- The action as an actual nonunital ring homomorphism into additive endomorphisms. -/
def toEndHom (h : NonUnitalModule A M) : A →ₙ+* AddMonoid.End M where
  toFun a :=
    { toFun := (a • ·)
      map_zero' := smul_zero a
      map_add' := smul_add a }
  map_zero' := AddMonoidHom.ext (zero_smul)
  map_add' a b := AddMonoidHom.ext (add_smul a b)
  map_mul' a b := AddMonoidHom.ext (mul_smul a b)

/-- Every nonunital homomorphism into additive endomorphisms supplies the source action laws. -/
abbrev ofEndHom (ρ : A →ₙ+* AddMonoid.End M) : NonUnitalModule A M where
  smul a m := ρ a m
  smul_zero a := (ρ a).map_zero
  smul_add a := (ρ a).map_add
  mul_smul a b m := by
    change ρ (a * b) m = (ρ a * ρ b) m
    exact congrArg (fun f : AddMonoid.End M => f m) (ρ.map_mul' a b)
  add_smul a b m := by
    change ρ (a + b) m = (ρ a + ρ b) m
    exact congrArg (fun f : AddMonoid.End M => f m) (ρ.map_add' a b)
  zero_smul m := by
    change ρ 0 m = 0
    exact congrArg (fun f : AddMonoid.End M => f m) ρ.map_zero'

/-- Exact correspondence with the endomorphism-ring description; no unit is adjoined. -/
def equivEndHom : NonUnitalModule A M ≃ (A →ₙ+* AddMonoid.End M) where
  toFun := toEndHom
  invFun := ofEndHom
  left_inv h := by cases h; rfl
  right_inv ρ := by ext a m; rfl

/-- An ordinary unital module gives an ambient nonunital module. This is not a global instance. -/
abbrev ofModule (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] :
    NonUnitalModule R M where
  smul := (· • ·)
  smul_zero := smul_zero
  smul_add := smul_add
  mul_smul := SemigroupAction.mul_smul
  add_smul := _root_.add_smul
  zero_smul := _root_.zero_smul R

/-- An ambient action becomes an ordinary module precisely after supplying its unit law. -/
abbrev toModule {R : Type u} [Ring R] [NonUnitalModule R M]
    (h : ∀ m : M, (1 : R) • m = m) : Module R M where
  smul := (· • ·)
  one_smul := h
  mul_smul := mul_smul
  smul_add := smul_add
  smul_zero := smul_zero
  add_smul := NonUnitalModule.add_smul
  zero_smul := NonUnitalModule.zero_smul

/-- Zero actions are allowed, including over unital rings and on nonzero groups. -/
abbrev zero : NonUnitalModule A M where
  smul _ _ := 0
  smul_zero _ := rfl
  smul_add _ _ _ := (add_zero 0).symm
  mul_smul _ _ _ := rfl
  add_smul _ _ _ := (add_zero 0).symm
  zero_smul _ := rfl

end NonUnitalModule

/-- Additive intertwining maps between nonunital modules. -/
structure NonUnitalModuleHom (A : Type u) (M : Type v) (N : Type w)
    [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] extends M →+ N where
  map_smul' (a : A) (m : M) : toAddMonoidHom (a • m) = a • toAddMonoidHom m

namespace NonUnitalModuleHom

variable {A : Type u} {M : Type v} {N : Type w} {P : Type x}
  [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule A M] [NonUnitalModule A N] [NonUnitalModule A P]

instance : CoeFun (NonUnitalModuleHom A M N) (fun _ => M → N) :=
  ⟨fun f => f.toAddMonoidHom⟩

@[ext] theorem ext {f g : NonUnitalModuleHom A M N} (h : ∀ m, f m = g m) : f = g := by
  cases f
  cases g
  congr 1
  exact AddMonoidHom.ext h

@[simp] theorem map_zero (f : NonUnitalModuleHom A M N) : f 0 = 0 :=
  f.toAddMonoidHom.map_zero

@[simp] theorem map_add (f : NonUnitalModuleHom A M N) (m n : M) :
    f (m + n) = f m + f n := f.toAddMonoidHom.map_add m n

@[simp] theorem map_smul (f : NonUnitalModuleHom A M N) (a : A) (m : M) :
    f (a • m) = a • f m := f.map_smul' a m

/-- Identity intertwiner. -/
def id (A : Type u) (M : Type v) [NonUnitalRing A] [AddCommGroup M]
    [NonUnitalModule A M] : NonUnitalModuleHom A M M where
  toAddMonoidHom := AddMonoidHom.id M
  map_smul' _ _ := rfl

/-- Composition of intertwiners. -/
def comp (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom A M P where
  toAddMonoidHom := g.toAddMonoidHom.comp f.toAddMonoidHom
  map_smul' a m := by change g (f (a • m)) = a • g (f m); rw [map_smul, map_smul]

@[simp] theorem id_apply (m : M) : id A M m = m := rfl
@[simp] theorem comp_apply (g : NonUnitalModuleHom A N P)
    (f : NonUnitalModuleHom A M N) (m : M) : comp g f m = g (f m) := rfl

end NonUnitalModuleHom

/-- Actual ambient modules with carrier universe independent of the scalar universe. -/
structure NonUnitalModuleCat (A : Type u) [NonUnitalRing A] where
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : NonUnitalModule A carrier]

attribute [instance] NonUnitalModuleCat.isAddCommGroup NonUnitalModuleCat.isModule

namespace NonUnitalModuleCat

variable (A : Type u) [NonUnitalRing A]

instance : CoeSort (NonUnitalModuleCat.{u, v} A) (Type v) := ⟨NonUnitalModuleCat.carrier⟩

/-- Bundle any action satisfying the source laws. -/
abbrev of (M : Type v) [AddCommGroup M] [NonUnitalModule A M] : NonUnitalModuleCat.{u, v} A :=
  ⟨M⟩

instance : CategoryTheory.Category (NonUnitalModuleCat.{u, v} A) where
  Hom M N := NonUnitalModuleHom A M N
  id M := NonUnitalModuleHom.id A M
  comp f g := NonUnitalModuleHom.comp g f
  id_comp f := by ext m; rfl
  comp_id f := by ext m; rfl
  assoc f g h := by ext m; rfl

end NonUnitalModuleCat

/-- A submodule is an additive subgroup stable under the actual ambient action. -/
structure NonUnitalSubmodule (A : Type u) (M : Type v) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] extends AddSubgroup M where
  smul_mem' (a : A) {m : M} : m ∈ toAddSubgroup → a • m ∈ toAddSubgroup

namespace NonUnitalSubmodule

variable {A : Type u} {M : Type v} [NonUnitalRing A] [AddCommGroup M]
  [NonUnitalModule A M]

instance : SetLike (NonUnitalSubmodule A M) M where
  coe S := S.toAddSubgroup
  coe_injective S T h := by
    cases S
    cases T
    congr 1
    exact SetLike.coe_injective h

instance : PartialOrder (NonUnitalSubmodule A M) := .ofSetLike _ _

instance (S : NonUnitalSubmodule A M) : AddCommGroup S :=
  inferInstanceAs (AddCommGroup S.toAddSubgroup)

instance (S : NonUnitalSubmodule A M) : NonUnitalModule A S where
  smul a m := ⟨a • m.val, S.smul_mem' a m.property⟩
  smul_zero a := Subtype.ext (smul_zero a)
  smul_add a m n := Subtype.ext (smul_add a m.val n.val)
  mul_smul a b m := Subtype.ext (mul_smul a b m.val)
  add_smul a b m := Subtype.ext (NonUnitalModule.add_smul a b m.val)
  zero_smul m := Subtype.ext (NonUnitalModule.zero_smul m.val)

/-- The actual additive intertwining inclusion of a submodule. -/
def subtype (S : NonUnitalSubmodule A M) : NonUnitalModuleHom A S M where
  toAddMonoidHom := S.toAddSubgroup.subtype
  map_smul' _ _ := rfl

@[simp] theorem subtype_apply (S : NonUnitalSubmodule A M) (m : S) :
    S.subtype m = (m : M) := rfl

/-- Inclusion between stable additive subgroups. -/
def inclusion {S T : NonUnitalSubmodule A M} (h : S ≤ T) : NonUnitalModuleHom A S T where
  toFun m := ⟨m.val, h m.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end NonUnitalSubmodule

/-- Every vector is fixed by an actual idempotent of the scalar ring. -/
def IsNondegenerate (A : Type u) (M : Type v) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  ∀ m : M, ∃ e : Idempotent A, (e : A) • m = m

/-- Elementwise unitality, without presupposing a `Module` structure. -/
def IsUnitalModule (R : Type u) (M : Type v) [Ring R]
    [AddCommGroup M] [NonUnitalModule R M] : Prop := ∀ m : M, (1 : R) • m = m

/-- Remark 1 of I.1.2, at the level of individual vectors. -/
theorem exists_idempotent_smul_eq_iff_one_smul_eq {R : Type u} {M : Type v}
    [Ring R] [AddCommGroup M] [NonUnitalModule R M] (m : M) :
    (∃ e : Idempotent R, (e : R) • m = m) ↔ (1 : R) • m = m := by
  constructor
  · rintro ⟨e, he⟩
    calc
      (1 : R) • m = (1 : R) • ((e : R) • m) := congrArg ((1 : R) • ·) he.symm
      _ = m := by rw [← mul_smul, one_mul, he]
  · intro h
    exact ⟨⟨1, IsIdempotentElem.one⟩, h⟩

theorem isNondegenerate_iff_isUnitalModule {R : Type u} {M : Type v}
    [Ring R] [AddCommGroup M] [NonUnitalModule R M] :
    IsNondegenerate R M ↔ IsUnitalModule R M := by
  simp only [IsNondegenerate, IsUnitalModule, exists_idempotent_smul_eq_iff_one_smul_eq]

/-- The object property defining Renard's full subcategory. -/
def nondegenerateProperty (A : Type u) [NonUnitalRing A] :
    CategoryTheory.ObjectProperty (NonUnitalModuleCat.{u, v} A) := fun M => IsNondegenerate A M

/-- The actual full subcategory of nondegenerate ambient modules. -/
abbrev NondegenerateModuleCat (A : Type u) [NonUnitalRing A] :=
  (nondegenerateProperty.{u, v} A).FullSubcategory

/-- The actual fully faithful inclusion into all ambient modules. -/
abbrev nondegenerateInclusion (A : Type u) [NonUnitalRing A] :
    NondegenerateModuleCat.{u, v} A ⥤ NonUnitalModuleCat.{u, v} A :=
  (nondegenerateProperty A).ι

namespace Idempotent

/-- The absorption law on every ambient module, derived from the ring-core order. -/
theorem smul_eq_of_le {A : Type u} {M : Type v} [NonUnitalRing A] [AddCommGroup M]
    [NonUnitalModule A M] {e f : Idempotent A} (h : e ≤ f) {m : M}
    (hm : (e : A) • m = m) : (f : A) • m = m := by
  calc
    (f : A) • m = (f : A) • ((e : A) • m) := congrArg ((f : A) • ·) hm.symm
    _ = m := by rw [← mul_smul, ((le_iff_mul e f).mp h).1, hm]

end Idempotent

/-- The actual stable additive subgroup of vectors fixed by some idempotent. -/
def nondegeneratePart {A : Type u} [NonUnitalRing A] (hA : IsIdempotented A)
    (M : Type v) [AddCommGroup M] [NonUnitalModule A M] : NonUnitalSubmodule A M := by
  classical
  exact
    { carrier := {m | ∃ e : Idempotent A, (e : A) • m = m}
      zero_mem' := ⟨⟨0, IsIdempotentElem.zero⟩, smul_zero (0 : A)⟩
      add_mem' := by
        rintro m n ⟨e, he⟩ ⟨f, hf⟩
        obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
        exact ⟨g, by rw [smul_add, Idempotent.smul_eq_of_le (hg e (by simp)) he,
          Idempotent.smul_eq_of_le (hg f (by simp)) hf]⟩
      neg_mem' := by
        rintro m ⟨e, he⟩
        exact ⟨e, by rw [smul_neg, he]⟩
      smul_mem' := by
        intro a m _
        obtain ⟨e, he⟩ := hA.exists_mem_corner a
        refine ⟨e, ?_⟩
        rw [← mul_smul, ((Idempotent.mem_corner_iff e a).mp he).1] }

@[simp] theorem mem_nondegeneratePart {A : Type u} {M : Type v} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] (hA : IsIdempotented A) (m : M) :
    m ∈ nondegeneratePart hA M ↔ ∃ e : Idempotent A, (e : A) • m = m := Iff.rfl

/-- The displayed union of images in I.1.2, expressed elementwise, without a colimit claim. -/
theorem mem_nondegeneratePart_iff_exists_smul {A : Type u} {M : Type v}
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (m : M) :
    m ∈ nondegeneratePart hA M ↔ ∃ (e : Idempotent A) (n : M), (e : A) • n = m := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, m, he⟩
  · rintro ⟨e, n, rfl⟩
    exact ⟨e, by rw [← mul_smul, e.property.eq]⟩

/-- The constructed part is itself nondegenerate, with its inherited action. -/
theorem nondegeneratePart_isNondegenerate {A : Type u} {M : Type v} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] (hA : IsIdempotented A) :
    IsNondegenerate A (nondegeneratePart hA M) := by
  intro m
  obtain ⟨e, he⟩ := m.property
  exact ⟨e, Subtype.ext he⟩

/-- Exact universal containment criterion among actual submodules. -/
theorem le_nondegeneratePart_iff {A : Type u} {M : Type v} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] (hA : IsIdempotented A)
    (S : NonUnitalSubmodule A M) : S ≤ nondegeneratePart hA M ↔ IsNondegenerate A S := by
  constructor
  · intro h m
    obtain ⟨e, he⟩ := h m.property
    exact ⟨e, Subtype.ext he⟩
  · intro h m hm
    obtain ⟨e, he⟩ := h ⟨m, hm⟩
    exact ⟨e, congrArg Subtype.val he⟩

/-- In a unital ring the part consists exactly of vectors fixed by the unit. -/
theorem mem_nondegeneratePart_iff_one_smul_eq {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [NonUnitalModule R M] (m : M) :
    m ∈ nondegeneratePart (IsIdempotented.of_ring R) M ↔ (1 : R) • m = m :=
  exists_idempotent_smul_eq_iff_one_smul_eq m

namespace NonUnitalModuleHom

variable {A : Type u} {M : Type v} {N : Type w} {P : Type x}
  [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule A M] [NonUnitalModule A N] [NonUnitalModule A P]

/-- An actual intertwiner preserves idempotent-fixed vectors. -/
theorem map_mem_nondegeneratePart (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N)
    {m : M} (hm : m ∈ nondegeneratePart hA M) : f m ∈ nondegeneratePart hA N := by
  obtain ⟨e, he⟩ := hm
  exact ⟨e, (f.map_smul e m).symm.trans (congrArg f he)⟩

/-- Restriction of an intertwiner to the actual nondegenerate submodules. -/
def restrictNondegeneratePart (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom A (nondegeneratePart hA M) (nondegeneratePart hA N) where
  toFun m := ⟨f m.val, f.map_mem_nondegeneratePart hA m.property⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' m n := Subtype.ext (f.map_add m.val n.val)
  map_smul' a m := Subtype.ext (f.map_smul a m.val)

@[simp] theorem restrictNondegeneratePart_apply (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) (m : nondegeneratePart hA M) :
    (f.restrictNondegeneratePart hA m : N) = f m.val := rfl

@[simp] theorem restrictNondegeneratePart_id (hA : IsIdempotented A) :
    (id A M).restrictNondegeneratePart hA = id A (nondegeneratePart hA M) := by
  ext m
  rfl

@[simp] theorem restrictNondegeneratePart_comp (hA : IsIdempotented A)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    (g.comp f).restrictNondegeneratePart hA =
      (g.restrictNondegeneratePart hA).comp (f.restrictNondegeneratePart hA) := by
  ext m
  rfl

end NonUnitalModuleHom

/-- The nondegenerate-part functor, including its actual identity and composition laws. -/
def nondegeneratePartFunctor {A : Type u} [NonUnitalRing A] (hA : IsIdempotented A) :
    NonUnitalModuleCat.{u, v} A ⥤ NondegenerateModuleCat.{u, v} A where
  obj M := ⟨NonUnitalModuleCat.of A (nondegeneratePart hA M),
    nondegeneratePart_isNondegenerate hA⟩
  map f := CategoryTheory.ObjectProperty.homMk (f.restrictNondegeneratePart hA)
  map_id M := by
    apply CategoryTheory.ObjectProperty.hom_ext
    exact NonUnitalModuleHom.restrictNondegeneratePart_id hA
  map_comp f g := by
    apply CategoryTheory.ObjectProperty.hom_ext
    exact NonUnitalModuleHom.restrictNondegeneratePart_comp hA g f

/-- The inclusions of the parts commute with every actual ambient morphism. -/
def nondegeneratePartInclusion {A : Type u} [NonUnitalRing A] (hA : IsIdempotented A) :
    nondegeneratePartFunctor.{u, v} hA ⋙ nondegenerateInclusion A ⟶
      𝟭 (NonUnitalModuleCat.{u, v} A) where
  app M := (nondegeneratePart hA M).subtype
  naturality := by
    intro M N f
    apply NonUnitalModuleHom.ext
    intro m
    rfl

namespace IsIdempotented

/-- Opposite rings have the same finite-local-unit property. -/
theorem op {A : Type u} [NonUnitalRing A] (hA : IsIdempotented A) :
    IsIdempotented Aᵐᵒᵖ := by
  classical
  intro s
  obtain ⟨e, he⟩ := hA (s.image MulOpposite.unop)
  refine ⟨⟨MulOpposite.op (e : A), ?_⟩, ?_⟩
  · change MulOpposite.op ((e : A) * e) = MulOpposite.op (e : A)
    exact congrArg MulOpposite.op e.property.eq
  · intro a ha
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, ← mul_assoc] using
      he a.unop (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

end IsIdempotented

/-- Right modules mean left modules over the opposite ring. -/
abbrev RightNonUnitalModule (A : Type u) (M : Type v) [NonUnitalRing A] [AddCommGroup M] :=
  NonUnitalModule Aᵐᵒᵖ M

/-- The actual ambient category of right modules, with the opposite-ring convention. -/
abbrev RightNonUnitalModuleCat (A : Type u) [NonUnitalRing A] :=
  NonUnitalModuleCat.{u, v} Aᵐᵒᵖ

/-- The right nondegeneracy predicate uses the very same construction over the opposite ring. -/
abbrev IsRightNondegenerate (A : Type u) (M : Type v) [NonUnitalRing A] [AddCommGroup M]
    [RightNonUnitalModule A M] : Prop := IsNondegenerate Aᵐᵒᵖ M

/-- The full subcategory of nondegenerate right modules. -/
abbrev RightNondegenerateModuleCat (A : Type u) [NonUnitalRing A] :=
  NondegenerateModuleCat.{u, v} Aᵐᵒᵖ

/-- The right-module nondegenerate-part functor is the opposite-ring instance of the left one. -/
abbrev rightNondegeneratePartFunctor {A : Type u} [NonUnitalRing A] (hA : IsIdempotented A) :
    RightNonUnitalModuleCat.{u, v} A ⥤ RightNondegenerateModuleCat.{u, v} A :=
  nondegeneratePartFunctor hA.op

/-- In right-action notation, associativity reverses the order of the opposite scalars. -/
theorem right_mul_smul {A : Type u} {M : Type v} [NonUnitalRing A] [AddCommGroup M]
    [RightNonUnitalModule A M] (a b : A) (m : M) :
    MulOpposite.op (a * b) • m = MulOpposite.op b • (MulOpposite.op a • m) := by
  rw [MulOpposite.op_mul, mul_smul]

end Langlands.Algebra
