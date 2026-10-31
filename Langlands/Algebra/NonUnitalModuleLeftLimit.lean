import Langlands.Algebra.NonUnitalModule
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# The actual additive left-image inverse limit of an original module

Renard I.1.4, printed pp.9–10/PDF15–16. Projections and transitions use
the original left action of actual idempotents on the original vectors.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uM uB

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

namespace Idempotent

/-- The source's actual `e • M`, as an additive subgroup of the original vectors. -/
def leftImage (e : Idempotent A) (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] :
    AddSubgroup M where
  carrier := {m | (e : A) • m = m}
  zero_mem' := smul_zero _
  add_mem' := by
    intro m n hm hn
    change (e : A) • (m + n) = m + n
    rw [smul_add, hm, hn]
  neg_mem' := by
    intro m hm
    change (e : A) • (-m) = -m
    rw [smul_neg, hm]

@[simp] theorem mem_leftImage (e : Idempotent A) (m : M) :
    m ∈ e.leftImage M ↔ (e : A) • m = m := Iff.rfl

theorem mem_leftImage_iff_exists (e : Idempotent A) (m : M) :
    m ∈ e.leftImage M ↔ ∃ n : M, (e : A) • n = m := by
  constructor
  · intro hm
    exact ⟨m, hm⟩
  · rintro ⟨n, rfl⟩
    change (e : A) • ((e : A) • n) = (e : A) • n
    rw [← mul_smul, e.property.eq]

/-- The actual left projection from original vectors onto `e • M`. -/
def leftProjection (e : Idempotent A) (M : Type uM)
    [AddCommGroup M] [NonUnitalModule A M] : M →+ e.leftImage M where
  toFun m := ⟨(e : A) • m, by
    change (e : A) • ((e : A) • m) = (e : A) • m
    rw [← mul_smul, e.property.eq]⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' m n := Subtype.ext (smul_add (e : A) m n)

@[simp] theorem coe_leftProjection (e : Idempotent A) (m : M) :
    (e.leftProjection M m : M) = (e : A) • m := rfl

@[simp] theorem leftProjection_coe (e : Idempotent A) (m : e.leftImage M) :
    e.leftProjection M (m : M) = m := Subtype.ext m.property

theorem leftProjection_surjective (e : Idempotent A) :
    Function.Surjective (e.leftProjection M) := by
  intro m
  exact ⟨m, leftProjection_coe e m⟩

/-- The inverse-system transition `f • M → e • M` for `e ≤ f`. -/
def leftTransition {e f : Idempotent A} (_h : e ≤ f) :
    f.leftImage M →+ e.leftImage M :=
  (e.leftProjection M).comp (f.leftImage M).subtype

@[simp] theorem coe_leftTransition {e f : Idempotent A} (h : e ≤ f)
    (m : f.leftImage M) : (leftTransition h m : M) = (e : A) • (m : M) := rfl

@[simp] theorem leftTransition_refl (e : Idempotent A) :
    leftTransition (M := M) (le_refl e) = AddMonoidHom.id (e.leftImage M) := by
  ext m
  exact m.property

theorem leftTransition_comp {e f g : Idempotent A} (hef : e ≤ f) (hfg : f ≤ g) :
    (leftTransition (M := M) hef).comp (leftTransition hfg) =
      leftTransition (hef.trans hfg) := by
  ext m
  change (e : A) • ((f : A) • (m : M)) = (e : A) • (m : M)
  rw [← mul_smul, ((le_iff_mul e f).1 hef).2]

theorem leftTransition_projection {e f : Idempotent A} (h : e ≤ f) :
    (leftTransition h).comp (f.leftProjection M) = e.leftProjection M := by
  ext m
  change (e : A) • ((f : A) • m) = (e : A) • m
  rw [← mul_smul, ((le_iff_mul e f).1 h).2]

end Idempotent

/-- The actual left-compatible families, as an additive subgroup of all coordinates. -/
def leftCompatibleFamilies (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    AddSubgroup (Idempotent A → M) where
  carrier := {x | (∀ e : Idempotent A, (e : A) • x e = x e) ∧
    ∀ e f : Idempotent A, e ≤ f → (e : A) • x f = x e}
  zero_mem' := by
    constructor
    · intro e
      exact smul_zero _
    · intro e f _
      exact smul_zero _
  add_mem' := by
    rintro x y ⟨hx, hcx⟩ ⟨hy, hcy⟩
    constructor
    · intro e
      change (e : A) • (x e + y e) = x e + y e
      rw [smul_add, hx, hy]
    · intro e f h
      change (e : A) • (x f + y f) = x e + y e
      rw [smul_add, hcx e f h, hcy e f h]
  neg_mem' := by
    rintro x ⟨hx, hcx⟩
    constructor
    · intro e
      change (e : A) • (-x e) = -x e
      rw [smul_neg, hx]
    · intro e f h
      change (e : A) • (-x f) = -x e
      rw [smul_neg, hcx e f h]

/-- The actual additive inverse limit `lim (e • M)`; no scalar action is installed. -/
abbrev NonUnitalModuleLeftLimit (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :=
  ↥(leftCompatibleFamilies A M)

namespace NonUnitalModuleLeftLimit

/-- The actual coordinate in `e • M`. -/
def evaluation (e : Idempotent A) : NonUnitalModuleLeftLimit A M →+ e.leftImage M where
  toFun x := ⟨x.val e, x.property.1 e⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coe_evaluation (e : Idempotent A) (x : NonUnitalModuleLeftLimit A M) :
    (evaluation e x : M) = x.val e := rfl

@[ext] theorem ext {x y : NonUnitalModuleLeftLimit A M}
    (h : ∀ e, evaluation e x = evaluation e y) : x = y := by
  apply Subtype.ext
  funext e
  exact congrArg Subtype.val (h e)

theorem transition_evaluation {e f : Idempotent A} (h : e ≤ f) :
    (Idempotent.leftTransition h).comp (evaluation (M := M) f) = evaluation e := by
  ext x
  exact x.property.2 e f h

/-- The canonical additive family of the original vector. -/
def canonical : M →+ NonUnitalModuleLeftLimit A M where
  toFun m := ⟨fun e => (e : A) • m, by
    constructor
    · intro e
      rw [← mul_smul, e.property.eq]
    · intro e f h
      change (e : A) • ((f : A) • m) = (e : A) • m
      rw [← mul_smul, ((Idempotent.le_iff_mul e f).1 h).2]⟩
  map_zero' := by
    apply Subtype.ext
    funext e
    exact smul_zero _
  map_add' m n := by
    apply Subtype.ext
    funext e
    exact smul_add (e : A) m n

@[simp] theorem canonical_val (m : M) (e : Idempotent A) :
    (canonical (A := A) m).val e = (e : A) • m := rfl

@[simp] theorem evaluation_canonical (e : Idempotent A) :
    (evaluation e).comp (canonical (A := A) (M := M)) = e.leftProjection M := rfl

/-- A fixing idempotent for a difference proves injectivity on original nondegenerate vectors. -/
theorem canonical_injective (hM : IsNondegenerate A M) :
    Function.Injective (canonical (A := A) (M := M)) := by
  intro m n hmn
  obtain ⟨e, he⟩ := hM (m - n)
  have h : (e : A) • m = (e : A) • n :=
    congrArg (fun x : NonUnitalModuleLeftLimit A M => x.val e) hmn
  have hz : (e : A) • (m - n) = 0 := by rw [smul_sub, h, sub_self]
  exact sub_eq_zero.mp (he.symm.trans hz)

variable {B : Type uB} [AddCommGroup B]

/-- The actual additive lift of a compatible cone to the explicit family group. -/
def lift (q : ∀ e : Idempotent A, B →+ e.leftImage M)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.leftTransition h).comp (q f) = q e) :
    B →+ NonUnitalModuleLeftLimit A M where
  toFun b := ⟨fun e => (q e b : M), by
    constructor
    · intro e
      exact (q e b).property
    · intro e f h
      exact congrArg Subtype.val (DFunLike.congr_fun (hq e f h) b)⟩
  map_zero' := by
    apply Subtype.ext
    funext e
    change (q e 0 : M) = 0
    rw [map_zero]
    rfl
  map_add' b c := by
    apply Subtype.ext
    funext e
    change (q e (b + c) : M) = (q e b : M) + (q e c : M)
    rw [map_add]
    rfl

@[simp] theorem evaluation_lift (q : ∀ e : Idempotent A, B →+ e.leftImage M)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.leftTransition h).comp (q f) = q e) (e : Idempotent A) :
    (evaluation e).comp (lift q hq) = q e := rfl

theorem lift_unique (q : ∀ e : Idempotent A, B →+ e.leftImage M)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.leftTransition h).comp (q f) = q e)
    (l : B →+ NonUnitalModuleLeftLimit A M)
    (hl : ∀ e, (evaluation e).comp l = q e) : l = lift q hq := by
  apply AddMonoidHom.ext
  intro b
  apply ext
  intro e
  exact DFunLike.congr_fun (hl e) b

/-- The unique actual additive lift, with no assumed limit witness. -/
theorem existsUnique_lift (q : ∀ e : Idempotent A, B →+ e.leftImage M)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.leftTransition h).comp (q f) = q e) :
    ∃! l : B →+ NonUnitalModuleLeftLimit A M,
      ∀ e, (evaluation e).comp l = q e :=
  ⟨lift q hq, evaluation_lift q hq, fun l hl => lift_unique q hq l hl⟩

/-! Complete unapplied interfaces at independent ring, vector and test-group universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    (e : Idempotent A) → (M : Type uM) → [AddCommGroup M] →
    [NonUnitalModule A M] → AddSubgroup M :=
  @Idempotent.leftImage.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (e : Idempotent A) → (M : Type uM) → [AddCommGroup M] →
    [NonUnitalModule A M] → M →+ e.leftImage M :=
  @Idempotent.leftProjection.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {e f : Idempotent A} → e ≤ f → f.leftImage M →+ e.leftImage M :=
  @Idempotent.leftTransition.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) → NonUnitalModuleLeftLimit A M →+ e.leftImage M :=
  @evaluation.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    M →+ NonUnitalModuleLeftLimit A M :=
  @canonical.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsNondegenerate A M → Function.Injective (canonical (A := A) (M := M)) :=
  @canonical_injective.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsNondegenerate A M → Function.Injective (canonical (A := A) (M := M)) :=
  @canonical_injective.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsNondegenerate A M → Function.Injective (canonical (A := A) (M := M)) :=
  @canonical_injective.{1, 0}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {B : Type uB} → [AddCommGroup B] →
    (q : ∀ e : Idempotent A, B →+ e.leftImage M) →
    (∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.leftTransition h).comp (q f) = q e) →
    ∃! l : B →+ NonUnitalModuleLeftLimit A M,
      ∀ e, (evaluation e).comp l = q e :=
  @existsUnique_lift.{uA, uM, uB}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    {B : Type} → [AddCommGroup B] →
    (q : ∀ e : Idempotent A, B →+ e.leftImage M) →
    (∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.leftTransition h).comp (q f) = q e) →
    ∃! l : B →+ NonUnitalModuleLeftLimit A M,
      ∀ e, (evaluation e).comp l = q e :=
  @existsUnique_lift.{0, 1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    {B : Type 1} → [AddCommGroup B] →
    (q : ∀ e : Idempotent A, B →+ e.leftImage M) →
    (∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.leftTransition h).comp (q f) = q e) →
    ∃! l : B →+ NonUnitalModuleLeftLimit A M,
      ∀ e, (evaluation e).comp l = q e :=
  @existsUnique_lift.{1, 0, 1}

end NonUnitalModuleLeftLimit
end Langlands.Algebra
