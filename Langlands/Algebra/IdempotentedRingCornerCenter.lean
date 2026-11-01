import Langlands.Algebra.IdempotentedRing
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# The projective system of corner centers

The actual centers and center-only sandwich transitions of Renard (9 July
2026), I.1.7, with the coherent-family ring. No comparison to a completed
ring or categorical center is made here.
-/

namespace Langlands.Algebra

universe uA uR

namespace Idempotent

variable {A : Type uA} [NonUnitalRing A]

/-- The actual center of the published unital corner, with its original ring. -/
def CornerCenter (e : Idempotent A) := ↥(Subring.center (Corner e))

namespace CornerCenter

instance commRing (e : Idempotent A) : CommRing (CornerCenter e) :=
  inferInstanceAs (CommRing ↥(Subring.center (Corner e)))

/-- The entire center inclusion into its original corner ring. -/
def toCorner (e : Idempotent A) : CornerCenter e →+* Corner e :=
  (Subring.center (Corner e)).subtype

/-- The actual ambient nonunital inclusion. -/
def toAmbient (e : Idempotent A) : CornerCenter e →ₙ+* A :=
  (Corner.toAmbient e).comp (toCorner e).toNonUnitalRingHom

@[simp] theorem toCorner_apply (e : Idempotent A) (z : CornerCenter e) :
    toCorner e z = z.val := rfl

@[simp] theorem toAmbient_apply (e : Idempotent A) (z : CornerCenter e) :
    toAmbient e z = z.val.val := rfl

/-- The complete underlying ambient function: the two subtype values. -/
theorem toAmbient_function (e : Idempotent A) :
    (toAmbient e : CornerCenter e → A) = fun z => z.val.val := rfl

theorem toAmbient_injective (e : Idempotent A) :
    Function.Injective (toAmbient e) := by
  intro z w h
  exact Subtype.ext (Subtype.ext h)

@[simp] theorem toAmbient_one (e : Idempotent A) :
    toAmbient e 1 = (e : A) := rfl

/-- Centrality in a corner, expressed using the original ambient multiplication. -/
theorem ambient_commute (e : Idempotent A) (z : CornerCenter e) (a : Corner e) :
    toAmbient e z * Corner.toAmbient e a = Corner.toAmbient e a * toAmbient e z :=
  congrArg (Corner.toAmbient e) ((Subring.mem_center_iff.mp z.property) a).symm

/-- A central element of the larger corner commutes with the smaller idempotent. -/
theorem ambient_commute_idempotent {e f : Idempotent A} (h : e ≤ f)
    (z : CornerCenter f) : toAmbient f z * (e : A) = (e : A) * toAmbient f z :=
  ambient_commute f z (Corner.inclusion h 1)

/-- Restriction into the smaller corner, before certifying its centrality. -/
def sandwich {e f : Idempotent A} (_h : e ≤ f) (z : CornerCenter f) : Corner e :=
  ⟨(e : A) * toAmbient f z * e,
    (mem_corner_iff_exists e _).mpr ⟨toAmbient f z, rfl⟩⟩

@[simp] theorem sandwich_ambient {e f : Idempotent A} (h : e ≤ f)
    (z : CornerCenter f) :
    Corner.toAmbient e (sandwich h z) = (e : A) * toAmbient f z * e := rfl

/-- Centrality removes one of the two copies of the smaller idempotent. -/
theorem sandwich_ambient_eq_left {e f : Idempotent A} (h : e ≤ f)
    (z : CornerCenter f) :
    Corner.toAmbient e (sandwich h z) = (e : A) * toAmbient f z := by
  change (e : A) * toAmbient f z * e = e * toAmbient f z
  rw [mul_assoc, ambient_commute_idempotent h z, ← mul_assoc, e.property.eq]

/-- The sandwich of a central element is central in the smaller corner. -/
theorem sandwich_mem_center {e f : Idempotent A} (h : e ≤ f)
    (z : CornerCenter f) : sandwich h z ∈ Subring.center (Corner e) := by
  apply Subring.mem_center_iff.mpr
  intro a
  apply (Corner.toAmbient_injective e)
  change Corner.toAmbient e a * Corner.toAmbient e (sandwich h z) =
    Corner.toAmbient e (sandwich h z) * Corner.toAmbient e a
  rw [sandwich_ambient_eq_left]
  have ha := (mem_corner_iff e a.val).mp a.property
  have hz := ambient_commute f z (Corner.inclusion h a)
  change toAmbient f z * a.val = a.val * toAmbient f z at hz
  change a.val * ((e : A) * toAmbient f z) =
    ((e : A) * toAmbient f z) * a.val
  calc
    a.val * ((e : A) * toAmbient f z) = a.val * toAmbient f z := by
      rw [← mul_assoc, ha.2]
    _ = toAmbient f z * a.val := hz.symm
    _ = (e : A) * (toAmbient f z * a.val) := by rw [hz, ← mul_assoc, ha.1]
    _ = ((e : A) * toAmbient f z) * a.val := (mul_assoc _ _ _).symm

/-- The center-only, unit-preserving transition `Z(fAf) → Z(eAe)`. -/
def transition {e f : Idempotent A} (h : e ≤ f) : CornerCenter f →+* CornerCenter e where
  toFun z := ⟨sandwich h z, sandwich_mem_center h z⟩
  map_zero' := by
    apply toAmbient_injective e
    change (e : A) * 0 * e = 0
    simp
  map_add' z w := by
    apply toAmbient_injective e
    change (e : A) * (toAmbient f z + toAmbient f w) * e =
      e * toAmbient f z * e + e * toAmbient f w * e
    rw [mul_add, add_mul]
  map_one' := by
    apply toAmbient_injective e
    change (e : A) * f * e = e
    rw [((le_iff_mul e f).mp h).2, e.property.eq]
  map_mul' z w := by
    apply toAmbient_injective e
    change Corner.toAmbient e (sandwich h (z * w)) =
      Corner.toAmbient e (sandwich h z) * Corner.toAmbient e (sandwich h w)
    rw [sandwich_ambient_eq_left, sandwich_ambient_eq_left, sandwich_ambient_eq_left]
    change (e : A) * (toAmbient f z * toAmbient f w) =
      (e * toAmbient f z) * (e * toAmbient f w)
    calc
      (e : A) * (toAmbient f z * toAmbient f w) =
          (e * toAmbient f z) * toAmbient f w := (mul_assoc _ _ _).symm
      _ = (e * toAmbient f z * e) * toAmbient f w :=
        congrArg (· * toAmbient f w) (sandwich_ambient_eq_left h z).symm
      _ = (e * toAmbient f z) * (e * toAmbient f w) := mul_assoc _ _ _

@[simp] theorem transition_ambient {e f : Idempotent A} (h : e ≤ f)
    (z : CornerCenter f) :
    toAmbient e (transition h z) = (e : A) * toAmbient f z * e := rfl

/-- The entire underlying ambient function, not just one point. -/
theorem transition_ambient_function {e f : Idempotent A} (h : e ≤ f) :
    toAmbient e ∘ transition h = fun z => (e : A) * toAmbient f z * e := rfl

@[simp] theorem toCorner_transition {e f : Idempotent A} (h : e ≤ f)
    (z : CornerCenter f) : toCorner e (transition h z) = sandwich h z := rfl

/-- The entire underlying corner-valued function is the sandwich restriction. -/
theorem toCorner_transition_function {e f : Idempotent A} (h : e ≤ f) :
    toCorner e ∘ transition h = sandwich h := rfl

@[simp] theorem transition_refl (e : Idempotent A) :
    transition (le_refl e) = RingHom.id (CornerCenter e) := by
  ext z
  apply toAmbient_injective e
  exact (mem_corner e z.val.val).mp z.val.property

/-- Composition holds as an equality of the entire ring homomorphisms. -/
theorem transition_comp {e f g : Idempotent A} (hef : e ≤ f) (hfg : f ≤ g) :
    (transition hef).comp (transition hfg) = transition (hef.trans hfg) := by
  ext z
  apply toAmbient_injective e
  change (e : A) * (f * toAmbient g z * f) * e = e * toAmbient g z * e
  have hef' := (le_iff_mul e f).mp hef
  simp only [← mul_assoc, hef'.2]
  rw [mul_assoc (e * toAmbient g z) (f : A) (e : A), hef'.1]

end CornerCenter
end Idempotent

namespace IdempotentedRingCornerCenter

open Idempotent

variable (A : Type uA) [NonUnitalRing A]

/-- The actual coherent-family subring of the product of the corner centers. -/
def coherentSubring : Subring (∀ e : Idempotent A, CornerCenter e) where
  carrier := {x | ∀ (e f : Idempotent A) (h : e ≤ f),
    CornerCenter.transition h (x f) = x e}
  zero_mem' := by intro e f h; exact map_zero _
  one_mem' := by intro e f h; exact map_one _
  add_mem' := by
    intro x y hx hy e f h
    change CornerCenter.transition h (x f + y f) = x e + y e
    rw [map_add, hx e f h, hy e f h]
  neg_mem' := by
    intro x hx e f h
    change CornerCenter.transition h (-x f) = -x e
    rw [map_neg, hx e f h]
  mul_mem' := by
    intro x y hx hy e f h
    change CornerCenter.transition h (x f * y f) = x e * y e
    rw [map_mul, hx e f h, hy e f h]

/-- Membership is exactly the full family of transition identities. -/
theorem mem_coherentSubring (x : ∀ e : Idempotent A, CornerCenter e) :
    x ∈ coherentSubring A ↔ ∀ (e f : Idempotent A) (h : e ≤ f),
      CornerCenter.transition h (x f) = x e := Iff.rfl

/-- The actual compatible families, with no independently supplied ring structure. -/
def Family := ↥(coherentSubring A)

namespace Family

instance commRing : CommRing (Family A) :=
  inferInstanceAs (CommRing ↥(coherentSubring A))

variable {A}

@[ext] theorem ext {x y : Family A} (h : ∀ e, x.val e = y.val e) : x = y :=
  Subtype.ext (funext h)

/-- Projection to the entire central element in the indicated corner. -/
def coordinate (e : Idempotent A) : Family A →+* CornerCenter e where
  toFun x := x.val e
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem coordinate_apply (e : Idempotent A) (x : Family A) :
    coordinate e x = x.val e := rfl

/-- The complete underlying coordinate function. -/
theorem coordinate_function (e : Idempotent A) :
    (coordinate e : Family A → CornerCenter e) = fun x => x.val e := rfl

/-- The coordinate is evaluation of the product after the actual subring inclusion. -/
theorem coordinate_eq_eval_comp_subtype (e : Idempotent A) :
    coordinate e =
      (Pi.evalRingHom (fun d : Idempotent A => CornerCenter d) e).comp
        (coherentSubring A).subtype := rfl

/-- The original ambient element of a coordinate. -/
def ambientCoordinate (e : Idempotent A) : Family A →ₙ+* A :=
  (CornerCenter.toAmbient e).comp (coordinate e).toNonUnitalRingHom

@[simp] theorem ambientCoordinate_apply (e : Idempotent A) (x : Family A) :
    ambientCoordinate e x = (x.val e).val.val := rfl

theorem ambientCoordinate_function (e : Idempotent A) :
    (ambientCoordinate e : Family A → A) = fun x => (x.val e).val.val := rfl

/-- Compatibility as equality of complete ring homomorphisms. -/
theorem coordinate_transition {e f : Idempotent A} (h : e ≤ f) :
    (CornerCenter.transition h).comp (coordinate f) = coordinate e := by
  ext x
  exact x.property e f h

/-- The source sandwich compatibility on the original ambient values. -/
theorem ambientCoordinate_compatible {e f : Idempotent A} (h : e ≤ f)
    (x : Family A) :
    (e : A) * ambientCoordinate f x * e = ambientCoordinate e x :=
  congrArg (CornerCenter.toAmbient e) (x.property e f h)

/-- Ambient compatibility as equality of the complete functions. -/
theorem ambientCoordinate_compatible_function {e f : Idempotent A} (h : e ≤ f) :
    (fun a : A => (e : A) * a * e) ∘ ambientCoordinate f = ambientCoordinate e :=
  funext (ambientCoordinate_compatible h)

/-- The intrinsic universal lift from an independently sized original ring. -/
def lift {R : Type uR} [Ring R] (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e) : R →+* Family A where
  toFun r := ⟨fun e => p e r, fun e f h =>
    congrArg (fun q : R →+* CornerCenter e => q r) (hp e f h)⟩
  map_zero' := ext (fun e => (p e).map_zero)
  map_one' := ext (fun e => (p e).map_one)
  map_add' r s := ext (fun e => (p e).map_add r s)
  map_mul' r s := ext (fun e => (p e).map_mul r s)

/-- Projection of a universal lift, as equality of entire ring homomorphisms. -/
@[simp] theorem coordinate_lift {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e) (e : Idempotent A) :
    (coordinate e).comp (lift p hp) = p e := rfl

theorem lift_coordinates_function {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e) :
    Subtype.val ∘ lift p hp = fun r e => p e r := rfl

/-- A ring homomorphism to the families is determined by its entire projections. -/
theorem lift_unique {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e)
    (q : R →+* Family A) (hq : ∀ e, (coordinate e).comp q = p e) :
    q = lift p hp := by
  apply RingHom.ext
  intro r
  apply ext
  intro e
  exact congrArg (fun k : R →+* CornerCenter e => k r) (hq e)

end Family

open CategoryTheory CategoryTheory.Limits Opposite

/-- The actual contravariant diagram of central unital corner rings. -/
def diagram : (Idempotent A)ᵒᵖ ⥤ CommRingCat.{uA} where
  obj e := CommRingCat.of (CornerCenter e.unop)
  map h := CommRingCat.ofHom (CornerCenter.transition (leOfHom h.unop))
  map_id e := by
    apply CommRingCat.hom_ext
    exact CornerCenter.transition_refl e.unop
  map_comp h k := by
    apply CommRingCat.hom_ext
    exact (CornerCenter.transition_comp (leOfHom k.unop) (leOfHom h.unop)).symm

/-- The projection cone on the actual coherent-family commutative ring. -/
def cone : Cone (diagram A) where
  pt := CommRingCat.of (Family A)
  π :=
    { app := fun e => CommRingCat.ofHom (Family.coordinate e.unop)
      naturality := by
        intro e f h
        apply CommRingCat.hom_ext
        change Family.coordinate f.unop =
          (CornerCenter.transition (leOfHom h.unop)).comp (Family.coordinate e.unop)
        exact (Family.coordinate_transition (leOfHom h.unop)).symm }

theorem diagram_obj (e : (Idempotent A)ᵒᵖ) :
    (diagram A).obj e = CommRingCat.of (CornerCenter e.unop) := rfl

/-- Each diagram arrow is exactly the corresponding center transition. -/
theorem diagram_map_hom {e f : (Idempotent A)ᵒᵖ} (h : e ⟶ f) :
    ((diagram A).map h).hom = CornerCenter.transition (leOfHom h.unop) := rfl

theorem cone_pt : (cone A).pt = CommRingCat.of (Family A) := rfl

/-- Each cone leg is exactly the corresponding coordinate homomorphism. -/
theorem cone_π_app_hom (e : (Idempotent A)ᵒᵖ) :
    ((cone A).π.app e).hom = Family.coordinate e.unop := rfl

variable {A} in
/-- The legs of any cone over the diagram form a compatible family. -/
theorem cone_legs_compatible (s : Cone (diagram A)) (e f : Idempotent A) (h : e ≤ f) :
    (CornerCenter.transition h).comp (s.π.app (op f)).hom = (s.π.app (op e)).hom := by
  have hh := s.π.naturality (homOfLE h).op
  simp only [Functor.const_obj_map] at hh
  exact congrArg CommRingCat.Hom.hom hh.symm

/-- The projection cone is the categorical limit of the actual diagram. -/
def coneIsLimit : IsLimit (cone A) where
  lift s := CommRingCat.ofHom
    (Family.lift (fun e => (s.π.app (op e)).hom) (cone_legs_compatible s))
  fac s e := by
    apply CommRingCat.hom_ext
    rfl
  uniq s m hm := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    apply Family.ext
    intro e
    exact congrArg (fun q : s.pt ⟶ (diagram A).obj (op e) => q.hom r) (hm (op e))

/-- The limit's factorization is exactly the universal lift of the cone legs. -/
theorem coneIsLimit_lift_hom (s : Cone (diagram A)) :
    ((coneIsLimit A).lift s).hom =
      Family.lift (fun e => (s.π.app (op e)).hom) (cone_legs_compatible s) := rfl

end IdempotentedRingCornerCenter

/-! Complete unapplied interfaces preserve their original telescopes and universes. -/
namespace IdempotentedRingCornerCenter

open Idempotent CategoryTheory CategoryTheory.Limits Opposite

section ArbitraryUniverses

example : ∀ {A : Type uA} [NonUnitalRing A], Idempotent A → Type uA :=
  @Idempotent.CornerCenter

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    CommRing (CornerCenter e) :=
  @CornerCenter.commRing

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter e →+* Corner e :=
  @CornerCenter.toCorner

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter e →ₙ+* A :=
  @CornerCenter.toAmbient

example : ∀ {A : Type uA} [NonUnitalRing A] {e f : Idempotent A},
    e ≤ f → CornerCenter f →+* CornerCenter e :=
  @CornerCenter.transition

example : ∀ {A : Type uA} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    CornerCenter.toAmbient e ∘ CornerCenter.transition h =
      fun z => (e : A) * CornerCenter.toAmbient f z * e :=
  @CornerCenter.transition_ambient_function

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter.transition (le_refl e) = RingHom.id (CornerCenter e) :=
  @CornerCenter.transition_refl

example : ∀ {A : Type uA} [NonUnitalRing A] {e f g : Idempotent A}
    (hef : e ≤ f) (hfg : f ≤ g),
    (CornerCenter.transition hef).comp (CornerCenter.transition hfg) =
      CornerCenter.transition (hef.trans hfg) :=
  @CornerCenter.transition_comp

example : ∀ (A : Type uA) [NonUnitalRing A],
    Subring (∀ e : Idempotent A, CornerCenter e) :=
  @coherentSubring

example : ∀ (A : Type uA) [NonUnitalRing A], Type uA :=
  @Family

example : ∀ (A : Type uA) [NonUnitalRing A], CommRing (Family A) :=
  @Family.commRing

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    Family A →+* CornerCenter e :=
  @Family.coordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    (Family.coordinate e : Family A → CornerCenter e) = fun x => x.val e :=
  @Family.coordinate_function

example : ∀ {A : Type uA} [NonUnitalRing A] (_e : Idempotent A),
    Family A →ₙ+* A :=
  @Family.ambientCoordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    (Family.ambientCoordinate e : Family A → A) = fun x => (x.val e).val.val :=
  @Family.ambientCoordinate_function

example : ∀ {A : Type uA} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    (CornerCenter.transition h).comp (Family.coordinate f) = Family.coordinate e :=
  @Family.coordinate_transition

example : ∀ {A : Type uA} [NonUnitalRing A] {e f : Idempotent A} (_h : e ≤ f),
    (fun a : A => (e : A) * a * e) ∘ Family.ambientCoordinate f =
      Family.ambientCoordinate e :=
  @Family.ambientCoordinate_compatible_function

example : ∀ {A : Type uA} [NonUnitalRing A] {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (_hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e), R →+* Family A :=
  @Family.lift

example : ∀ {A : Type uA} [NonUnitalRing A] {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e) (e : Idempotent A),
    (Family.coordinate e).comp (Family.lift p hp) = p e :=
  @Family.coordinate_lift

example : ∀ {A : Type uA} [NonUnitalRing A] {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e),
    Subtype.val ∘ Family.lift p hp = fun r e => p e r :=
  @Family.lift_coordinates_function

example : ∀ {A : Type uA} [NonUnitalRing A] {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e)
    (q : R →+* Family A) (_hq : ∀ e, (Family.coordinate e).comp q = p e),
    q = Family.lift p hp :=
  @Family.lift_unique

example : ∀ (A : Type uA) [NonUnitalRing A],
    (Idempotent A)ᵒᵖ ⥤ CommRingCat.{uA} :=
  @diagram

example : ∀ (A : Type uA) [NonUnitalRing A], Cone (diagram A) :=
  @cone

example : ∀ (A : Type uA) [NonUnitalRing A], IsLimit (cone A) :=
  @coneIsLimit

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    (CornerCenter.toAmbient e : CornerCenter e → A) = fun z => z.val.val :=
  @CornerCenter.toAmbient_function

example : ∀ {A : Type uA} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    CornerCenter.toCorner e ∘ CornerCenter.transition h = CornerCenter.sandwich h :=
  @CornerCenter.toCorner_transition_function

example : ∀ (A : Type uA) [NonUnitalRing A] (x : ∀ e : Idempotent A, CornerCenter e),
    x ∈ coherentSubring A ↔ ∀ (e f : Idempotent A) (h : e ≤ f),
      CornerCenter.transition h (x f) = x e :=
  @mem_coherentSubring

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    Family.coordinate e =
      (Pi.evalRingHom (fun d : Idempotent A => CornerCenter d) e).comp
        (coherentSubring A).subtype :=
  @Family.coordinate_eq_eval_comp_subtype

example : ∀ (A : Type uA) [NonUnitalRing A] (e : (Idempotent A)ᵒᵖ),
    (diagram A).obj e = CommRingCat.of (CornerCenter e.unop) :=
  @diagram_obj

example : ∀ (A : Type uA) [NonUnitalRing A] {e f : (Idempotent A)ᵒᵖ} (h : e ⟶ f),
    ((diagram A).map h).hom = CornerCenter.transition (leOfHom h.unop) :=
  @diagram_map_hom

example : ∀ (A : Type uA) [NonUnitalRing A],
    (cone A).pt = CommRingCat.of (Family A) :=
  @cone_pt

example : ∀ (A : Type uA) [NonUnitalRing A] (e : (Idempotent A)ᵒᵖ),
    ((cone A).π.app e).hom = Family.coordinate e.unop :=
  @cone_π_app_hom

example : ∀ {A : Type uA} [NonUnitalRing A] (s : Cone (diagram A))
    (e f : Idempotent A) (h : e ≤ f),
    (CornerCenter.transition h).comp (s.π.app (op f)).hom = (s.π.app (op e)).hom :=
  @cone_legs_compatible

example : ∀ (A : Type uA) [NonUnitalRing A] (s : Cone (diagram A)),
    ((coneIsLimit A).lift s).hom =
      Family.lift (fun e => (s.π.app (op e)).hom) (cone_legs_compatible s) :=
  @coneIsLimit_lift_hom

end ArbitraryUniverses

section UniverseZeroOne

example : ∀ {A : Type 0} [NonUnitalRing A], Idempotent A → Type 0 :=
  @Idempotent.CornerCenter

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    CommRing (CornerCenter e) :=
  @CornerCenter.commRing

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter e →+* Corner e :=
  @CornerCenter.toCorner

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter e →ₙ+* A :=
  @CornerCenter.toAmbient

example : ∀ {A : Type 0} [NonUnitalRing A] {e f : Idempotent A},
    e ≤ f → CornerCenter f →+* CornerCenter e :=
  @CornerCenter.transition

example : ∀ {A : Type 0} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    CornerCenter.toAmbient e ∘ CornerCenter.transition h =
      fun z => (e : A) * CornerCenter.toAmbient f z * e :=
  @CornerCenter.transition_ambient_function

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter.transition (le_refl e) = RingHom.id (CornerCenter e) :=
  @CornerCenter.transition_refl

example : ∀ {A : Type 0} [NonUnitalRing A] {e f g : Idempotent A}
    (hef : e ≤ f) (hfg : f ≤ g),
    (CornerCenter.transition hef).comp (CornerCenter.transition hfg) =
      CornerCenter.transition (hef.trans hfg) :=
  @CornerCenter.transition_comp

example : ∀ (A : Type 0) [NonUnitalRing A],
    Subring (∀ e : Idempotent A, CornerCenter e) :=
  @coherentSubring

example : ∀ (A : Type 0) [NonUnitalRing A], Type 0 :=
  @Family

example : ∀ (A : Type 0) [NonUnitalRing A], CommRing (Family A) :=
  @Family.commRing

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    Family A →+* CornerCenter e :=
  @Family.coordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    (Family.coordinate e : Family A → CornerCenter e) = fun x => x.val e :=
  @Family.coordinate_function

example : ∀ {A : Type 0} [NonUnitalRing A] (_e : Idempotent A),
    Family A →ₙ+* A :=
  @Family.ambientCoordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    (Family.ambientCoordinate e : Family A → A) = fun x => (x.val e).val.val :=
  @Family.ambientCoordinate_function

example : ∀ {A : Type 0} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    (CornerCenter.transition h).comp (Family.coordinate f) = Family.coordinate e :=
  @Family.coordinate_transition

example : ∀ {A : Type 0} [NonUnitalRing A] {e f : Idempotent A} (_h : e ≤ f),
    (fun a : A => (e : A) * a * e) ∘ Family.ambientCoordinate f =
      Family.ambientCoordinate e :=
  @Family.ambientCoordinate_compatible_function

example : ∀ {A : Type 0} [NonUnitalRing A] {R : Type 1} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (_hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e), R →+* Family A :=
  @Family.lift

example : ∀ {A : Type 0} [NonUnitalRing A] {R : Type 1} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e) (e : Idempotent A),
    (Family.coordinate e).comp (Family.lift p hp) = p e :=
  @Family.coordinate_lift

example : ∀ {A : Type 0} [NonUnitalRing A] {R : Type 1} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e),
    Subtype.val ∘ Family.lift p hp = fun r e => p e r :=
  @Family.lift_coordinates_function

example : ∀ {A : Type 0} [NonUnitalRing A] {R : Type 1} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e)
    (q : R →+* Family A) (_hq : ∀ e, (Family.coordinate e).comp q = p e),
    q = Family.lift p hp :=
  @Family.lift_unique

example : ∀ (A : Type 0) [NonUnitalRing A],
    (Idempotent A)ᵒᵖ ⥤ CommRingCat.{0} :=
  @diagram

example : ∀ (A : Type 0) [NonUnitalRing A], Cone (diagram A) :=
  @cone

example : ∀ (A : Type 0) [NonUnitalRing A], IsLimit (cone A) :=
  @coneIsLimit

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    (CornerCenter.toAmbient e : CornerCenter e → A) = fun z => z.val.val :=
  @CornerCenter.toAmbient_function

example : ∀ {A : Type 0} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    CornerCenter.toCorner e ∘ CornerCenter.transition h = CornerCenter.sandwich h :=
  @CornerCenter.toCorner_transition_function

example : ∀ (A : Type 0) [NonUnitalRing A] (x : ∀ e : Idempotent A, CornerCenter e),
    x ∈ coherentSubring A ↔ ∀ (e f : Idempotent A) (h : e ≤ f),
      CornerCenter.transition h (x f) = x e :=
  @mem_coherentSubring

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    Family.coordinate e =
      (Pi.evalRingHom (fun d : Idempotent A => CornerCenter d) e).comp
        (coherentSubring A).subtype :=
  @Family.coordinate_eq_eval_comp_subtype

example : ∀ (A : Type 0) [NonUnitalRing A] (e : (Idempotent A)ᵒᵖ),
    (diagram A).obj e = CommRingCat.of (CornerCenter e.unop) :=
  @diagram_obj

example : ∀ (A : Type 0) [NonUnitalRing A] {e f : (Idempotent A)ᵒᵖ} (h : e ⟶ f),
    ((diagram A).map h).hom = CornerCenter.transition (leOfHom h.unop) :=
  @diagram_map_hom

example : ∀ (A : Type 0) [NonUnitalRing A],
    (cone A).pt = CommRingCat.of (Family A) :=
  @cone_pt

example : ∀ (A : Type 0) [NonUnitalRing A] (e : (Idempotent A)ᵒᵖ),
    ((cone A).π.app e).hom = Family.coordinate e.unop :=
  @cone_π_app_hom

example : ∀ {A : Type 0} [NonUnitalRing A] (s : Cone (diagram A))
    (e f : Idempotent A) (h : e ≤ f),
    (CornerCenter.transition h).comp (s.π.app (op f)).hom = (s.π.app (op e)).hom :=
  @cone_legs_compatible

example : ∀ (A : Type 0) [NonUnitalRing A] (s : Cone (diagram A)),
    ((coneIsLimit A).lift s).hom =
      Family.lift (fun e => (s.π.app (op e)).hom) (cone_legs_compatible s) :=
  @coneIsLimit_lift_hom

end UniverseZeroOne

section UniverseOneZero

example : ∀ {A : Type 1} [NonUnitalRing A], Idempotent A → Type 1 :=
  @Idempotent.CornerCenter

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    CommRing (CornerCenter e) :=
  @CornerCenter.commRing

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter e →+* Corner e :=
  @CornerCenter.toCorner

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter e →ₙ+* A :=
  @CornerCenter.toAmbient

example : ∀ {A : Type 1} [NonUnitalRing A] {e f : Idempotent A},
    e ≤ f → CornerCenter f →+* CornerCenter e :=
  @CornerCenter.transition

example : ∀ {A : Type 1} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    CornerCenter.toAmbient e ∘ CornerCenter.transition h =
      fun z => (e : A) * CornerCenter.toAmbient f z * e :=
  @CornerCenter.transition_ambient_function

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    CornerCenter.transition (le_refl e) = RingHom.id (CornerCenter e) :=
  @CornerCenter.transition_refl

example : ∀ {A : Type 1} [NonUnitalRing A] {e f g : Idempotent A}
    (hef : e ≤ f) (hfg : f ≤ g),
    (CornerCenter.transition hef).comp (CornerCenter.transition hfg) =
      CornerCenter.transition (hef.trans hfg) :=
  @CornerCenter.transition_comp

example : ∀ (A : Type 1) [NonUnitalRing A],
    Subring (∀ e : Idempotent A, CornerCenter e) :=
  @coherentSubring

example : ∀ (A : Type 1) [NonUnitalRing A], Type 1 :=
  @Family

example : ∀ (A : Type 1) [NonUnitalRing A], CommRing (Family A) :=
  @Family.commRing

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    Family A →+* CornerCenter e :=
  @Family.coordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    (Family.coordinate e : Family A → CornerCenter e) = fun x => x.val e :=
  @Family.coordinate_function

example : ∀ {A : Type 1} [NonUnitalRing A] (_e : Idempotent A),
    Family A →ₙ+* A :=
  @Family.ambientCoordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    (Family.ambientCoordinate e : Family A → A) = fun x => (x.val e).val.val :=
  @Family.ambientCoordinate_function

example : ∀ {A : Type 1} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    (CornerCenter.transition h).comp (Family.coordinate f) = Family.coordinate e :=
  @Family.coordinate_transition

example : ∀ {A : Type 1} [NonUnitalRing A] {e f : Idempotent A} (_h : e ≤ f),
    (fun a : A => (e : A) * a * e) ∘ Family.ambientCoordinate f =
      Family.ambientCoordinate e :=
  @Family.ambientCoordinate_compatible_function

example : ∀ {A : Type 1} [NonUnitalRing A] {R : Type 0} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (_hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e), R →+* Family A :=
  @Family.lift

example : ∀ {A : Type 1} [NonUnitalRing A] {R : Type 0} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e) (e : Idempotent A),
    (Family.coordinate e).comp (Family.lift p hp) = p e :=
  @Family.coordinate_lift

example : ∀ {A : Type 1} [NonUnitalRing A] {R : Type 0} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e),
    Subtype.val ∘ Family.lift p hp = fun r e => p e r :=
  @Family.lift_coordinates_function

example : ∀ {A : Type 1} [NonUnitalRing A] {R : Type 0} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e)
    (q : R →+* Family A) (_hq : ∀ e, (Family.coordinate e).comp q = p e),
    q = Family.lift p hp :=
  @Family.lift_unique

example : ∀ (A : Type 1) [NonUnitalRing A],
    (Idempotent A)ᵒᵖ ⥤ CommRingCat.{1} :=
  @diagram

example : ∀ (A : Type 1) [NonUnitalRing A], Cone (diagram A) :=
  @cone

example : ∀ (A : Type 1) [NonUnitalRing A], IsLimit (cone A) :=
  @coneIsLimit

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    (CornerCenter.toAmbient e : CornerCenter e → A) = fun z => z.val.val :=
  @CornerCenter.toAmbient_function

example : ∀ {A : Type 1} [NonUnitalRing A] {e f : Idempotent A} (h : e ≤ f),
    CornerCenter.toCorner e ∘ CornerCenter.transition h = CornerCenter.sandwich h :=
  @CornerCenter.toCorner_transition_function

example : ∀ (A : Type 1) [NonUnitalRing A] (x : ∀ e : Idempotent A, CornerCenter e),
    x ∈ coherentSubring A ↔ ∀ (e f : Idempotent A) (h : e ≤ f),
      CornerCenter.transition h (x f) = x e :=
  @mem_coherentSubring

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    Family.coordinate e =
      (Pi.evalRingHom (fun d : Idempotent A => CornerCenter d) e).comp
        (coherentSubring A).subtype :=
  @Family.coordinate_eq_eval_comp_subtype

example : ∀ (A : Type 1) [NonUnitalRing A] (e : (Idempotent A)ᵒᵖ),
    (diagram A).obj e = CommRingCat.of (CornerCenter e.unop) :=
  @diagram_obj

example : ∀ (A : Type 1) [NonUnitalRing A] {e f : (Idempotent A)ᵒᵖ} (h : e ⟶ f),
    ((diagram A).map h).hom = CornerCenter.transition (leOfHom h.unop) :=
  @diagram_map_hom

example : ∀ (A : Type 1) [NonUnitalRing A],
    (cone A).pt = CommRingCat.of (Family A) :=
  @cone_pt

example : ∀ (A : Type 1) [NonUnitalRing A] (e : (Idempotent A)ᵒᵖ),
    ((cone A).π.app e).hom = Family.coordinate e.unop :=
  @cone_π_app_hom

example : ∀ {A : Type 1} [NonUnitalRing A] (s : Cone (diagram A))
    (e f : Idempotent A) (h : e ≤ f),
    (CornerCenter.transition h).comp (s.π.app (op f)).hom = (s.π.app (op e)).hom :=
  @cone_legs_compatible

example : ∀ (A : Type 1) [NonUnitalRing A] (s : Cone (diagram A)),
    ((coneIsLimit A).lift s).hom =
      Family.lift (fun e => (s.π.app (op e)).hom) (cone_legs_compatible s) :=
  @coneIsLimit_lift_hom

end UniverseOneZero

/-! Explicit choices retain the original rings when competing instances coexist. -/
section CompetingAmbient

-- Both local instances are intentional in these checks.
set_option linter.overlappingInstances false

variable {A : Type uA} [originalAmbient : NonUnitalRing A]
  [competingAmbient : NonUnitalRing A]

example :
    letI := originalAmbient
    ∀ e : Idempotent A, CornerCenter e →ₙ+* A :=
  @CornerCenter.toAmbient A originalAmbient

example :
    letI := originalAmbient
    ∀ {e f : Idempotent A}, e ≤ f → CornerCenter f →+* CornerCenter e :=
  @CornerCenter.transition A originalAmbient

example :
    letI := originalAmbient
    ∀ {e f : Idempotent A} (h : e ≤ f),
      CornerCenter.toAmbient e ∘ CornerCenter.transition h =
        fun z => (e : A) * CornerCenter.toAmbient f z * e :=
  @CornerCenter.transition_ambient_function A originalAmbient

example :
    letI := originalAmbient
    ∀ _e : Idempotent A, Family A →ₙ+* A :=
  @Family.ambientCoordinate A originalAmbient

example :
    letI := originalAmbient
    (Idempotent A)ᵒᵖ ⥤ CommRingCat.{uA} :=
  @diagram A originalAmbient

end CompetingAmbient

section CompetingCornerAndFamily

variable {A : Type uA} [NonUnitalRing A] (e f : Idempotent A)
  [competingCornerRing : Ring (Corner e)]
  [competingCenterRing : CommRing (CornerCenter e)]
  [competingLargerCenterRing : CommRing (CornerCenter f)]
  [competingFamilyRing : CommRing (Family A)]

example :
    letI := Corner.ring e
    letI := CornerCenter.commRing e
    CornerCenter e →+* Corner e :=
  @CornerCenter.toCorner A _ e

example :
    letI := CornerCenter.commRing e
    CornerCenter e →ₙ+* A :=
  @CornerCenter.toAmbient A _ e

example :
    letI := CornerCenter.commRing e
    letI := CornerCenter.commRing f
    e ≤ f → CornerCenter f →+* CornerCenter e :=
  @CornerCenter.transition A _ e f

example :
    letI := CornerCenter.commRing e
    letI := Family.commRing A
    Family A →+* CornerCenter e :=
  @Family.coordinate A _ e

example :
    letI := Family.commRing A
    Family A →ₙ+* A :=
  @Family.ambientCoordinate A _ e

example :
    letI := CornerCenter.commRing e
    letI := Family.commRing A
    ∀ x y : Family A,
      Family.coordinate e (x * y) = Family.coordinate e x * Family.coordinate e y :=
  (Family.coordinate e).map_mul

example :
    (diagram A).obj (op e) = @CommRingCat.of (CornerCenter e) (CornerCenter.commRing e) := rfl

example :
    (cone A).pt = @CommRingCat.of (Family A) (Family.commRing A) := rfl

example : IsLimit (cone A) := coneIsLimit A

example :
    letI := Family.commRing A
    ∀ {R : Type uR} [Ring R]
      (p : ∀ d : Idempotent A, R →+* CornerCenter d)
      (_hp : ∀ (d g : Idempotent A) (h : d ≤ g),
        (CornerCenter.transition h).comp (p g) = p d), R →+* Family A :=
  @Family.lift A _

end CompetingCornerAndFamily

/-! The zero idempotent and subsingleton ambient ring require no exclusions. -/
section ZeroIdempotent

variable {A : Type uA} [NonUnitalRing A]

example :
    let e0 : Idempotent A := ⟨0, zero_mul 0⟩
    ∀ z : CornerCenter e0, CornerCenter.toAmbient e0 z = 0 := by
  intro e0 z
  change z.val.val = 0
  have hz := (mem_corner_iff e0 z.val.val).mp z.val.property
  simpa only [e0, zero_mul] using hz.1.symm

example :
    let e0 : Idempotent A := ⟨0, zero_mul 0⟩
    Subsingleton (CornerCenter e0) := by
  intro e0
  refine ⟨fun z w => CornerCenter.toAmbient_injective e0 ?_⟩
  have hz := (mem_corner_iff e0 z.val.val).mp z.val.property
  have hw := (mem_corner_iff e0 w.val.val).mp w.val.property
  change z.val.val = w.val.val
  rw [← hz.1, ← hw.1]
  simp only [e0, zero_mul]

example :
    let e0 : Idempotent A := ⟨0, zero_mul 0⟩
    ∀ f : Idempotent A, e0 ≤ f := by
  intro e0 f
  apply (le_iff_mul e0 f).mpr
  simp only [e0, mul_zero, zero_mul, and_self]

example :
    let e0 : Idempotent A := ⟨0, zero_mul 0⟩
    ∀ (f : Idempotent A) (h : e0 ≤ f),
      (CornerCenter.toAmbient e0 ∘ CornerCenter.transition h) = fun _ => (0 : A) := by
  intro e0 f h
  rw [CornerCenter.transition_ambient_function]
  funext z
  simp only [e0, zero_mul]

example :
    let e0 : Idempotent A := ⟨0, zero_mul 0⟩
    (Family.ambientCoordinate e0 : Family A → A) = fun _ => (0 : A) := by
  intro e0
  funext x
  change (x.val e0).val.val = 0
  have hx := (mem_corner_iff e0 (x.val e0).val.val).mp (x.val e0).val.property
  simpa only [e0, zero_mul] using hx.1.symm

end ZeroIdempotent

section ZeroAmbient

variable {A : Type uA} [NonUnitalRing A] [Subsingleton A]

example (e : Idempotent A) : Subsingleton (CornerCenter e) :=
  ⟨fun _z _w => CornerCenter.toAmbient_injective e (Subsingleton.elim _ _)⟩

example : Subsingleton (Family A) :=
  ⟨fun _x _y => Family.ext (fun e =>
    CornerCenter.toAmbient_injective e (Subsingleton.elim _ _))⟩

example : (1 : Family A) = 0 := by
  apply Family.ext
  intro e
  exact CornerCenter.toAmbient_injective e (Subsingleton.elim _ _)

example (e f : Idempotent A) (h : e ≤ f) :
    (CornerCenter.toAmbient e ∘ CornerCenter.transition h) = fun _ => (0 : A) := by
  funext z
  exact Subsingleton.elim _ _

example {R : Type uR} [Ring R]
    (p : ∀ e : Idempotent A, R →+* CornerCenter e)
    (hp : ∀ (e f : Idempotent A) (h : e ≤ f),
      (CornerCenter.transition h).comp (p f) = p e) (r : R) :
    Family.lift p hp r = 0 := by
  apply Family.ext
  intro e
  exact CornerCenter.toAmbient_injective e (Subsingleton.elim _ _)

example : IsLimit (cone A) := coneIsLimit A

end ZeroAmbient

end IdempotentedRingCornerCenter

end Langlands.Algebra
