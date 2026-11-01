import Langlands.Algebra.IdempotentedRingRightLimitRing
import Langlands.Algebra.IdempotentedRingCornerCenter

/-!
# The completed-ring centre and its corner-centre comparison maps

Renard (9 July 2026), I.1.7, printed p.13/PDF19. The actual centre of the
published ring of right-compatible families, the coordinates `z ↦ z(e)` of
its elements as central elements of the corners, and the converse map from
coherent families of corner-central elements. Mutual inverse identities and
the categorical centre are not treated here.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA

namespace IdempotentedRingRightLimit

open Idempotent IdempotentedRingCornerCenter

variable {A : Type uA} [NonUnitalRing A]

/-- The actual centre of the published completed ring `ring hA`. -/
def centerSubring (hA : IsIdempotented A) :
    letI := ring hA
    Subring (IdempotentedRingRightLimit A) :=
  letI := ring hA
  Subring.center (IdempotentedRingRightLimit A)

theorem centerSubring_eq (hA : IsIdempotented A) :
    letI := ring hA
    centerSubring hA = Subring.center (IdempotentedRingRightLimit A) := rfl

theorem coe_centerSubring (hA : IsIdempotented A) :
    letI := ring hA
    (centerSubring hA : Set (IdempotentedRingRightLimit A)) =
      Set.center (IdempotentedRingRightLimit A) := rfl

/-- Membership, with the named ring's multiplication. -/
theorem mem_centerSubring_iff_mul (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A) :
    letI := ring hA
    z ∈ centerSubring hA ↔ ∀ y : IdempotentedRingRightLimit A, y * z = z * y :=
  @Subring.mem_center_iff _ (ring hA) z

/-- Membership is commutation with every compatible right family under the
actual product. -/
theorem mem_centerSubring_iff (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A) :
    letI := ring hA
    z ∈ centerSubring hA ↔
      ∀ y : IdempotentedRingRightLimit A, product hA y z = product hA z y :=
  mem_centerSubring_iff_mul hA z

/-- The actual subtype of central compatible right families. -/
def Center (hA : IsIdempotented A) := ↥(centerSubring hA)

namespace Center

/-- The commutative ring inherited from the actual centre. -/
instance commRing (hA : IsIdempotented A) : CommRing (Center hA) :=
  inferInstanceAs
    (CommRing ↥(@Subring.center (IdempotentedRingRightLimit A) (ring hA).toNonAssocRing))

theorem carrier_eq (hA : IsIdempotented A) : Center hA = ↥(centerSubring hA) := rfl

/-- The canonical unital inclusion into the completed ring. -/
def inclusion (hA : IsIdempotented A) :
    letI := ring hA
    Center hA →+* IdempotentedRingRightLimit A :=
  letI := ring hA
  (Subring.center (IdempotentedRingRightLimit A)).subtype

@[simp] theorem inclusion_apply (hA : IsIdempotented A) (z : Center hA) :
    inclusion hA z = z.val := rfl

/-- The entire inclusion function is the subtype value. -/
theorem inclusion_function (hA : IsIdempotented A) :
    (inclusion hA : Center hA → IdempotentedRingRightLimit A) = Subtype.val := rfl

theorem inclusion_injective (hA : IsIdempotented A) :
    Function.Injective (inclusion hA) :=
  Subtype.val_injective

/-- The centre's multiplication is the actual completed product. -/
@[simp] theorem mul_val (hA : IsIdempotented A) (z w : Center hA) :
    (z * w).val = product hA z.val w.val := rfl

/-- The centre's unit is the actual completed unit `e ↦ e`. -/
@[simp] theorem one_val (hA : IsIdempotented A) :
    (1 : Center hA).val = unit := rfl

/-- The centre's addition is the original pointwise addition of families. -/
@[simp] theorem add_val (hA : IsIdempotented A) (z w : Center hA) :
    (z + w).val = z.val + w.val := rfl

@[ext] theorem ext {hA : IsIdempotented A} {z w : Center hA}
    (h : ∀ e : Idempotent A, z.val.val e = w.val.val e) : z = w :=
  Subtype.ext (Subtype.ext (funext h))

/-- A central family commutes with every compatible right family. -/
theorem product_comm (hA : IsIdempotented A) (z : Center hA)
    (y : IdempotentedRingRightLimit A) :
    product hA y z.val = product hA z.val y :=
  (mem_centerSubring_iff hA z.val).mp z.property y

/-- Commuting with `canonical e` makes each coordinate left-supported by `e`. -/
theorem left_support (hA : IsIdempotented A) (z : Center hA) (e : Idempotent A) :
    (e : A) * z.val.val e = z.val.val e := by
  have h := congrArg (fun x : IdempotentedRingRightLimit A => x.val e)
    (product_comm hA z (canonical (e : A)))
  change applyOriginal hA (canonical (e : A)) (z.val.val e) =
    applyOriginal hA z.val ((e : A) * e) at h
  rw [canonical_applyOriginal, e.property.eq, applyOriginal_idempotent] at h
  exact h

/-- Each coordinate lies in the actual corner `eAe`. -/
theorem coordinate_mem_corner (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A) : z.val.val e ∈ e.corner :=
  (mem_corner_iff e _).mpr ⟨left_support hA z e, z.val.property.1 e⟩

/-- Commuting with `canonical a`, `a ∈ eAe`, makes the coordinate commute with `a`. -/
theorem commute_corner (hA : IsIdempotented A) (z : Center hA) (e : Idempotent A)
    (a : A) (ha : a ∈ e.corner) : a * z.val.val e = z.val.val e * a := by
  obtain ⟨hea, hae⟩ := (mem_corner_iff e a).mp ha
  have h := congrArg (fun x : IdempotentedRingRightLimit A => x.val e)
    (product_comm hA z (canonical a))
  change applyOriginal hA (canonical a) (z.val.val e) =
    applyOriginal hA z.val (a * e) at h
  rw [canonical_applyOriginal, hae, applyOriginal_eq hA z.val a e hea] at h
  exact h

/-- The coordinate as an element of the published unital corner. -/
def cornerCoordinate (hA : IsIdempotented A) (z : Center hA) (e : Idempotent A) :
    Corner e :=
  ⟨z.val.val e, coordinate_mem_corner hA z e⟩

@[simp] theorem cornerCoordinate_ambient (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A) : Corner.toAmbient e (cornerCoordinate hA z e) = z.val.val e :=
  rfl

/-- The coordinate is central in the actual corner ring. -/
theorem cornerCoordinate_mem_center (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A) : cornerCoordinate hA z e ∈ Subring.center (Corner e) := by
  apply Subring.mem_center_iff.mpr
  intro a
  apply Corner.toAmbient_injective e
  change a.val * z.val.val e = z.val.val e * a.val
  exact commute_corner hA z e a.val a.property

/-- The source's `e z e = z(e)`, bundled as a unital ring homomorphism. -/
def coordinate (hA : IsIdempotented A) (e : Idempotent A) :
    Center hA →+* CornerCenter e where
  toFun z := ⟨cornerCoordinate hA z e, cornerCoordinate_mem_center hA z e⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' z w := by
    apply CornerCenter.toAmbient_injective e
    change (product hA z.val w.val).val e = z.val.val e * w.val.val e
    exact product_val hA z.val w.val e e (left_support hA w e)

@[simp] theorem coordinate_ambient (hA : IsIdempotented A) (e : Idempotent A)
    (z : Center hA) : CornerCenter.toAmbient e (coordinate hA e z) = z.val.val e := rfl

@[simp] theorem toCorner_coordinate (hA : IsIdempotented A) (e : Idempotent A)
    (z : Center hA) : CornerCenter.toCorner e (coordinate hA e z) =
      cornerCoordinate hA z e := rfl

/-- The entire coordinate function, as dependent subtype values. -/
theorem coordinate_function (hA : IsIdempotented A) (e : Idempotent A) :
    (coordinate hA e : Center hA → CornerCenter e) =
      fun z => ⟨cornerCoordinate hA z e, cornerCoordinate_mem_center hA z e⟩ := rfl

/-- The entire ambient coordinate function. -/
theorem coordinate_ambient_function (hA : IsIdempotented A) (e : Idempotent A) :
    CornerCenter.toAmbient e ∘ coordinate hA e = fun z => z.val.val e := rfl

/-- The coordinate in `e A e` is the sandwich `e z(e) e` of the family's coordinate. -/
theorem coordinate_ambient_sandwich (hA : IsIdempotented A) (e : Idempotent A)
    (z : Center hA) :
    CornerCenter.toAmbient e (coordinate hA e z) = (e : A) * z.val.val e * e :=
  (coordinate_mem_corner hA z e).symm

/-- Compatibility with each centre-only transition, as equality of entire maps. -/
theorem transition_comp_coordinate (hA : IsIdempotented A) {e f : Idempotent A}
    (h : e ≤ f) :
    (CornerCenter.transition h).comp (coordinate hA f) = coordinate hA e := by
  ext z
  apply CornerCenter.toAmbient_injective e
  change (e : A) * z.val.val f * e = z.val.val e
  rw [mul_assoc, z.val.property.2 e f h, left_support hA z e]

/-- The coordinates bundled into the published coherent-family ring. -/
def toFamily (hA : IsIdempotented A) : Center hA →+* Family A :=
  Family.lift (coordinate hA) (fun _ _ h => transition_comp_coordinate hA h)

/-- Each published coordinate of the bundled map, as equality of entire maps. -/
@[simp] theorem coordinate_comp_toFamily (hA : IsIdempotented A) (e : Idempotent A) :
    (Family.coordinate e).comp (toFamily hA) = coordinate hA e := rfl

@[simp] theorem toFamily_val (hA : IsIdempotented A) (z : Center hA) (e : Idempotent A) :
    (toFamily hA z).val e = coordinate hA e z := rfl

/-- The entire dependent coordinate function of the bundled map. -/
theorem toFamily_function (hA : IsIdempotented A) :
    Subtype.val ∘ toFamily hA = fun z e => coordinate hA e z := rfl

/-- The ambient coordinate of a central family, as a nonunital ring homomorphism. -/
def ambientCoordinate (hA : IsIdempotented A) (e : Idempotent A) : Center hA →ₙ+* A :=
  (CornerCenter.toAmbient e).comp (coordinate hA e).toNonUnitalRingHom

@[simp] theorem ambientCoordinate_apply (hA : IsIdempotented A) (e : Idempotent A)
    (z : Center hA) : ambientCoordinate hA e z = z.val.val e := rfl

theorem ambientCoordinate_function (hA : IsIdempotented A) (e : Idempotent A) :
    (ambientCoordinate hA e : Center hA → A) = fun z => z.val.val e := rfl

/-- The published ambient coordinate after the bundled map, as equality of entire maps. -/
@[simp] theorem ambientCoordinate_comp_toFamily (hA : IsIdempotented A) (e : Idempotent A) :
    (Family.ambientCoordinate e).comp (toFamily hA).toNonUnitalRingHom =
      ambientCoordinate hA e := rfl

/-- The entire composite function with the published ambient coordinate. -/
theorem ambientCoordinate_toFamily_function (hA : IsIdempotented A) (e : Idempotent A) :
    (Family.ambientCoordinate e : Family A → A) ∘ toFamily hA = fun z => z.val.val e :=
  rfl

end Center
end IdempotentedRingRightLimit

namespace IdempotentedRingCornerCenter
namespace Family

open Idempotent IdempotentedRingRightLimit

variable {A : Type uA} [NonUnitalRing A]

/-- Corner membership: every ambient coordinate is left-supported by its idempotent. -/
theorem ambientCoordinate_left_support (e : Idempotent A) (x : Family A) :
    (e : A) * ambientCoordinate e x = ambientCoordinate e x :=
  ((mem_corner_iff e _).mp (x.val e).val.property).1

/-- Corner membership: every ambient coordinate is right-supported by its idempotent. -/
theorem ambientCoordinate_right_support (e : Idempotent A) (x : Family A) :
    ambientCoordinate e x * (e : A) = ambientCoordinate e x :=
  ((mem_corner_iff e _).mp (x.val e).val.property).2

/-- Sandwich coherence and centrality give right compatibility. -/
theorem ambientCoordinate_mul_of_le {e f : Idempotent A} (h : e ≤ f) (x : Family A) :
    ambientCoordinate f x * (e : A) = ambientCoordinate e x :=
  calc ambientCoordinate f x * (e : A) = (e : A) * ambientCoordinate f x :=
        CornerCenter.ambient_commute_idempotent h (x.val f)
    _ = (e : A) * ambientCoordinate f x * e :=
        (CornerCenter.sandwich_ambient_eq_left h (x.val f)).symm
    _ = ambientCoordinate e x := ambientCoordinate_compatible h x

/-- The actual right-compatible family with coordinates `(x.val e).val.val`. -/
def toRightLimit (x : Family A) : IdempotentedRingRightLimit A :=
  ⟨fun e => (x.val e).val.val, by
    constructor
    · intro e
      exact ambientCoordinate_right_support e x
    · intro e f h
      exact ambientCoordinate_mul_of_le h x⟩

@[simp] theorem toRightLimit_val (x : Family A) (e : Idempotent A) :
    (toRightLimit x).val e = (x.val e).val.val := rfl

/-- The entire underlying coordinate function. -/
theorem toRightLimit_function :
    (fun x : Family A => (toRightLimit x).val) = fun x e => (x.val e).val.val := rfl

/-- Multiplicativity, computed with the source product formula at `f = e`. -/
theorem toRightLimit_mul (hA : IsIdempotented A) (x y : Family A) :
    toRightLimit (x * y) = product hA (toRightLimit x) (toRightLimit y) := by
  apply Subtype.ext
  funext e
  exact (product_val hA (toRightLimit x) (toRightLimit y) e e
    (ambientCoordinate_left_support e y)).symm

/-- Every central corner family commutes with every compatible right family:
use a two-sided local unit `f` for `e` and `y(e)`. -/
theorem product_toRightLimit_comm (hA : IsIdempotented A) (x : Family A)
    (y : IdempotentedRingRightLimit A) :
    product hA y (toRightLimit x) = product hA (toRightLimit x) y := by
  classical
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {(e : A), y.val e}
  have hfe := hf (e : A) (by simp)
  have hfy := hf (y.val e) (by simp)
  have hef : e ≤ f := (le_iff_mul e f).mpr hfe
  have hcomm := CornerCenter.ambient_commute f (x.val f)
    ⟨y.val e, (mem_corner_iff f _).mpr hfy⟩
  change ambientCoordinate f x * y.val e = y.val e * ambientCoordinate f x at hcomm
  change (product hA y (toRightLimit x)).val e = (product hA (toRightLimit x) y).val e
  rw [product_val hA y (toRightLimit x) e e (ambientCoordinate_left_support e x),
    product_val hA (toRightLimit x) y e f hfy.1]
  calc y.val e * ambientCoordinate e x
      = y.val e * (ambientCoordinate f x * e) := by
        rw [ambientCoordinate_mul_of_le hef x]
    _ = y.val e * ((e : A) * ambientCoordinate f x) :=
        congrArg (y.val e * ·) (CornerCenter.ambient_commute_idempotent hef (x.val f))
    _ = (y.val e * e) * ambientCoordinate f x := (mul_assoc _ _ _).symm
    _ = y.val e * ambientCoordinate f x := by rw [y.property.1 e]
    _ = ambientCoordinate f x * y.val e := hcomm.symm

/-- The family lies in the actual centre of the completed ring. -/
theorem toRightLimit_mem_centerSubring (hA : IsIdempotented A) (x : Family A) :
    toRightLimit x ∈ centerSubring hA :=
  (mem_centerSubring_iff hA (toRightLimit x)).mpr (product_toRightLimit_comm hA x)

/-- The construction as a unital ring homomorphism into the completed ring. -/
def toRightLimitRingHom (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    Family A →+* IdempotentedRingRightLimit A :=
  letI := IdempotentedRingRightLimit.ring hA
  { toFun := toRightLimit
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := toRightLimit_mul hA }

@[simp] theorem toRightLimitRingHom_apply (hA : IsIdempotented A) (x : Family A) :
    toRightLimitRingHom hA x = toRightLimit x := rfl

theorem toRightLimitRingHom_function (hA : IsIdempotented A) :
    (toRightLimitRingHom hA : Family A → IdempotentedRingRightLimit A) = toRightLimit :=
  rfl

/-- The comparison map from the coherent families to the completed-ring centre. -/
def toCenter (hA : IsIdempotented A) : Family A →+* Center hA where
  toFun x := ⟨toRightLimit x, toRightLimit_mem_centerSubring hA x⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' x y := Subtype.ext (toRightLimit_mul hA x y)

@[simp] theorem toCenter_val (hA : IsIdempotented A) (x : Family A) :
    (toCenter hA x).val = toRightLimit x := rfl

/-- Pointwise coordinate formula. -/
@[simp] theorem toCenter_coordinate (hA : IsIdempotented A) (x : Family A)
    (e : Idempotent A) : (toCenter hA x).val.val e = (x.val e).val.val := rfl

/-- The entire underlying coordinate function. -/
theorem toCenter_function (hA : IsIdempotented A) :
    (fun x : Family A => (toCenter hA x).val.val) = fun x e => (x.val e).val.val := rfl

@[simp] theorem inclusion_toCenter (hA : IsIdempotented A) (x : Family A) :
    Center.inclusion hA (toCenter hA x) = toRightLimit x := rfl

/-- The whole map after the centre inclusion, as functions. -/
theorem inclusion_comp_toCenter_function (hA : IsIdempotented A) :
    (Center.inclusion hA : Center hA → IdempotentedRingRightLimit A) ∘ toCenter hA =
      toRightLimit := rfl

/-- The whole map after the centre inclusion, as unital ring homomorphisms. -/
theorem inclusion_comp_toCenter (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    (Center.inclusion hA).comp (toCenter hA) = toRightLimitRingHom hA := rfl

end Family
end IdempotentedRingCornerCenter

/-! Complete unapplied interfaces preserve their original telescopes and universes. -/

open Idempotent IdempotentedRingRightLimit IdempotentedRingCornerCenter

section ArbitraryUniverse

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Subring (IdempotentedRingRightLimit A) :=
  @centerSubring

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    centerSubring hA = Subring.center (IdempotentedRingRightLimit A) :=
  @centerSubring_eq

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    (centerSubring hA : Set (IdempotentedRingRightLimit A)) =
      Set.center (IdempotentedRingRightLimit A) :=
  @coe_centerSubring

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A),
    letI := ring hA
    z ∈ centerSubring hA ↔ ∀ y : IdempotentedRingRightLimit A, y * z = z * y :=
  @mem_centerSubring_iff_mul

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A),
    letI := ring hA
    z ∈ centerSubring hA ↔
      ∀ y : IdempotentedRingRightLimit A, product hA y z = product hA z y :=
  @mem_centerSubring_iff

example : ∀ {A : Type uA} [NonUnitalRing A], IsIdempotented A → Type uA :=
  @Center

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A), CommRing (Center hA) :=
  @Center.commRing

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    Center hA = ↥(centerSubring hA) :=
  @Center.carrier_eq

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Center hA →+* IdempotentedRingRightLimit A :=
  @Center.inclusion

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA),
    Center.inclusion hA z = z.val :=
  @Center.inclusion_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    (Center.inclusion hA : Center hA → IdempotentedRingRightLimit A) = Subtype.val :=
  @Center.inclusion_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    Function.Injective (Center.inclusion hA) :=
  @Center.inclusion_injective

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z w : Center hA),
    (z * w).val = product hA z.val w.val :=
  @Center.mul_val

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    (1 : Center hA).val = unit :=
  @Center.one_val

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z w : Center hA),
    (z + w).val = z.val + w.val :=
  @Center.add_val

example : ∀ {A : Type uA} [NonUnitalRing A] {hA : IsIdempotented A} {z w : Center hA},
    (∀ e : Idempotent A, z.val.val e = w.val.val e) → z = w :=
  @Center.ext

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (y : IdempotentedRingRightLimit A), product hA y z.val = product hA z.val y :=
  @Center.product_comm

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), (e : A) * z.val.val e = z.val.val e :=
  @Center.left_support

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), z.val.val e ∈ e.corner :=
  @Center.coordinate_mem_corner

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A) (a : A), a ∈ e.corner → a * z.val.val e = z.val.val e * a :=
  @Center.commute_corner

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    Center hA → ∀ e : Idempotent A, Corner e :=
  @Center.cornerCoordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), Corner.toAmbient e (Center.cornerCoordinate hA z e) = z.val.val e :=
  @Center.cornerCoordinate_ambient

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), Center.cornerCoordinate hA z e ∈ Subring.center (Corner e) :=
  @Center.cornerCoordinate_mem_center

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A), Center hA →+* CornerCenter e :=
  @Center.coordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toAmbient e (Center.coordinate hA e z) = z.val.val e :=
  @Center.coordinate_ambient

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toCorner e (Center.coordinate hA e z) = Center.cornerCoordinate hA z e :=
  @Center.toCorner_coordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Center.coordinate hA e : Center hA → CornerCenter e) =
      fun z => ⟨Center.cornerCoordinate hA z e, Center.cornerCoordinate_mem_center hA z e⟩ :=
  @Center.coordinate_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    CornerCenter.toAmbient e ∘ Center.coordinate hA e = fun z => z.val.val e :=
  @Center.coordinate_ambient_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toAmbient e (Center.coordinate hA e z) = (e : A) * z.val.val e * e :=
  @Center.coordinate_ambient_sandwich

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    {e f : Idempotent A} (h : e ≤ f),
    (CornerCenter.transition h).comp (Center.coordinate hA f) = Center.coordinate hA e :=
  @Center.transition_comp_coordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A), Center hA →+* Family A :=
  @Center.toFamily

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.coordinate e).comp (Center.toFamily hA) = Center.coordinate hA e :=
  @Center.coordinate_comp_toFamily

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), (Center.toFamily hA z).val e = Center.coordinate hA e z :=
  @Center.toFamily_val

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    Subtype.val ∘ Center.toFamily hA = fun z e => Center.coordinate hA e z :=
  @Center.toFamily_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (_e : Idempotent A), Center hA →ₙ+* A :=
  @Center.ambientCoordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA), Center.ambientCoordinate hA e z = z.val.val e :=
  @Center.ambientCoordinate_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Center.ambientCoordinate hA e : Center hA → A) = fun z => z.val.val e :=
  @Center.ambientCoordinate_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.ambientCoordinate e).comp (Center.toFamily hA).toNonUnitalRingHom =
      Center.ambientCoordinate hA e :=
  @Center.ambientCoordinate_comp_toFamily

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.ambientCoordinate e : Family A → A) ∘ Center.toFamily hA = fun z => z.val.val e :=
  @Center.ambientCoordinate_toFamily_function

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A) (x : Family A),
    (e : A) * Family.ambientCoordinate e x = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_left_support

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A) (x : Family A),
    Family.ambientCoordinate e x * (e : A) = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_right_support

example : ∀ {A : Type uA} [NonUnitalRing A] {e f : Idempotent A} (_h : e ≤ f)
    (x : Family A), Family.ambientCoordinate f x * (e : A) = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_mul_of_le

example : ∀ {A : Type uA} [NonUnitalRing A], Family A → IdempotentedRingRightLimit A :=
  @Family.toRightLimit

example : ∀ {A : Type uA} [NonUnitalRing A] (x : Family A) (e : Idempotent A),
    (Family.toRightLimit x).val e = (x.val e).val.val :=
  @Family.toRightLimit_val

example : ∀ {A : Type uA} [NonUnitalRing A],
    (fun x : Family A => (Family.toRightLimit x).val) = fun x e => (x.val e).val.val :=
  @Family.toRightLimit_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (x y : Family A),
    Family.toRightLimit (x * y) =
      product hA (Family.toRightLimit x) (Family.toRightLimit y) :=
  @Family.toRightLimit_mul

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A)
    (y : IdempotentedRingRightLimit A),
    product hA y (Family.toRightLimit x) = product hA (Family.toRightLimit x) y :=
  @Family.product_toRightLimit_comm

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Family.toRightLimit x ∈ centerSubring hA :=
  @Family.toRightLimit_mem_centerSubring

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Family A →+* IdempotentedRingRightLimit A :=
  @Family.toRightLimitRingHom

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Family.toRightLimitRingHom hA x = Family.toRightLimit x :=
  @Family.toRightLimitRingHom_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    (Family.toRightLimitRingHom hA : Family A → IdempotentedRingRightLimit A) =
      Family.toRightLimit :=
  @Family.toRightLimitRingHom_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A), Family A →+* Center hA :=
  @Family.toCenter

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    (Family.toCenter hA x).val = Family.toRightLimit x :=
  @Family.toCenter_val

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A)
    (e : Idempotent A), (Family.toCenter hA x).val.val e = (x.val e).val.val :=
  @Family.toCenter_coordinate

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    (fun x : Family A => (Family.toCenter hA x).val.val) = fun x e => (x.val e).val.val :=
  @Family.toCenter_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Center.inclusion hA (Family.toCenter hA x) = Family.toRightLimit x :=
  @Family.inclusion_toCenter

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    (Center.inclusion hA : Center hA → IdempotentedRingRightLimit A) ∘ Family.toCenter hA =
      Family.toRightLimit :=
  @Family.inclusion_comp_toCenter_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    (Center.inclusion hA).comp (Family.toCenter hA) = Family.toRightLimitRingHom hA :=
  @Family.inclusion_comp_toCenter

end ArbitraryUniverse

section UniverseZero

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Subring (IdempotentedRingRightLimit A) :=
  @centerSubring

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    centerSubring hA = Subring.center (IdempotentedRingRightLimit A) :=
  @centerSubring_eq

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    (centerSubring hA : Set (IdempotentedRingRightLimit A)) =
      Set.center (IdempotentedRingRightLimit A) :=
  @coe_centerSubring

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A),
    letI := ring hA
    z ∈ centerSubring hA ↔ ∀ y : IdempotentedRingRightLimit A, y * z = z * y :=
  @mem_centerSubring_iff_mul

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A),
    letI := ring hA
    z ∈ centerSubring hA ↔
      ∀ y : IdempotentedRingRightLimit A, product hA y z = product hA z y :=
  @mem_centerSubring_iff

example : ∀ {A : Type 0} [NonUnitalRing A], IsIdempotented A → Type 0 :=
  @Center

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A), CommRing (Center hA) :=
  @Center.commRing

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    Center hA = ↥(centerSubring hA) :=
  @Center.carrier_eq

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Center hA →+* IdempotentedRingRightLimit A :=
  @Center.inclusion

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA),
    Center.inclusion hA z = z.val :=
  @Center.inclusion_apply

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    (Center.inclusion hA : Center hA → IdempotentedRingRightLimit A) = Subtype.val :=
  @Center.inclusion_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    Function.Injective (Center.inclusion hA) :=
  @Center.inclusion_injective

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z w : Center hA),
    (z * w).val = product hA z.val w.val :=
  @Center.mul_val

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    (1 : Center hA).val = unit :=
  @Center.one_val

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z w : Center hA),
    (z + w).val = z.val + w.val :=
  @Center.add_val

example : ∀ {A : Type 0} [NonUnitalRing A] {hA : IsIdempotented A} {z w : Center hA},
    (∀ e : Idempotent A, z.val.val e = w.val.val e) → z = w :=
  @Center.ext

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (y : IdempotentedRingRightLimit A), product hA y z.val = product hA z.val y :=
  @Center.product_comm

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), (e : A) * z.val.val e = z.val.val e :=
  @Center.left_support

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), z.val.val e ∈ e.corner :=
  @Center.coordinate_mem_corner

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A) (a : A), a ∈ e.corner → a * z.val.val e = z.val.val e * a :=
  @Center.commute_corner

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    Center hA → ∀ e : Idempotent A, Corner e :=
  @Center.cornerCoordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), Corner.toAmbient e (Center.cornerCoordinate hA z e) = z.val.val e :=
  @Center.cornerCoordinate_ambient

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), Center.cornerCoordinate hA z e ∈ Subring.center (Corner e) :=
  @Center.cornerCoordinate_mem_center

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A), Center hA →+* CornerCenter e :=
  @Center.coordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toAmbient e (Center.coordinate hA e z) = z.val.val e :=
  @Center.coordinate_ambient

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toCorner e (Center.coordinate hA e z) = Center.cornerCoordinate hA z e :=
  @Center.toCorner_coordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Center.coordinate hA e : Center hA → CornerCenter e) =
      fun z => ⟨Center.cornerCoordinate hA z e, Center.cornerCoordinate_mem_center hA z e⟩ :=
  @Center.coordinate_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    CornerCenter.toAmbient e ∘ Center.coordinate hA e = fun z => z.val.val e :=
  @Center.coordinate_ambient_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toAmbient e (Center.coordinate hA e z) = (e : A) * z.val.val e * e :=
  @Center.coordinate_ambient_sandwich

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    {e f : Idempotent A} (h : e ≤ f),
    (CornerCenter.transition h).comp (Center.coordinate hA f) = Center.coordinate hA e :=
  @Center.transition_comp_coordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A), Center hA →+* Family A :=
  @Center.toFamily

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.coordinate e).comp (Center.toFamily hA) = Center.coordinate hA e :=
  @Center.coordinate_comp_toFamily

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), (Center.toFamily hA z).val e = Center.coordinate hA e z :=
  @Center.toFamily_val

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    Subtype.val ∘ Center.toFamily hA = fun z e => Center.coordinate hA e z :=
  @Center.toFamily_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (_e : Idempotent A), Center hA →ₙ+* A :=
  @Center.ambientCoordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA), Center.ambientCoordinate hA e z = z.val.val e :=
  @Center.ambientCoordinate_apply

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Center.ambientCoordinate hA e : Center hA → A) = fun z => z.val.val e :=
  @Center.ambientCoordinate_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.ambientCoordinate e).comp (Center.toFamily hA).toNonUnitalRingHom =
      Center.ambientCoordinate hA e :=
  @Center.ambientCoordinate_comp_toFamily

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.ambientCoordinate e : Family A → A) ∘ Center.toFamily hA = fun z => z.val.val e :=
  @Center.ambientCoordinate_toFamily_function

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A) (x : Family A),
    (e : A) * Family.ambientCoordinate e x = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_left_support

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A) (x : Family A),
    Family.ambientCoordinate e x * (e : A) = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_right_support

example : ∀ {A : Type 0} [NonUnitalRing A] {e f : Idempotent A} (_h : e ≤ f)
    (x : Family A), Family.ambientCoordinate f x * (e : A) = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_mul_of_le

example : ∀ {A : Type 0} [NonUnitalRing A], Family A → IdempotentedRingRightLimit A :=
  @Family.toRightLimit

example : ∀ {A : Type 0} [NonUnitalRing A] (x : Family A) (e : Idempotent A),
    (Family.toRightLimit x).val e = (x.val e).val.val :=
  @Family.toRightLimit_val

example : ∀ {A : Type 0} [NonUnitalRing A],
    (fun x : Family A => (Family.toRightLimit x).val) = fun x e => (x.val e).val.val :=
  @Family.toRightLimit_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (x y : Family A),
    Family.toRightLimit (x * y) =
      product hA (Family.toRightLimit x) (Family.toRightLimit y) :=
  @Family.toRightLimit_mul

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A)
    (y : IdempotentedRingRightLimit A),
    product hA y (Family.toRightLimit x) = product hA (Family.toRightLimit x) y :=
  @Family.product_toRightLimit_comm

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Family.toRightLimit x ∈ centerSubring hA :=
  @Family.toRightLimit_mem_centerSubring

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Family A →+* IdempotentedRingRightLimit A :=
  @Family.toRightLimitRingHom

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Family.toRightLimitRingHom hA x = Family.toRightLimit x :=
  @Family.toRightLimitRingHom_apply

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    (Family.toRightLimitRingHom hA : Family A → IdempotentedRingRightLimit A) =
      Family.toRightLimit :=
  @Family.toRightLimitRingHom_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A), Family A →+* Center hA :=
  @Family.toCenter

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    (Family.toCenter hA x).val = Family.toRightLimit x :=
  @Family.toCenter_val

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A)
    (e : Idempotent A), (Family.toCenter hA x).val.val e = (x.val e).val.val :=
  @Family.toCenter_coordinate

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    (fun x : Family A => (Family.toCenter hA x).val.val) = fun x e => (x.val e).val.val :=
  @Family.toCenter_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Center.inclusion hA (Family.toCenter hA x) = Family.toRightLimit x :=
  @Family.inclusion_toCenter

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    (Center.inclusion hA : Center hA → IdempotentedRingRightLimit A) ∘ Family.toCenter hA =
      Family.toRightLimit :=
  @Family.inclusion_comp_toCenter_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    (Center.inclusion hA).comp (Family.toCenter hA) = Family.toRightLimitRingHom hA :=
  @Family.inclusion_comp_toCenter

end UniverseZero

section UniverseOne

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Subring (IdempotentedRingRightLimit A) :=
  @centerSubring

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    centerSubring hA = Subring.center (IdempotentedRingRightLimit A) :=
  @centerSubring_eq

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    (centerSubring hA : Set (IdempotentedRingRightLimit A)) =
      Set.center (IdempotentedRingRightLimit A) :=
  @coe_centerSubring

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A),
    letI := ring hA
    z ∈ centerSubring hA ↔ ∀ y : IdempotentedRingRightLimit A, y * z = z * y :=
  @mem_centerSubring_iff_mul

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (z : IdempotentedRingRightLimit A),
    letI := ring hA
    z ∈ centerSubring hA ↔
      ∀ y : IdempotentedRingRightLimit A, product hA y z = product hA z y :=
  @mem_centerSubring_iff

example : ∀ {A : Type 1} [NonUnitalRing A], IsIdempotented A → Type 1 :=
  @Center

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A), CommRing (Center hA) :=
  @Center.commRing

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    Center hA = ↥(centerSubring hA) :=
  @Center.carrier_eq

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Center hA →+* IdempotentedRingRightLimit A :=
  @Center.inclusion

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA),
    Center.inclusion hA z = z.val :=
  @Center.inclusion_apply

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    (Center.inclusion hA : Center hA → IdempotentedRingRightLimit A) = Subtype.val :=
  @Center.inclusion_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    Function.Injective (Center.inclusion hA) :=
  @Center.inclusion_injective

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z w : Center hA),
    (z * w).val = product hA z.val w.val :=
  @Center.mul_val

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    (1 : Center hA).val = unit :=
  @Center.one_val

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z w : Center hA),
    (z + w).val = z.val + w.val :=
  @Center.add_val

example : ∀ {A : Type 1} [NonUnitalRing A] {hA : IsIdempotented A} {z w : Center hA},
    (∀ e : Idempotent A, z.val.val e = w.val.val e) → z = w :=
  @Center.ext

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (y : IdempotentedRingRightLimit A), product hA y z.val = product hA z.val y :=
  @Center.product_comm

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), (e : A) * z.val.val e = z.val.val e :=
  @Center.left_support

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), z.val.val e ∈ e.corner :=
  @Center.coordinate_mem_corner

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A) (a : A), a ∈ e.corner → a * z.val.val e = z.val.val e * a :=
  @Center.commute_corner

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    Center hA → ∀ e : Idempotent A, Corner e :=
  @Center.cornerCoordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), Corner.toAmbient e (Center.cornerCoordinate hA z e) = z.val.val e :=
  @Center.cornerCoordinate_ambient

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), Center.cornerCoordinate hA z e ∈ Subring.center (Corner e) :=
  @Center.cornerCoordinate_mem_center

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A), Center hA →+* CornerCenter e :=
  @Center.coordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toAmbient e (Center.coordinate hA e z) = z.val.val e :=
  @Center.coordinate_ambient

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toCorner e (Center.coordinate hA e z) = Center.cornerCoordinate hA z e :=
  @Center.toCorner_coordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Center.coordinate hA e : Center hA → CornerCenter e) =
      fun z => ⟨Center.cornerCoordinate hA z e, Center.cornerCoordinate_mem_center hA z e⟩ :=
  @Center.coordinate_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    CornerCenter.toAmbient e ∘ Center.coordinate hA e = fun z => z.val.val e :=
  @Center.coordinate_ambient_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA),
    CornerCenter.toAmbient e (Center.coordinate hA e z) = (e : A) * z.val.val e * e :=
  @Center.coordinate_ambient_sandwich

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    {e f : Idempotent A} (h : e ≤ f),
    (CornerCenter.transition h).comp (Center.coordinate hA f) = Center.coordinate hA e :=
  @Center.transition_comp_coordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A), Center hA →+* Family A :=
  @Center.toFamily

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.coordinate e).comp (Center.toFamily hA) = Center.coordinate hA e :=
  @Center.coordinate_comp_toFamily

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (z : Center hA)
    (e : Idempotent A), (Center.toFamily hA z).val e = Center.coordinate hA e z :=
  @Center.toFamily_val

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    Subtype.val ∘ Center.toFamily hA = fun z e => Center.coordinate hA e z :=
  @Center.toFamily_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (_e : Idempotent A), Center hA →ₙ+* A :=
  @Center.ambientCoordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A) (z : Center hA), Center.ambientCoordinate hA e z = z.val.val e :=
  @Center.ambientCoordinate_apply

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Center.ambientCoordinate hA e : Center hA → A) = fun z => z.val.val e :=
  @Center.ambientCoordinate_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.ambientCoordinate e).comp (Center.toFamily hA).toNonUnitalRingHom =
      Center.ambientCoordinate hA e :=
  @Center.ambientCoordinate_comp_toFamily

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (e : Idempotent A),
    (Family.ambientCoordinate e : Family A → A) ∘ Center.toFamily hA = fun z => z.val.val e :=
  @Center.ambientCoordinate_toFamily_function

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A) (x : Family A),
    (e : A) * Family.ambientCoordinate e x = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_left_support

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A) (x : Family A),
    Family.ambientCoordinate e x * (e : A) = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_right_support

example : ∀ {A : Type 1} [NonUnitalRing A] {e f : Idempotent A} (_h : e ≤ f)
    (x : Family A), Family.ambientCoordinate f x * (e : A) = Family.ambientCoordinate e x :=
  @Family.ambientCoordinate_mul_of_le

example : ∀ {A : Type 1} [NonUnitalRing A], Family A → IdempotentedRingRightLimit A :=
  @Family.toRightLimit

example : ∀ {A : Type 1} [NonUnitalRing A] (x : Family A) (e : Idempotent A),
    (Family.toRightLimit x).val e = (x.val e).val.val :=
  @Family.toRightLimit_val

example : ∀ {A : Type 1} [NonUnitalRing A],
    (fun x : Family A => (Family.toRightLimit x).val) = fun x e => (x.val e).val.val :=
  @Family.toRightLimit_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (x y : Family A),
    Family.toRightLimit (x * y) =
      product hA (Family.toRightLimit x) (Family.toRightLimit y) :=
  @Family.toRightLimit_mul

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A)
    (y : IdempotentedRingRightLimit A),
    product hA y (Family.toRightLimit x) = product hA (Family.toRightLimit x) y :=
  @Family.product_toRightLimit_comm

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Family.toRightLimit x ∈ centerSubring hA :=
  @Family.toRightLimit_mem_centerSubring

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    Family A →+* IdempotentedRingRightLimit A :=
  @Family.toRightLimitRingHom

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Family.toRightLimitRingHom hA x = Family.toRightLimit x :=
  @Family.toRightLimitRingHom_apply

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    (Family.toRightLimitRingHom hA : Family A → IdempotentedRingRightLimit A) =
      Family.toRightLimit :=
  @Family.toRightLimitRingHom_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A), Family A →+* Center hA :=
  @Family.toCenter

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    (Family.toCenter hA x).val = Family.toRightLimit x :=
  @Family.toCenter_val

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A)
    (e : Idempotent A), (Family.toCenter hA x).val.val e = (x.val e).val.val :=
  @Family.toCenter_coordinate

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    (fun x : Family A => (Family.toCenter hA x).val.val) = fun x e => (x.val e).val.val :=
  @Family.toCenter_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (x : Family A),
    Center.inclusion hA (Family.toCenter hA x) = Family.toRightLimit x :=
  @Family.inclusion_toCenter

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    (Center.inclusion hA : Center hA → IdempotentedRingRightLimit A) ∘ Family.toCenter hA =
      Family.toRightLimit :=
  @Family.inclusion_comp_toCenter_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := ring hA
    (Center.inclusion hA).comp (Family.toCenter hA) = Family.toRightLimitRingHom hA :=
  @Family.inclusion_comp_toCenter

end UniverseOne


/-! Explicit choices retain the original ring when a competing one coexists. -/
section CompetingAmbient

-- Both local instances are intentional in these checks.
set_option linter.overlappingInstances false

variable {A : Type uA} [originalAmbient : NonUnitalRing A]
  [competingAmbient : NonUnitalRing A]

example :
    letI := originalAmbient
    ∀ hA : IsIdempotented A,
      letI := ring hA
      Subring (IdempotentedRingRightLimit A) :=
  @centerSubring A originalAmbient

example :
    letI := originalAmbient
    IsIdempotented A → Type uA :=
  @Center A originalAmbient

example :
    letI := originalAmbient
    ∀ (hA : IsIdempotented A) (z : Center hA) (e : Idempotent A),
      (e : A) * z.val.val e = z.val.val e :=
  @Center.left_support A originalAmbient

example :
    letI := originalAmbient
    ∀ (hA : IsIdempotented A) (e : Idempotent A), Center hA →+* CornerCenter e :=
  @Center.coordinate A originalAmbient

example :
    letI := originalAmbient
    ∀ hA : IsIdempotented A, Center hA →+* Family A :=
  @Center.toFamily A originalAmbient

example :
    letI := originalAmbient
    ∀ (hA : IsIdempotented A) (_e : Idempotent A), Center hA →ₙ+* A :=
  @Center.ambientCoordinate A originalAmbient

example :
    letI := originalAmbient
    Family A → IdempotentedRingRightLimit A :=
  @Family.toRightLimit A originalAmbient

example :
    letI := originalAmbient
    ∀ hA : IsIdempotented A, Family A →+* Center hA :=
  @Family.toCenter A originalAmbient

end CompetingAmbient

section CompetingStructures

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
  [competingCompletedRing : Ring (IdempotentedRingRightLimit A)]
  [competingCenterRing : CommRing (Center hA)]
  [competingCornerRing : Ring (Corner e)]
  [competingCornerCenterRing : CommRing (CornerCenter e)]
  [competingFamilyRing : CommRing (Family A)]

example :
    letI := ring hA
    ∀ z : IdempotentedRingRightLimit A,
      z ∈ centerSubring hA ↔ ∀ y : IdempotentedRingRightLimit A, y * z = z * y :=
  mem_centerSubring_iff_mul hA

example :
    letI := ring hA
    letI := Center.commRing hA
    Center hA →+* IdempotentedRingRightLimit A :=
  Center.inclusion hA

example :
    letI := Center.commRing hA
    ∀ z w : Center hA, (z * w).val = product hA z.val w.val :=
  Center.mul_val hA

example :
    letI := Center.commRing hA
    ∀ z w : Center hA, (z + w).val.val e = z.val.val e + w.val.val e :=
  fun _ _ => rfl

example :
    letI := Center.commRing hA
    (1 : Center hA).val.val e = (e : A) :=
  rfl

example :
    letI := Center.commRing hA
    letI := CornerCenter.commRing e
    ∀ z w : Center hA,
      Center.coordinate hA e (z * w) = Center.coordinate hA e z * Center.coordinate hA e w :=
  (Center.coordinate hA e).map_mul

example :
    letI := Corner.ring e
    letI := CornerCenter.commRing e
    ∀ z : Center hA,
      CornerCenter.toCorner e (Center.coordinate hA e z) = Center.cornerCoordinate hA z e :=
  Center.toCorner_coordinate hA e

example :
    letI := Center.commRing hA
    letI := Family.commRing A
    Center hA →+* Family A :=
  Center.toFamily hA

example :
    letI := Center.commRing hA
    letI := Family.commRing A
    ∀ z w : Center hA, Center.toFamily hA (z * w) = Center.toFamily hA z * Center.toFamily hA w :=
  (Center.toFamily hA).map_mul

example :
    letI := ring hA
    letI := Family.commRing A
    ∀ x y : Family A,
      Family.toRightLimit (x * y) = Family.toRightLimit x * Family.toRightLimit y :=
  Family.toRightLimit_mul hA

example :
    letI := ring hA
    letI := Family.commRing A
    Family A →+* IdempotentedRingRightLimit A :=
  Family.toRightLimitRingHom hA

example :
    letI := Family.commRing A
    letI := Center.commRing hA
    Family A →+* Center hA :=
  Family.toCenter hA

example :
    letI := Family.commRing A
    letI := Center.commRing hA
    ∀ x y : Family A, Family.toCenter hA (x * y) = Family.toCenter hA x * Family.toCenter hA y :=
  (Family.toCenter hA).map_mul

example :
    letI := Family.commRing A
    letI := Center.commRing hA
    (Family.toCenter hA 1 : Center hA) = 1 :=
  (Family.toCenter hA).map_one

end CompetingStructures

/-! Zero ambient rings and the zero idempotent need no exclusion. -/
section ZeroRings

variable {A : Type uA} [NonUnitalRing A]

example (hA : IsIdempotented A) (z : Center hA) :
    let e0 : Idempotent A := ⟨0, zero_mul 0⟩
    CornerCenter.toAmbient e0 (Center.coordinate hA e0 z) = 0 := by
  intro e0
  change z.val.val e0 = 0
  exact (Center.left_support hA z e0).symm.trans (zero_mul _)

example : Subsingleton (Center (IsIdempotented.of_ring PUnit.{uA + 1})) :=
  ⟨fun _ _ => Center.ext fun _ => Subsingleton.elim _ _⟩

example : Center (IsIdempotented.of_ring PUnit.{uA + 1}) →+* Family PUnit.{uA + 1} :=
  Center.toFamily (IsIdempotented.of_ring PUnit.{uA + 1})

example : Family PUnit.{uA + 1} →+* Center (IsIdempotented.of_ring PUnit.{uA + 1}) :=
  Family.toCenter (IsIdempotented.of_ring PUnit.{uA + 1})

end ZeroRings

end Langlands.Algebra
