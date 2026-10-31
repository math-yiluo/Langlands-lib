import Langlands.Algebra.RegularModuleHom

/-!
# The original left action on actual compatible module families

Renard I.1.4, printed p.10/PDF16. The direct local-unit construction
uses the original action and the actual family's left-coherence equations.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM

namespace NonUnitalModuleLeftLimit

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [hM : NonUnitalModule A M]

private theorem exists_rightUnit (hA : IsIdempotented A) (a : A) :
    ∃ e : Idempotent A, a * (e : A) = a := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a}
  exact ⟨e, (he a (by simp)).2⟩

private theorem coordinate_independent (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a : A) (e f : Idempotent A)
    (he : a * (e : A) = a) (hf : a * (f : A) = a) :
    a • x.val e = a • x.val f := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have heg : e ≤ g := hg e (by simp)
  have hfg : f ≤ g := hg f (by simp)
  calc
    a • x.val e = a • ((e : A) • x.val g) := by
      rw [x.property.2 e g heg]
    _ = a • x.val g := by rw [← mul_smul, he]
    _ = a • ((f : A) • x.val g) := by rw [← mul_smul, hf]
    _ = a • x.val f := by rw [x.property.2 f g hfg]

private def coordinateValue (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a : A) : M :=
  a • x.val (Classical.choose (exists_rightUnit hA a))

private theorem coordinateValue_eq (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A)
    (he : a * (e : A) = a) :
    coordinateValue hA x a = a • x.val e :=
  coordinate_independent hA x a _ e
    (Classical.choose_spec (exists_rightUnit hA a)) he

private theorem coordinateValue_zero (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) : coordinateValue hA x 0 = 0 := by
  obtain ⟨e, he⟩ := exists_rightUnit hA (0 : A)
  rw [coordinateValue_eq hA x 0 e he]
  exact NonUnitalModule.zero_smul _

private theorem coordinateValue_add (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a b : A) :
    coordinateValue hA x (a + b) =
      coordinateValue hA x a + coordinateValue hA x b := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a, b}
  have hea : a * (e : A) = a := (he a (by simp)).2
  have heb : b * (e : A) = b := (he b (by simp)).2
  have heab : (a + b) * (e : A) = a + b := by rw [add_mul, hea, heb]
  rw [coordinateValue_eq hA x (a + b) e heab,
    coordinateValue_eq hA x a e hea, coordinateValue_eq hA x b e heb,
    NonUnitalModule.add_smul]

private theorem coordinateValue_mul (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a b : A) :
    coordinateValue hA x (a * b) = a • coordinateValue hA x b := by
  obtain ⟨e, he⟩ := exists_rightUnit hA b
  have heab : (a * b) * (e : A) = a * b := by rw [mul_assoc, he]
  rw [coordinateValue_eq hA x (a * b) e heab,
    coordinateValue_eq hA x b e he, mul_smul]

private theorem coordinateValue_zeroFamily (hA : IsIdempotented A) (a : A) :
    coordinateValue hA (0 : NonUnitalModuleLeftLimit A M) a = 0 := by
  obtain ⟨e, he⟩ := exists_rightUnit hA a
  rw [coordinateValue_eq hA 0 a e he]
  exact smul_zero a

private theorem coordinateValue_addFamily (hA : IsIdempotented A)
    (x y : NonUnitalModuleLeftLimit A M) (a : A) :
    coordinateValue hA (x + y) a =
      coordinateValue hA x a + coordinateValue hA y a := by
  obtain ⟨e, he⟩ := exists_rightUnit hA a
  rw [coordinateValue_eq hA (x + y) a e he,
    coordinateValue_eq hA x a e he, coordinateValue_eq hA y a e he]
  exact smul_add a (x.val e) (y.val e)

/-- Direct local-unit action on actual compatible families, before packaging its laws. -/
def scalarAction (hA : IsIdempotented A) (a : A)
    (x : NonUnitalModuleLeftLimit A M) : NonUnitalModuleLeftLimit A M :=
  ⟨fun e => coordinateValue hA x ((e : A) * a), by
    constructor
    · intro e
      change (e : A) • coordinateValue hA x ((e : A) * a) = _
      rw [← coordinateValue_mul, ← mul_assoc, e.property.eq]
    · intro e f hef
      change (e : A) • coordinateValue hA x ((f : A) * a) = _
      rw [← coordinateValue_mul, ← mul_assoc,
        ((Idempotent.le_iff_mul e f).mp hef).2]⟩

/-- The coordinate formula holds for every right local unit of `e*a`. -/
theorem scalarAction_val (hA : IsIdempotented A) (a : A)
    (x : NonUnitalModuleLeftLimit A M) (e f : Idempotent A)
    (hf : ((e : A) * a) * (f : A) = (e : A) * a) :
    (scalarAction hA a x).val e = ((e : A) * a) • x.val f :=
  coordinateValue_eq hA x ((e : A) * a) f hf

private theorem coordinateValue_scalarAction (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a b : A) :
    coordinateValue hA (scalarAction hA b x) a =
      coordinateValue hA x (a * b) := by
  obtain ⟨e, he⟩ := exists_rightUnit hA a
  rw [coordinateValue_eq hA (scalarAction hA b x) a e he]
  change a • coordinateValue hA x ((e : A) * b) = _
  rw [← coordinateValue_mul, ← mul_assoc, he]

/-- The original left module action, depending explicitly on the local-unit hypothesis. -/
abbrev nonUnitalModule (hA : IsIdempotented A) :
    NonUnitalModule A (NonUnitalModuleLeftLimit A M) where
  smul := scalarAction hA
  smul_zero a := by
    apply Subtype.ext
    funext e
    exact coordinateValue_zeroFamily hA ((e : A) * a)
  smul_add a x y := by
    apply Subtype.ext
    funext e
    exact coordinateValue_addFamily hA x y ((e : A) * a)
  mul_smul a b x := by
    apply Subtype.ext
    funext e
    change coordinateValue hA x ((e : A) * (a * b)) =
      coordinateValue hA (scalarAction hA b x) ((e : A) * a)
    rw [coordinateValue_scalarAction, mul_assoc]
  add_smul a b x := by
    apply Subtype.ext
    funext e
    change coordinateValue hA x ((e : A) * (a + b)) =
      coordinateValue hA x ((e : A) * a) + coordinateValue hA x ((e : A) * b)
    rw [mul_add, coordinateValue_add]
  zero_smul x := by
    apply Subtype.ext
    funext e
    change coordinateValue hA x ((e : A) * 0) = 0
    rw [mul_zero, coordinateValue_zero]

@[simp] theorem nonUnitalModule_smul (hA : IsIdempotented A) (a : A)
    (x : NonUnitalModuleLeftLimit A M) :
    (nonUnitalModule hA).smul a x = scalarAction hA a x := rfl

/-- The original vector map intertwines the original and constructed actions. -/
theorem scalarAction_canonical (hA : IsIdempotented A) (a : A) (m : M) :
    scalarAction hA a (canonical (A := A) m) = canonical (a • m) := by
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := exists_rightUnit hA ((e : A) * a)
  rw [scalarAction_val hA a _ e f hf]
  change ((e : A) * a) • ((f : A) • m) = (e : A) • (a • m)
  rw [← mul_smul, hf, mul_smul]

private theorem coordinateValue_toLeftLimit (hA : IsIdempotented A)
    (φ : RegularModuleHom A M) (a : A) :
    coordinateValue hA (RegularModuleHom.toLeftLimit φ) a = φ a := by
  obtain ⟨e, he⟩ := exists_rightUnit hA a
  rw [coordinateValue_eq hA _ a e he]
  change a • φ (e : A) = φ a
  rw [← RegularModuleHom.map_mul_left, he]

/-- Actual idempotent evaluation intertwines right precomposition and this family action. -/
theorem scalarAction_toLeftLimit (hA : IsIdempotented A) (a : A)
    (φ : RegularModuleHom A M) :
    scalarAction hA a (RegularModuleHom.toLeftLimit φ) =
      RegularModuleHom.toLeftLimit (a • φ) := by
  apply Subtype.ext
  funext e
  exact coordinateValue_toLeftLimit hA φ ((e : A) * a)

/-- The existing evaluation additive map, with its actual intertwining law. -/
def toLeftLimitHom (hA : IsIdempotented A) :
    @NonUnitalModuleHom A (RegularModuleHom A M) (NonUnitalModuleLeftLimit A M)
      _ _ _ RegularModuleHom.instNonUnitalModule (nonUnitalModule hA) := by
  letI := nonUnitalModule (M := M) hA
  exact
    { toAddMonoidHom := RegularModuleHom.toLeftLimit
      map_smul' := fun a φ => (scalarAction_toLeftLimit hA a φ).symm }

@[simp] theorem toLeftLimitHom_toAddMonoidHom (hA : IsIdempotented A) :
    letI := nonUnitalModule (M := M) hA
    (toLeftLimitHom (M := M) hA).toAddMonoidHom = RegularModuleHom.toLeftLimit := rfl

/-- The existing canonical additive map, with its actual intertwining law. -/
def canonicalHom (hA : IsIdempotented A) :
    @NonUnitalModuleHom A M (NonUnitalModuleLeftLimit A M)
      _ _ _ hM (nonUnitalModule hA) := by
  letI := nonUnitalModule (M := M) hA
  exact
    { toAddMonoidHom := canonical
      map_smul' := fun a m => (scalarAction_canonical hA a m).symm }

@[simp] theorem canonicalHom_toAddMonoidHom (hA : IsIdempotented A) :
    letI := nonUnitalModule (M := M) hA
    (canonicalHom (M := M) hA).toAddMonoidHom = canonical := rfl

/-- An idempotent acting on a family is the canonical family of its coordinate. -/
theorem idempotent_scalarAction (hA : IsIdempotented A) (e : Idempotent A)
    (x : NonUnitalModuleLeftLimit A M) :
    scalarAction hA (e : A) x = canonical (x.val e) := by
  apply Subtype.ext
  funext f
  have he : ((f : A) * (e : A)) * (e : A) = (f : A) * (e : A) := by
    rw [mul_assoc, e.property.eq]
  rw [scalarAction_val hA (e : A) x f e he]
  change ((f : A) * (e : A)) • x.val e = (f : A) • x.val e
  rw [mul_smul, x.property.1 e]

/-- Exact coordinate formula with the constructed action installed locally. -/
theorem smul_val (hA : IsIdempotented A) (a : A)
    (x : NonUnitalModuleLeftLimit A M) (e f : Idempotent A)
    (hf : ((e : A) * a) * (f : A) = (e : A) * a) :
    letI := nonUnitalModule (M := M) hA
    (a • x).val e = ((e : A) * a) • x.val f :=
  scalarAction_val hA a x e f hf

@[simp] theorem toLeftLimitHom_apply (hA : IsIdempotented A)
    (φ : RegularModuleHom A M) :
    letI := nonUnitalModule (M := M) hA
    toLeftLimitHom (M := M) hA φ = RegularModuleHom.toLeftLimit φ := rfl

@[simp] theorem canonicalHom_apply (hA : IsIdempotented A) (m : M) :
    letI := nonUnitalModule (M := M) hA
    canonicalHom (M := M) hA m = canonical m := rfl

/-- The intrinsic idempotent formula in the constructed module. -/
theorem idempotent_smul (hA : IsIdempotented A) (e : Idempotent A)
    (x : NonUnitalModuleLeftLimit A M) :
    letI := nonUnitalModule (M := M) hA
    (e : A) • x = canonical (x.val e) :=
  idempotent_scalarAction hA e x

/-! Complete unapplied interfaces preserve every original action and both universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → NonUnitalModule A (NonUnitalModuleLeftLimit A M) :=
  @nonUnitalModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → A → NonUnitalModuleLeftLimit A M → NonUnitalModuleLeftLimit A M :=
  @scalarAction.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (a : A) → (x : NonUnitalModuleLeftLimit A M) →
    (e f : Idempotent A) → ((e : A) * a) * (f : A) = (e : A) * a →
    (scalarAction hA a x).val e = ((e : A) * a) • x.val f :=
  @scalarAction_val.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    @NonUnitalModuleHom A (RegularModuleHom A M) (NonUnitalModuleLeftLimit A M)
      _ _ _ RegularModuleHom.instNonUnitalModule (nonUnitalModule hA) :=
  @toLeftLimitHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → (hM : NonUnitalModule A M) →
    (hA : IsIdempotented A) →
    @NonUnitalModuleHom A M (NonUnitalModuleLeftLimit A M)
      _ _ _ hM (nonUnitalModule hA) :=
  @canonicalHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    (letI := nonUnitalModule (M := M) hA
     (toLeftLimitHom (M := M) hA).toAddMonoidHom = RegularModuleHom.toLeftLimit) :=
  @toLeftLimitHom_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    (letI := nonUnitalModule (M := M) hA
     (canonicalHom (M := M) hA).toAddMonoidHom = canonical) :=
  @canonicalHom_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (e : Idempotent A) → (x : NonUnitalModuleLeftLimit A M) →
    scalarAction hA (e : A) x = canonical (x.val e) :=
  @idempotent_scalarAction.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → NonUnitalModule A (NonUnitalModuleLeftLimit A M) :=
  @nonUnitalModule.{0, 1}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (a : A) → (x : NonUnitalModuleLeftLimit A M) →
    (e f : Idempotent A) → ((e : A) * a) * (f : A) = (e : A) * a →
    (scalarAction hA a x).val e = ((e : A) * a) • x.val f :=
  @scalarAction_val.{0, 1}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    @NonUnitalModuleHom A (RegularModuleHom A M) (NonUnitalModuleLeftLimit A M)
      _ _ _ RegularModuleHom.instNonUnitalModule (nonUnitalModule hA) :=
  @toLeftLimitHom.{0, 1}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → (hM : NonUnitalModule A M) →
    (hA : IsIdempotented A) →
    @NonUnitalModuleHom A M (NonUnitalModuleLeftLimit A M)
      _ _ _ hM (nonUnitalModule hA) :=
  @canonicalHom.{0, 1}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    (letI := nonUnitalModule (M := M) hA
     (toLeftLimitHom (M := M) hA).toAddMonoidHom = RegularModuleHom.toLeftLimit) :=
  @toLeftLimitHom_toAddMonoidHom.{0, 1}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    (letI := nonUnitalModule (M := M) hA
     (canonicalHom (M := M) hA).toAddMonoidHom = canonical) :=
  @canonicalHom_toAddMonoidHom.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → NonUnitalModule A (NonUnitalModuleLeftLimit A M) :=
  @nonUnitalModule.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (a : A) → (x : NonUnitalModuleLeftLimit A M) →
    (e f : Idempotent A) → ((e : A) * a) * (f : A) = (e : A) * a →
    (scalarAction hA a x).val e = ((e : A) * a) • x.val f :=
  @scalarAction_val.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    @NonUnitalModuleHom A (RegularModuleHom A M) (NonUnitalModuleLeftLimit A M)
      _ _ _ RegularModuleHom.instNonUnitalModule (nonUnitalModule hA) :=
  @toLeftLimitHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → (hM : NonUnitalModule A M) →
    (hA : IsIdempotented A) →
    @NonUnitalModuleHom A M (NonUnitalModuleLeftLimit A M)
      _ _ _ hM (nonUnitalModule hA) :=
  @canonicalHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    (letI := nonUnitalModule (M := M) hA
     (toLeftLimitHom (M := M) hA).toAddMonoidHom = RegularModuleHom.toLeftLimit) :=
  @toLeftLimitHom_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) →
    (letI := nonUnitalModule (M := M) hA
     (canonicalHom (M := M) hA).toAddMonoidHom = canonical) :=
  @canonicalHom_toAddMonoidHom.{1, 0}

/-! The coordinate law also retains the exact locally installed action. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (a : A) → (x : NonUnitalModuleLeftLimit A M) →
    (e f : Idempotent A) → ((e : A) * a) * (f : A) = (e : A) * a →
    (letI := nonUnitalModule (M := M) hA
     (a • x).val e = ((e : A) * a) • x.val f) :=
  @smul_val.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (a : A) → (x : NonUnitalModuleLeftLimit A M) →
    (e f : Idempotent A) → ((e : A) * a) * (f : A) = (e : A) * a →
    (letI := nonUnitalModule (M := M) hA
     (a • x).val e = ((e : A) * a) • x.val f) :=
  @smul_val.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (a : A) → (x : NonUnitalModuleLeftLimit A M) →
    (e f : Idempotent A) → ((e : A) * a) * (f : A) = (e : A) * a →
    (letI := nonUnitalModule (M := M) hA
     (a • x).val e = ((e : A) * a) • x.val f) :=
  @smul_val.{1, 0}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (e : Idempotent A) →
    (x : NonUnitalModuleLeftLimit A M) →
    (letI := nonUnitalModule (M := M) hA
     (e : A) • x = canonical (x.val e)) :=
  @idempotent_smul.{uA, uM}

/-! Equal carriers keep a zero target action distinct from the regular Hom source. -/

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    NonUnitalModule A (@NonUnitalModuleLeftLimit A A _ _
      (NonUnitalModule.zero (A := A) (M := A))) :=
  @nonUnitalModule A _ A _ (NonUnitalModule.zero (A := A) (M := A)) hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    @NonUnitalModuleHom A (RegularModuleHom A A) (NonUnitalModuleLeftLimit A A)
      _ _ _ RegularModuleHom.instNonUnitalModule (nonUnitalModule hA) := by
  letI : NonUnitalModule A A := NonUnitalModule.zero
  exact toLeftLimitHom hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    @NonUnitalModuleHom A A (NonUnitalModuleLeftLimit A A)
      _ _ _ NonUnitalModule.zero (nonUnitalModule hA) := by
  letI : NonUnitalModule A A := NonUnitalModule.zero
  exact canonicalHom hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    letI := nonUnitalModule (M := A) hA
    (toLeftLimitHom (M := A) hA).toAddMonoidHom = RegularModuleHom.toLeftLimit := by
  exact @toLeftLimitHom_toAddMonoidHom A _ A _
    (NonUnitalModule.zero (A := A) (M := A)) hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    letI := nonUnitalModule (M := A) hA
    (canonicalHom (M := A) hA).toAddMonoidHom = canonical := by
  exact @canonicalHom_toAddMonoidHom A _ A _
    (NonUnitalModule.zero (A := A) (M := A)) hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    ∀ (a : A) (x : NonUnitalModuleLeftLimit A A) (e f : Idempotent A),
      ((e : A) * a) * (f : A) = (e : A) * a →
      (scalarAction hA a x).val e = ((e : A) * a) • x.val f := by
  exact @scalarAction_val A _ A _
    (NonUnitalModule.zero (A := A) (M := A)) hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI : NonUnitalModule A A := NonUnitalModule.zero
    letI := nonUnitalModule (M := A) hA
    ∀ (a : A) (x : NonUnitalModuleLeftLimit A A) (e f : Idempotent A),
      ((e : A) * a) * (f : A) = (e : A) * a →
      (a • x).val e = ((e : A) * a) • x.val f := by
  exact @smul_val A _ A _
    (NonUnitalModule.zero (A := A) (M := A)) hA

end NonUnitalModuleLeftLimit
end Langlands.Algebra
