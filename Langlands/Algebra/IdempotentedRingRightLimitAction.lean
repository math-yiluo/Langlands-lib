import Langlands.Algebra.IdempotentedRingRightLimitRing
import Langlands.Algebra.NonUnitalModule
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# The actual right-limit action on original nondegenerate modules

Renard I.1.3, printed p.9/PDF15. Every actual fixing idempotent computes
the same extended action on the original additive carrier.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace IdempotentedRingRightLimitAction

universe uA uM uN uP

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

/-- Family coherence makes the source action formula independent of its fixer. -/
theorem coordinate_smul_independent (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (m : M) (e f : Idempotent A)
    (he : (e : A) • m = m) (hf : (f : A) • m = m) :
    x.val e • m = x.val f • m := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have heg : e ≤ g := hg e (by simp)
  have hfg : f ≤ g := hg f (by simp)
  calc
    x.val e • m = (x.val g * (e : A)) • m := by
      rw [x.property.2 e g heg]
    _ = x.val g • m := by rw [mul_smul, he]
    _ = (x.val g * (f : A)) • m := by rw [mul_smul, hf]
    _ = x.val f • m := by rw [x.property.2 f g hfg]

/-- The source's actual action, initially choosing one fixing idempotent. -/
def act (hM : IsNondegenerate A M) (x : IdempotentedRingRightLimit A) (m : M) : M :=
  x.val (Classical.choose (hM m)) • m

/-- Every fixing idempotent gives exactly the same actual action value. -/
theorem act_eq (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) (m : M) (e : Idempotent A)
    (he : (e : A) • m = m) : act hM x m = x.val e • m :=
  coordinate_smul_independent hA x m _ e (Classical.choose_spec (hM m)) he

@[simp] theorem act_zero (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) : act hM x 0 = 0 := by
  obtain ⟨e, he⟩ := hM 0
  rw [act_eq hA hM x 0 e he, smul_zero]

@[simp] theorem zero_act (hA : IsIdempotented A) (hM : IsNondegenerate A M) (m : M) :
    act hM (0 : IdempotentedRingRightLimit A) m = 0 := by
  obtain ⟨e, he⟩ := hM m
  rw [act_eq hA hM 0 m e he]
  exact NonUnitalModule.zero_smul m

/-- A common upper fixer supplies additivity in the original vector. -/
theorem act_add (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) (m n : M) :
    act hM x (m + n) = act hM x m + act hM x n := by
  classical
  obtain ⟨e, he⟩ := hM m
  obtain ⟨f, hf⟩ := hM n
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have hgm : (g : A) • m = m := Idempotent.smul_eq_of_le (hg e (by simp)) he
  have hgn : (g : A) • n = n := Idempotent.smul_eq_of_le (hg f (by simp)) hf
  have hgs : (g : A) • (m + n) = m + n := by rw [smul_add, hgm, hgn]
  rw [act_eq hA hM x (m + n) g hgs,
    act_eq hA hM x m g hgm, act_eq hA hM x n g hgn, smul_add]

theorem add_act (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x y : IdempotentedRingRightLimit A) (m : M) :
    act hM (x + y) m = act hM x m + act hM y m := by
  obtain ⟨e, he⟩ := hM m
  rw [act_eq hA hM (x + y) m e he,
    act_eq hA hM x m e he, act_eq hA hM y m e he]
  exact NonUnitalModule.add_smul (x.val e) (y.val e) m

@[simp] theorem unit_act (hA : IsIdempotented A) (hM : IsNondegenerate A M) (m : M) :
    act hM IdempotentedRingRightLimit.unit m = m := by
  obtain ⟨e, he⟩ := hM m
  rw [act_eq hA hM IdempotentedRingRightLimit.unit m e he]
  exact he

/-- A left unit for the intermediate coordinate also fixes its action on the vector. -/
theorem product_act (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x y : IdempotentedRingRightLimit A) (m : M) :
    act hM (IdempotentedRingRightLimit.product hA x y) m =
      act hM x (act hM y m) := by
  classical
  obtain ⟨e, he⟩ := hM m
  obtain ⟨f, hf⟩ :=
    (IsIdempotented.iff_two_sided_local_units.mp hA) {y.val e}
  have hfy : (f : A) * y.val e = y.val e := (hf (y.val e) (by simp)).1
  have hfm : (f : A) • (y.val e • m) = y.val e • m := by
    rw [← mul_smul, hfy]
  rw [act_eq hA hM (IdempotentedRingRightLimit.product hA x y) m e he,
    IdempotentedRingRightLimit.product_val hA x y e f hfy,
    act_eq hA hM y m e he, act_eq hA hM x (y.val e • m) f hfm, mul_smul]

/-- The actual extended module retains precisely the original additive group. -/
@[instance_reducible]
def module (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := IdempotentedRingRightLimit.ring hA
    Module (IdempotentedRingRightLimit A) M := by
  letI := IdempotentedRingRightLimit.ring hA
  exact
    { smul := act hM
      one_smul := unit_act hA hM
      mul_smul := product_act hA hM
      smul_zero := act_zero hA hM
      smul_add := act_add hA hM
      add_smul := add_act hA hM
      zero_smul := zero_act hA hM }

/-- The installed module action has exactly the source coordinate formula. -/
theorem smul_eq (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) (m : M) (e : Idempotent A)
    (he : (e : A) • m = m) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    x • m = x.val e • m := act_eq hA hM x m e he

/-- Along the original canonical map, the new action is exactly the original action. -/
@[simp] theorem canonical_act (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (a : A) (m : M) : act hM (IdempotentedRingRightLimit.canonical a) m = a • m := by
  obtain ⟨e, he⟩ := hM m
  rw [act_eq hA hM (IdempotentedRingRightLimit.canonical a) m e he]
  change (a * (e : A)) • m = a • m
  rw [mul_smul, he]

theorem canonical_smul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (a : A) (m : M) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    IdempotentedRingRightLimit.canonical a • m = a • m :=
  canonical_act hA hM a m

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

/-- An original intertwiner preserves every fixing equation, hence the actual action. -/
theorem map_act (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (x : IdempotentedRingRightLimit A) (m : M) :
    f (act hM x m) = act hN x (f m) := by
  obtain ⟨e, he⟩ := hM m
  have hef : (e : A) • f m = f m := by rw [← f.map_smul, he]
  rw [act_eq hA hM x m e he, f.map_smul, act_eq hA hN x (f m) e hef]

/-- The same actual additive intertwiner, now linear for the constructed modules. -/
def linearMap (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    letI := module hA hN
    M →ₗ[IdempotentedRingRightLimit A] N := by
  letI := IdempotentedRingRightLimit.ring hA
  letI := module hA hM
  letI := module hA hN
  exact
    { f.toAddMonoidHom with
      map_smul' := map_act hA hM hN f }

@[simp] theorem linearMap_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (m : M) :
    linearMap hA hM hN f m = f m := rfl

@[simp] theorem linearMap_toAddMonoidHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    letI := module hA hN
    (linearMap hA hM hN f).toAddMonoidHom = f.toAddMonoidHom := rfl

theorem linearMap_id (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    linearMap hA hM hM (NonUnitalModuleHom.id A M) = LinearMap.id := by
  let := IdempotentedRingRightLimit.ring hA
  let := module hA hM
  apply LinearMap.ext
  intro m
  rfl

variable {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]

theorem linearMap_comp (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom A N P) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    letI := module hA hN
    letI := module hA hP
    linearMap hA hM hP (g.comp f) = (linearMap hA hN hP g).comp (linearMap hA hM hN f) := by
  let := IdempotentedRingRightLimit.ring hA
  let := module hA hM
  let := module hA hN
  let := module hA hP
  apply LinearMap.ext
  intro m
  rfl

/-! Complete unapplied interfaces preserve independent scalar and carrier universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsNondegenerate A M → IdempotentedRingRightLimit A → M → M :=
  @act.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → (x : IdempotentedRingRightLimit A) → (m : M) →
    (e f : Idempotent A) → (e : A) • m = m → (f : A) • m = m →
    x.val e • m = x.val f • m :=
  @coordinate_smul_independent.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := IdempotentedRingRightLimit.ring hA
    Module (IdempotentedRingRightLimit A) M :=
  @module.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := IdempotentedRingRightLimit.ring hA
    Module (IdempotentedRingRightLimit A) M :=
  @module.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := IdempotentedRingRightLimit.ring hA
    Module (IdempotentedRingRightLimit A) M :=
  @module.{1, 0}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) → (m : M) → (e : Idempotent A) →
    (e : A) • m = m →
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    x • m = x.val e • m :=
  @smul_eq.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (a : A) → (m : M) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    IdempotentedRingRightLimit.canonical a • m = a • m :=
  @canonical_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    (hM : IsNondegenerate A M) → (hN : IsNondegenerate A N) →
    NonUnitalModuleHom A M N →
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    letI := module hA hN
    M →ₗ[IdempotentedRingRightLimit A] N :=
  @linearMap.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    (hM : IsNondegenerate A M) → (hN : IsNondegenerate A N) →
    (f : NonUnitalModuleHom A M N) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    letI := module hA hN
    (linearMap hA hM hN f).toAddMonoidHom = f.toAddMonoidHom :=
  @linearMap_toAddMonoidHom.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    linearMap hA hM hM (NonUnitalModuleHom.id A M) = LinearMap.id :=
  @linearMap_id.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    {P : Type uP} → [AddCommGroup P] → [NonUnitalModule A P] →
    (hA : IsIdempotented A) →
    (hM : IsNondegenerate A M) → (hN : IsNondegenerate A N) →
    (hP : IsNondegenerate A P) →
    (f : NonUnitalModuleHom A M N) → (g : NonUnitalModuleHom A N P) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    letI := module hA hN
    letI := module hA hP
    linearMap hA hM hP (g.comp f) =
      (linearMap hA hN hP g).comp (linearMap hA hM hN f) :=
  @linearMap_comp.{uA, uM, uN, uP}

/-! Installation changes the scalar action only; the additive group is the original input. -/

example (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) (m : M) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := module hA hM
    x • m = act hM x m := rfl

end IdempotentedRingRightLimitAction
end Langlands.Algebra
