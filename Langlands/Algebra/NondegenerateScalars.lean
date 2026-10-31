import Langlands.Algebra.CompatibleNonUnitalAction
import Mathlib.Basic.Complex.Basic

/-!
# Canonical scalars on original nondegenerate modules

Renard (9 July 2026), I.2.1, printed p. 14. The construction starts with the
original additive action, without a scalar module structure on the carrier.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateScalars

universe uK uA uM uN uP

section General

variable (k : Type uK) {A : Type uA} {M : Type uM}
  [CommSemiring k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [NonUnitalModule A M]

/-- The raw scalar formula, using a chosen fixing idempotent. -/
noncomputable def scalarMul (hM : IsNondegenerate A M) (c : k) (m : M) : M :=
  (c • ((hM m).choose : A)) • m

omit [SMulCommClass k A A] in
private theorem scaled_fixer_eq_of_le (c : k) {e f : Idempotent A} (hef : e ≤ f)
    {m : M} (he : (e : A) • m = m) :
    (c • (e : A)) • m = (c • (f : A)) • m := by
  calc
    (c • (e : A)) • m = (c • ((f : A) * e)) • m := by
      rw [((Idempotent.le_iff_mul e f).mp hef).1]
    _ = ((c • (f : A)) * e) • m := by rw [smul_mul_assoc]
    _ = (c • (f : A)) • ((e : A) • m) := mul_smul _ _ _
    _ = (c • (f : A)) • m := by rw [he]

omit [SMulCommClass k A A] in
/-- Any two fixing idempotents give exactly the same scalar value. -/
theorem fixer_independent (hA : IsIdempotented A) (c : k) (m : M)
    (e f : Idempotent A) (he : (e : A) • m = m) (hf : (f : A) • m = m) :
    (c • (e : A)) • m = (c • (f : A)) • m := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  exact (scaled_fixer_eq_of_le k c (hg e (by simp)) he).trans
    (scaled_fixer_eq_of_le k c (hg f (by simp)) hf).symm

omit [SMulCommClass k A A] in
/-- The raw scalar formula holds for every fixing idempotent. -/
theorem scalarMul_eq (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : k) (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    scalarMul k hM c m = (c • (e : A)) • m :=
  fixer_independent k hA c m _ e (hM m).choose_spec he

omit [SMulCommClass k A A] in
/-- Raw scalars pass through the algebra action by scaling the algebra element. -/
theorem scalarMul_action (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : k) (a : A) (m : M) :
    scalarMul k hM c (a • m) = (c • a) • m := by
  obtain ⟨e, he⟩ := hA.exists_mem_corner a
  have hea := ((Idempotent.mem_corner_iff e a).mp he).1
  have hem : (e : A) • (a • m) = a • m := by rw [← mul_smul, hea]
  rw [scalarMul_eq k hA hM c (a • m) e hem, ← mul_smul, smul_mul_assoc, hea]

/-- The original action commutes with the raw scalars. -/
theorem action_scalarMul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : k) (a : A) (m : M) :
    a • scalarMul k hM c m = (c • a) • m := by
  obtain ⟨e, he⟩ := hM m
  rw [scalarMul_eq k hA hM c m e he, ← mul_smul, mul_smul_comm,
    ← smul_mul_assoc, mul_smul, he]

/-- The actual canonical scalar module, retaining the given additive group and A-action.
This definition is installed only locally. -/
noncomputable abbrev module (k : Type uK) {A : Type uA} {M : Type uM}
    [CommSemiring k] [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    Module k M where
  smul := scalarMul k hM
  one_smul m := by
    change scalarMul k hM 1 m = m
    rw [scalarMul, one_smul]
    exact (hM m).choose_spec
  mul_smul c d m := by
    change scalarMul k hM (c * d) m = scalarMul k hM c (scalarMul k hM d m)
    obtain ⟨e, he⟩ := hM m
    rw [scalarMul_eq k hA hM d m e he, scalarMul_action k hA hM,
      scalarMul_eq k hA hM (c * d) m e he, mul_smul]
  smul_zero c := by
    change scalarMul k hM c 0 = 0
    exact smul_zero _
  smul_add c m n := by
    classical
    change scalarMul k hM c (m + n) = scalarMul k hM c m + scalarMul k hM c n
    obtain ⟨e, he⟩ := hM m
    obtain ⟨f, hf⟩ := hM n
    obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
    have hgm := Idempotent.smul_eq_of_le (hg e (by simp)) he
    have hgn := Idempotent.smul_eq_of_le (hg f (by simp)) hf
    have hgs : (g : A) • (m + n) = m + n := by rw [smul_add, hgm, hgn]
    rw [scalarMul_eq k hA hM c (m + n) g hgs, scalarMul_eq k hA hM c m g hgm,
      scalarMul_eq k hA hM c n g hgn, smul_add]
  add_smul c d m := by
    change scalarMul k hM (c + d) m = scalarMul k hM c m + scalarMul k hM d m
    simp only [scalarMul, add_smul, NonUnitalModule.add_smul]
  zero_smul m := by
    change scalarMul k hM 0 m = 0
    simp only [scalarMul, zero_smul, NonUnitalModule.zero_smul]

/-- The canonical module satisfies the source formula for every fixer. -/
theorem smul_eq (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : k) (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    letI := module k hA hM
    c • m = (c • (e : A)) • m :=
  scalarMul_eq k hA hM c m e he

/-- First compatibility identity of I.2.1.1. -/
theorem smul_action (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : k) (a : A) (m : M) :
    letI := module k hA hM
    c • (a • m) = (c • a) • m :=
  scalarMul_action k hA hM c a m

/-- Second compatibility identity of I.2.1.1. -/
theorem action_smul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : k) (a : A) (m : M) :
    letI := module k hA hM
    a • (c • m) = (c • a) • m :=
  action_scalarMul k hA hM c a m

/-- Named local scalar-tower adapter for the constructed module. -/
theorem isScalarTower (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := module k hA hM
    IsScalarTower k A M := by
  let _ := module k hA hM
  exact ⟨fun c a m => (smul_action k hA hM c a m).symm⟩

/-- Named local commuting-action adapter for the constructed module. -/
theorem smulCommClass (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := module k hA hM
    SMulCommClass k A M := by
  let _ := module k hA hM
  exact ⟨fun c a m => (smul_action k hA hM c a m).trans
    (action_smul k hA hM c a m).symm⟩

/-- The retained original action as the published actual linear-endomorphism homomorphism. -/
noncomputable def toLinearEndHom (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := module k hA hM
    A →ₙₐ[k] Module.End k M :=
  letI := module k hA hM
  letI := isScalarTower k hA hM
  letI := smulCommClass k hA hM
  NonUnitalModule.toLinearEndHom k

@[simp] theorem toLinearEndHom_apply (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (a : A) (m : M) : toLinearEndHom k hA hM a m = a • m := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Any compatible existing scalar multiplication satisfies the same raw formula.
Only the scalar-tower half of compatibility is needed for this comparison. -/
theorem scalarMul_eq_of_compatible [Module k M] [IsScalarTower k A M]
    (hM : IsNondegenerate A M) (c : k) (m : M) :
    scalarMul k hM c m = c • m := by
  rw [scalarMul, smul_assoc, (hM m).choose_spec]

/-- Uniqueness on the specified additive group and original algebra action. -/
theorem module_eq_of_compatible [h : Module k M] [IsScalarTower k A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    module k hA hM = h :=
  Module.ext' _ _ (scalarMul_eq_of_compatible k hM)

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

omit [SMulCommClass k A A] in
/-- An original additive intertwiner automatically preserves the raw scalars. -/
theorem map_scalarMul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N) (c : k) (m : M) :
    f (scalarMul k hM c m) = scalarMul k hN c (f m) := by
  obtain ⟨e, he⟩ := hM m
  have hef : (e : A) • f m = f m := (f.map_smul e m).symm.trans (congrArg f he)
  rw [scalarMul_eq k hA hM c m e he, scalarMul_eq k hA hN c (f m) e hef,
    f.map_smul]

/-- Automatic scalar linearity, with both constructed module structures explicit. -/
theorem map_smul (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N) (c : k) (m : M) :
    letI := module k hA hM
    letI := module k hA hN
    f (c • m) = c • f m :=
  map_scalarMul k hA hM hN f c m

/-- The published linear-intertwiner conversion, with its linearity proved here. -/
noncomputable def toLinearIntertwiner (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    letI := module k hA hM
    letI := module k hA hN
    LinearIntertwiner (toLinearEndHom k hA hM) (toLinearEndHom k hA hN) :=
  letI := module k hA hM
  letI := module k hA hN
  letI := isScalarTower k hA hM
  letI := smulCommClass k hA hM
  letI := isScalarTower k hA hN
  letI := smulCommClass k hA hN
  f.toLinearIntertwiner k (map_smul k hA hM hN f)

@[simp] theorem toLinearIntertwiner_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (m : M) :
    toLinearIntertwiner k hA hM hN f m = f m := rfl

/-- Forgetting by the published conversion recovers the specified original intertwiner. -/
@[simp] theorem ofLinearIntertwiner_toLinearIntertwiner (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    letI := module k hA hM
    letI := module k hA hN
    letI := isScalarTower k hA hM
    letI := smulCommClass k hA hM
    letI := isScalarTower k hA hN
    letI := smulCommClass k hA hN
    NonUnitalModuleHom.ofLinearIntertwiner (toLinearIntertwiner k hA hM hN f) = f := rfl

/-- The actual scalar-linear map of an original additive intertwiner. -/
noncomputable def toLinearMap (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    letI := module k hA hM
    letI := module k hA hN
    M →ₗ[k] N :=
  letI := module k hA hM
  letI := module k hA hN
  (toLinearIntertwiner k hA hM hN f).toLinearMap

@[simp] theorem toLinearMap_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (m : M) :
    toLinearMap k hA hM hN f m = f m := rfl

/-- The adapter retains the entire additive map, not just pointwise values. -/
@[simp] theorem toLinearMap_toAddMonoidHom (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    (toLinearMap k hA hM hN f).toAddMonoidHom = f.toAddMonoidHom := rfl

@[simp] theorem toLinearMap_id (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    letI := module k hA hM
    toLinearMap k hA hM hM (NonUnitalModuleHom.id A M) = LinearMap.id := rfl

variable {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]

@[simp] theorem toLinearMap_comp (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N) (hP : IsNondegenerate A P)
    (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    letI := module k hA hM
    letI := module k hA hN
    letI := module k hA hP
    toLinearMap k hA hM hP (g.comp f) =
      (toLinearMap k hA hN hP g).comp (toLinearMap k hA hM hN f) := rfl

end General

section Unital

variable (k : Type uK) {R : Type uA} {M : Type uM}
  [CommSemiring k] [Ring R] [Algebra k R] [AddCommGroup M] [NonUnitalModule R M]

/-- Unital source specialization, without a supplied scalar module on the carrier. -/
noncomputable abbrev unitalModule (hM : IsUnitalModule R M) : Module k M :=
  module k (IsIdempotented.of_ring R) (isNondegenerate_iff_isUnitalModule.mpr hM)

/-- In a unital algebra, the scalar formula uses the global unit. -/
theorem unital_smul_eq (hM : IsUnitalModule R M) (c : k) (m : M) :
    letI := unitalModule k hM
    c • m = (c • (1 : R)) • m :=
  smul_eq k (IsIdempotented.of_ring R) (isNondegenerate_iff_isUnitalModule.mpr hM)
    c m ⟨1, IsIdempotentElem.one⟩ (hM m)

end Unital

section Complex

variable {A : Type uA} {M : Type uM} {N : Type uN}
  [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [AddCommGroup M] [NonUnitalModule A M] [AddCommGroup N] [NonUnitalModule A N]

/-- Renard's exact complex scalar module on the original nondegenerate carrier. -/
noncomputable abbrev complexModule (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    Module ℂ M :=
  module ℂ hA hM

/-- The exact complex construction has the formula for every fixing idempotent. -/
theorem complex_smul_eq (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (c : ℂ) (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    letI := complexModule hA hM
    c • m = (c • (e : A)) • m :=
  smul_eq ℂ hA hM c m e he

/-- Automatic complex linearity in independent algebra and carrier universes. -/
noncomputable def complexToLinearMap (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) :
    letI := complexModule hA hM
    letI := complexModule hA hN
    M →ₗ[ℂ] N :=
  toLinearMap ℂ hA hM hN f

@[simp] theorem complexToLinearMap_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (m : M) :
    complexToLinearMap hA hM hN f m = f m := rfl

end Complex

end Langlands.Algebra.NondegenerateScalars
