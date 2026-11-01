import Langlands.Algebra.NonUnitalModuleDual

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDual

open MulOpposite

universe uA uM uN uP

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)

/-- Extensionality for the actual full dual with explicitly recovered scalars. -/
@[ext] theorem fullDual_ext {φ ψ : FullDual hA hM} (h : ∀ m, φ m = ψ m) : φ = ψ := by
  let _ := NondegenerateScalars.complexModule hA hM
  exact LinearMap.ext h

/-- Extensionality for the actual subtype, evaluated as a functional. -/
@[ext] theorem dual_ext {φ ψ : Dual hA hM} (h : ∀ m, φ.val m = ψ.val m) : φ = ψ :=
  Subtype.ext (fullDual_ext hA hM h)

/-- Pullback is exactly the dual of the automatically linear original intertwiner. -/
def fullPullbackLinear (f : NonUnitalModuleHom A M N) :
    FullDual hA hN →ₗ[ℂ] FullDual hA hM :=
  letI := NondegenerateScalars.complexModule hA hM
  letI := NondegenerateScalars.complexModule hA hN
  (NondegenerateScalars.complexToLinearMap hA hM hN f).dualMap

theorem fullPullbackLinear_eq_dualMap (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    fullPullbackLinear hA hM hN f =
      (NondegenerateScalars.complexToLinearMap hA hM hN f).dualMap := rfl

theorem fullPullbackLinear_coe (f : NonUnitalModuleHom A M N) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    ⇑(fullPullbackLinear hA hM hN f) =
      fun φ => φ.comp (NondegenerateScalars.complexToLinearMap hA hM hN f) := rfl

@[simp] theorem fullPullbackLinear_apply (f : NonUnitalModuleHom A M N)
    (φ : FullDual hA hN) (m : M) :
    fullPullbackLinear hA hM hN f φ m = φ (f m) := rfl

section Actions

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hM) := fullAction hA hM
local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hN) := fullAction hA hN

/-- The same entire linear pullback, bundled as an original right intertwiner. -/
def fullPullback (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom Aᵐᵒᵖ (FullDual hA hN) (FullDual hA hM) where
  toAddMonoidHom := (fullPullbackLinear hA hM hN f).toAddMonoidHom
  map_smul' a φ := by
    apply fullDual_ext hA hM
    intro m
    change φ (a.unop • f m) = φ (f (a.unop • m))
    rw [f.map_smul]

theorem fullPullback_toAddMonoidHom (f : NonUnitalModuleHom A M N) :
    (fullPullback hA hM hN f).toAddMonoidHom =
      (fullPullbackLinear hA hM hN f).toAddMonoidHom := rfl

theorem fullPullback_coe (f : NonUnitalModuleHom A M N) :
    ⇑(fullPullback hA hM hN f) = ⇑(fullPullbackLinear hA hM hN f) := rfl

theorem fullPullback_apply_eq_comp (f : NonUnitalModuleHom A M N)
    (φ : FullDual hA hN) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    fullPullback hA hM hN f φ =
      φ.comp (NondegenerateScalars.complexToLinearMap hA hM hN f) := rfl

@[simp] theorem fullPullback_apply (f : NonUnitalModuleHom A M N)
    (φ : FullDual hA hN) (m : M) :
    fullPullback hA hM hN f φ m = φ (f m) := rfl

theorem fullPullback_map_smul (f : NonUnitalModuleHom A M N)
    (a : Aᵐᵒᵖ) (φ : FullDual hA hN) :
    fullPullback hA hM hN f (a • φ) = a • fullPullback hA hM hN f φ :=
  (fullPullback hA hM hN f).map_smul a φ

/-- Restrict the actual pullback to the actual nondegenerate parts. -/
def pullback (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom Aᵐᵒᵖ (Dual hA hN) (Dual hA hM) :=
  (fullPullback hA hM hN f).restrictNondegeneratePart hA.op

/-- The whole underlying map on the subtype, including its actual membership proof. -/
theorem pullback_coe (f : NonUnitalModuleHom A M N) :
    ⇑(pullback hA hM hN f) =
      fun φ => ⟨fullPullback hA hM hN f φ.val,
        (fullPullback hA hM hN f).map_mem_nondegeneratePart hA.op φ.property⟩ := rfl

theorem pullback_val (f : NonUnitalModuleHom A M N) (φ : Dual hA hN) :
    (pullback hA hM hN f φ).val = fullPullback hA hM hN f φ.val := rfl

theorem pullback_val_eq_comp (f : NonUnitalModuleHom A M N) (φ : Dual hA hN) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA hN
    (pullback hA hM hN f φ).val =
      φ.val.comp (NondegenerateScalars.complexToLinearMap hA hM hN f) := rfl

@[simp] theorem pullback_apply (f : NonUnitalModuleHom A M N) (φ : Dual hA hN) (m : M) :
    (pullback hA hM hN f φ).val m = φ.val (f m) := rfl

/-- The entire included functional is precomposition of the included original functional. -/
theorem inclusion_pullback (f : NonUnitalModuleHom A M N) :
    (inclusion hA hM).comp (pullback hA hM hN f) =
      (fullPullback hA hM hN f).comp (inclusion hA hN) := rfl

theorem fullPullback_id :
    fullPullback hA hM hM (NonUnitalModuleHom.id A M) =
      NonUnitalModuleHom.id Aᵐᵒᵖ (FullDual hA hM) := by
  apply NonUnitalModuleHom.ext
  intro φ
  exact fullDual_ext hA hM (fun _ => rfl)

theorem pullback_id :
    pullback hA hM hM (NonUnitalModuleHom.id A M) =
      NonUnitalModuleHom.id Aᵐᵒᵖ (Dual hA hM) := by
  apply NonUnitalModuleHom.ext
  intro φ
  exact dual_ext hA hM (fun _ => rfl)

theorem fullPullback_zero :
    fullPullback hA hM hN (0 : NonUnitalModuleHom A M N) = 0 := by
  let _ := NondegenerateScalars.complexModule hA hN
  apply NonUnitalModuleHom.ext
  intro φ
  apply fullDual_ext hA hM
  intro m
  exact φ.map_zero

theorem fullPullback_add (f g : NonUnitalModuleHom A M N) :
    fullPullback hA hM hN (f + g) =
      fullPullback hA hM hN f + fullPullback hA hM hN g := by
  let _ := NondegenerateScalars.complexModule hA hN
  apply NonUnitalModuleHom.ext
  intro φ
  apply fullDual_ext hA hM
  intro m
  exact φ.map_add (f m) (g m)

theorem pullback_zero :
    pullback hA hM hN (0 : NonUnitalModuleHom A M N) = 0 := by
  let _ := NondegenerateScalars.complexModule hA hN
  apply NonUnitalModuleHom.ext
  intro φ
  apply dual_ext hA hM
  intro m
  exact φ.val.map_zero

theorem pullback_add (f g : NonUnitalModuleHom A M N) :
    pullback hA hM hN (f + g) = pullback hA hM hN f + pullback hA hM hN g := by
  let _ := NondegenerateScalars.complexModule hA hN
  apply NonUnitalModuleHom.ext
  intro φ
  apply dual_ext hA hM
  intro m
  exact φ.val.map_add (f m) (g m)

variable {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]
  (hP : IsNondegenerate A P)

local instance : NonUnitalModule Aᵐᵒᵖ (FullDual hA hP) := fullAction hA hP

theorem fullPullback_comp (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    fullPullback hA hM hP (g.comp f) =
      (fullPullback hA hM hN f).comp (fullPullback hA hN hP g) := by
  apply NonUnitalModuleHom.ext
  intro φ
  exact fullDual_ext hA hM (fun _ => rfl)

theorem pullback_comp (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    pullback hA hM hP (g.comp f) =
      (pullback hA hM hN f).comp (pullback hA hN hP g) := by
  apply NonUnitalModuleHom.ext
  intro φ
  exact dual_ext hA hM (fun _ => rfl)

end Actions

/-! Full unapplied interfaces retain separate algebra/source/target universes. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (hN : IsNondegenerate A N) → NonUnitalModuleHom A M N →
    (FullDual hA hN →ₗ[ℂ] FullDual hA hM) := @fullPullbackLinear.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (hN : IsNondegenerate A N) → NonUnitalModuleHom A M N →
    letI := fullAction hA hM
    letI := fullAction hA hN
    NonUnitalModuleHom Aᵐᵒᵖ (Dual hA hN) (Dual hA hM) := @pullback.{uA, uM, uN}

end Langlands.Algebra.NonUnitalModuleDual
