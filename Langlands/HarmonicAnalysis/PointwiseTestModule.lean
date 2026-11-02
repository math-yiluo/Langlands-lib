import Langlands.HarmonicAnalysis.PointwiseTestAlgebra
import Langlands.Algebra.NondegenerateScalars
import Mathlib.Algebra.Module.RingHom

/-!
# Smooth multipliers on original nondegenerate pointwise test modules

Renard (9 July 2026), II.2.5, printed p.39 / PDF45.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.HarmonicAnalysis.PointwiseTestModule

open Langlands.Algebra PointwiseTestAlgebra

universe uX uM uN uP

variable {X : Type uX} [TopologicalSpace X]

/-- Compatibility of the actual smooth multiplication with test multiplication. -/
instance testScalarTower :
    IsScalarTower (LocallyConstant X ℂ) (Carrier X) (Carrier X) where
  smul_assoc f a b := by
    ext x
    exact mul_assoc (f x) (a x) (b x)

/-- The actual smooth and test multiplications commute on tests. -/
instance testSMulCommClass :
    SMulCommClass (LocallyConstant X ℂ) (Carrier X) (Carrier X) where
  smul_comm f a b := by
    ext x
    exact mul_left_comm (f x) (a x) (b x)

variable {M : Type uM} [AddCommGroup M] [μM : NonUnitalModule (Carrier X) M]

/-- A compact-clopen characteristic fixes every original nondegenerate vector. -/
theorem exists_characteristic_fixer (hM : IsNondegenerate (Carrier X) M) (m : M) :
    ∃ (U : Set X) (hU : IsClopen U) (hc : IsCompact U),
      characteristic hU hc • m = m := by
  obtain ⟨e, he⟩ := hM m
  refine ⟨Function.support (e : Carrier X), isClopen_support (e : Carrier X),
    isCompact_support (e : Carrier X), ?_⟩
  have hunit : characteristic (isClopen_support (e : Carrier X))
      (isCompact_support (e : Carrier X)) * e = (e : Carrier X) :=
    (characteristic_mul_eq_self_iff _ _ _).mpr (Set.Subset.refl _)
  calc
    characteristic _ _ • m = characteristic _ _ • ((e : Carrier X) • m) :=
      congrArg (characteristic _ _ • ·) he.symm
    _ = m := by
      rw [← mul_smul (characteristic (isClopen_support (e : Carrier X))
        (isCompact_support (e : Carrier X))) (e : Carrier X) m, hunit, he]

/-- Nondegeneracy relative to compact-clopen indicators for a specified smooth action.
The original test action is retained explicitly, without a prior compatibility premise. -/
def IsRelativelyNondegenerate (_originalAction : NonUnitalModule (Carrier X) M)
    (σM : Module (LocallyConstant X ℂ) M) : Prop :=
  letI := σM
  ∀ m : M, ∃ (U : Set X) (hU : IsClopen U) (hc : IsCompact U),
    inclusion (characteristic hU hc) • m = m

/-- The unital smooth-function action on the original additive carrier. -/
abbrev module (hM : IsNondegenerate (Carrier X) M) :
    Module (LocallyConstant X ℂ) M :=
  NondegenerateScalars.module (LocallyConstant X ℂ) isIdempotented hM

/-- The source formula holds for every original fixing characteristic. -/
theorem smul_eq (hM : IsNondegenerate (Carrier X) M)
    (f : LocallyConstant X ℂ) (m : M) {U : Set X}
    (hU : IsClopen U) (hc : IsCompact U) (hm : characteristic hU hc • m = m) :
    letI := module hM
    f • m = (f • characteristic hU hc) • m :=
  NondegenerateScalars.smul_eq (LocallyConstant X ℂ) isIdempotented hM f m
    (characteristicIdempotent hU hc) hm

/-- Any two original fixing characteristics give the same smooth multiplier value. -/
theorem fixer_independent (f : LocallyConstant X ℂ) (m : M) {U V : Set X}
    (hU : IsClopen U) (hUc : IsCompact U) (hV : IsClopen V) (hVc : IsCompact V)
    (hmU : characteristic hU hUc • m = m) (hmV : characteristic hV hVc • m = m) :
    (f • characteristic hU hUc) • m = (f • characteristic hV hVc) • m :=
  NondegenerateScalars.fixer_independent (LocallyConstant X ℂ) isIdempotented f m
    (characteristicIdempotent hU hUc) (characteristicIdempotent hV hVc) hmU hmV

/-- The smooth action of an included test is exactly its specified original action. -/
theorem inclusion_smul (hM : IsNondegenerate (Carrier X) M) (a : Carrier X) (m : M) :
    letI := module hM
    inclusion a • m = a • m := by
  let _ := module hM
  obtain ⟨e, he⟩ := hM m
  rw [NondegenerateScalars.smul_eq (LocallyConstant X ℂ) isIdempotented hM
    (inclusion a) m e he, PointwiseTestAlgebra.inclusion_smul,
    mul_smul a (e : Carrier X) m, he]

/-- The constructed action has the source's relative nondegeneracy property. -/
theorem isRelativelyNondegenerate (hM : IsNondegenerate (Carrier X) M) :
    IsRelativelyNondegenerate μM (module hM) := by
  intro m
  obtain ⟨U, hU, hc, hm⟩ := exists_characteristic_fixer hM m
  exact ⟨U, hU, hc, (inclusion_smul hM _ m).trans hm⟩

/-- The formula also holds for every characteristic fixing the constructed smooth action. -/
theorem smul_eq_of_inclusion_fixes (hM : IsNondegenerate (Carrier X) M)
    (f : LocallyConstant X ℂ) (m : M) {U : Set X}
    (hU : IsClopen U) (hc : IsCompact U) :
    letI := module hM
    inclusion (characteristic hU hc) • m = m →
      f • m = (f • characteristic hU hc) • m := by
  let _ := module hM
  intro hm
  exact smul_eq hM f m hU hc ((inclusion_smul hM _ m).symm.trans hm)

/-- Smooth scalars pass through the original test action by multiplying the test. -/
theorem smul_action (hM : IsNondegenerate (Carrier X) M)
    (f : LocallyConstant X ℂ) (a : Carrier X) (m : M) :
    letI := module hM
    f • (a • m) = (f • a) • m :=
  NondegenerateScalars.smul_action (LocallyConstant X ℂ) isIdempotented hM f a m

/-- The original test action passes through the smooth scalars. -/
theorem action_smul (hM : IsNondegenerate (Carrier X) M)
    (f : LocallyConstant X ℂ) (a : Carrier X) (m : M) :
    letI := module hM
    a • (f • m) = (f • a) • m :=
  NondegenerateScalars.action_smul (LocallyConstant X ℂ) isIdempotented hM f a m

/-- Scalar-tower adapter derived from the actual pointwise action. -/
theorem isScalarTower (hM : IsNondegenerate (Carrier X) M) :
    letI := module hM
    IsScalarTower (LocallyConstant X ℂ) (Carrier X) M :=
  NondegenerateScalars.isScalarTower (LocallyConstant X ℂ) isIdempotented hM

/-- Commuting-action adapter derived from the actual pointwise action. -/
theorem smulCommClass (hM : IsNondegenerate (Carrier X) M) :
    letI := module hM
    SMulCommClass (LocallyConstant X ℂ) (Carrier X) M :=
  NondegenerateScalars.smulCommClass (LocallyConstant X ℂ) isIdempotented hM

/-- Constants act by the exact canonical complex module on the original carrier. -/
theorem const_smul (hM : IsNondegenerate (Carrier X) M) (c : ℂ) (m : M) :
    (letI := module hM; LocallyConstant.const X c • m) =
      (letI := NondegenerateScalars.module ℂ isIdempotented hM; c • m) := by
  change ((LocallyConstant.const X c) • ((hM m).choose : Carrier X)) • m =
    (c • ((hM m).choose : Carrier X)) • m
  rw [PointwiseTestAlgebra.const_smul]

/-- Actual restriction of the chosen smooth module along the constant ring homomorphism. -/
abbrev constantRestriction (hM : IsNondegenerate (Carrier X) M) : Module ℂ M :=
  letI := module hM
  Module.compHom M (LocallyConstant.constRingHom (X := X) (Y := ℂ))

/-- Equality of the restricted module with the exact published canonical complex module. -/
theorem constantRestriction_eq (hM : IsNondegenerate (Carrier X) M) :
    constantRestriction hM = NondegenerateScalars.module ℂ isIdempotented hM :=
  Module.ext' _ _ (const_smul hM)

variable {N : Type uN} [AddCommGroup N] [μN : NonUnitalModule (Carrier X) N]

/-- Every original additive intertwiner is smooth-linear for the two chosen extensions. -/
def toLinearMap (hM : IsNondegenerate (Carrier X) M)
    (hN : IsNondegenerate (Carrier X) N) (f : NonUnitalModuleHom (Carrier X) M N) :
    letI := module hM
    letI := module hN
    M →ₗ[LocallyConstant X ℂ] N :=
  NondegenerateScalars.toLinearMap (LocallyConstant X ℂ) isIdempotented hM hN f

@[simp]
theorem toLinearMap_apply (hM : IsNondegenerate (Carrier X) M)
    (hN : IsNondegenerate (Carrier X) N) (f : NonUnitalModuleHom (Carrier X) M N)
    (m : M) : toLinearMap hM hN f m = f m := rfl

/-- The entire underlying additive map is preserved. -/
@[simp]
theorem toLinearMap_toAddMonoidHom (hM : IsNondegenerate (Carrier X) M)
    (hN : IsNondegenerate (Carrier X) N) (f : NonUnitalModuleHom (Carrier X) M N) :
    (toLinearMap hM hN f).toAddMonoidHom = f.toAddMonoidHom := rfl

@[simp]
theorem toLinearMap_id (hM : IsNondegenerate (Carrier X) M) :
    letI := module hM
    toLinearMap hM hM (NonUnitalModuleHom.id (Carrier X) M) = LinearMap.id := rfl

variable {P : Type uP} [AddCommGroup P] [μP : NonUnitalModule (Carrier X) P]

@[simp]
theorem toLinearMap_comp (hM : IsNondegenerate (Carrier X) M)
    (hN : IsNondegenerate (Carrier X) N) (hP : IsNondegenerate (Carrier X) P)
    (g : NonUnitalModuleHom (Carrier X) N P) (f : NonUnitalModuleHom (Carrier X) M N) :
    letI := module hM
    letI := module hN
    letI := module hP
    toLinearMap hM hP (g.comp f) = (toLinearMap hN hP g).comp (toLinearMap hM hN f) := rfl

end Langlands.HarmonicAnalysis.PointwiseTestModule
