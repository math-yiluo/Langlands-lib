import Langlands.GroupScheme.Cohomology.RegularCochains
import Langlands.GroupScheme.Lie.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Base change of regular module representations and cochains -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}} (K : CommAlgCat.{u} R)

local instance restrictedTestAlgebra (A : CommAlgCat.{u} K) : Algebra R A :=
  Algebra.compHom A (algebraMap R K)

local instance restrictedTestTower (A : CommAlgCat.{u} K) : IsScalarTower R K A :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Regard a test algebra over the new base as a test algebra over the old base. -/
abbrev restrictedTest (A : CommAlgCat.{u} K) : CommAlgCat.{u} R := CommAlgCat.of R A

def restrictedTestMap {A B : CommAlgCat.{u} K} (f : A ⟶ B) :
    restrictedTest K A ⟶ restrictedTest K B :=
  CommAlgCat.ofHom (f.hom.restrictScalars R)

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Cancel the scalar extension in the quasi-coherent coefficient functor. -/
def scalarExtensionCancel (A : CommAlgCat.{u} K) :
    ModulePoints (R := CommRingCat.of K) (K ⊗[R] M) A ≃ₗ[A]
      ModulePoints M (restrictedTest K A) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R K A A M

/-- Coefficient cancellation is natural in every algebra over the new base. -/
theorem scalarExtensionCancel_naturality {A B : CommAlgCat.{u} K} (f : A ⟶ B)
    (x : ModulePoints (R := CommRingCat.of K) (K ⊗[R] M) A) :
    scalarExtensionCancel K M B (modulePointMap (R := CommRingCat.of K) (K ⊗[R] M) f x) =
      modulePointMap M (restrictedTestMap K f) (scalarExtensionCancel K M A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    induction t using TensorProduct.inductionOn with
    | tmul k m =>
      simp only [modulePointMap_tmul, scalarExtensionCancel,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      change (k • f.hom a) ⊗ₜ[R] m = f.hom (k • a) ⊗ₜ[R] m
      rw [map_smul]
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {M} {H : GroupScheme (Spec R)}

/-- The pointwise action after base change, transferred by coefficient
cancellation and the actual affine pullback point equivalence. -/
def ModuleRepresentation.baseChangeAction (ρ : ModuleRepresentation M H)
    (A : CommAlgCat.{u} K) :
    ((GroupScheme.baseChange (algebraBaseMap R K)).obj H).affinePoints A →*
      (ModulePoints (R := CommRingCat.of K) (K ⊗[R] M) A ≃ₗ[A]
        ModulePoints (R := CommRingCat.of K) (K ⊗[R] M) A) where
  toFun h := (scalarExtensionCancel K M A).trans
    ((ρ.action (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h)).trans
      (scalarExtensionCancel K M A).symm)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [map_one, LinearEquiv.trans_apply]
    exact (scalarExtensionCancel K M A).symm_apply_apply x
  map_mul' h k := by
    apply LinearEquiv.ext
    intro x
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply]

/-- Any natural regular module representation commutes with arbitrary base
change, with its coefficient module extended by the same base algebra. -/
def ModuleRepresentation.baseChange (ρ : ModuleRepresentation M H) :
    ModuleRepresentation (R := CommRingCat.of K) (K ⊗[R] M)
      ((GroupScheme.baseChange (algebraBaseMap R K)).obj H) where
  action A := ρ.baseChangeAction K A
  naturality {A B} f h x := by
    apply (scalarExtensionCancel K M B).injective
    change scalarExtensionCancel K M B
        (modulePointMap (R := CommRingCat.of K) (K ⊗[R] M) f
          ((scalarExtensionCancel K M A).symm
            (ρ.action (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h)
              (scalarExtensionCancel K M A x)))) =
      scalarExtensionCancel K M B
        ((scalarExtensionCancel K M B).symm
          (ρ.action (restrictedTest K B)
            (Lie.affineBaseChangeEquiv R K H B
              (((GroupScheme.baseChange (algebraBaseMap R K)).obj H).affinePointMap f h))
            (scalarExtensionCancel K M B
              (modulePointMap (R := CommRingCat.of K) (K ⊗[R] M) f x))))
    rw [scalarExtensionCancel_naturality, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, ρ.naturality, scalarExtensionCancel_naturality]
    congr 1

/-- Restrict a regular one-cochain to algebras over the new base and extend its
coefficient module by that base algebra. -/
def OneCochain.baseChange (c : OneCochain M H) :
    OneCochain (R := CommRingCat.of K) (K ⊗[R] M)
      ((GroupScheme.baseChange (algebraBaseMap R K)).obj H) where
  value A h := (scalarExtensionCancel K M A).symm
    (c.value (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h))
  naturality {A B} f h := by
    apply (scalarExtensionCancel K M B).injective
    rw [scalarExtensionCancel_naturality, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, c.naturality]
    congr 1

/-- The analogous actual restriction for regular two-cochains. -/
def TwoCochain.baseChange (c : TwoCochain M H) :
    TwoCochain (R := CommRingCat.of K) (K ⊗[R] M)
      ((GroupScheme.baseChange (algebraBaseMap R K)).obj H) where
  value A h k := (scalarExtensionCancel K M A).symm
    (c.value (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h)
      (Lie.affineBaseChangeEquiv R K H A k))
  naturality {A B} f h k := by
    apply (scalarExtensionCancel K M B).injective
    rw [scalarExtensionCancel_naturality, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, c.naturality]
    congr 1

/-- Actual base change preserves the one-cocycle equation. -/
theorem OneCochain.baseChange_isCocycle (ρ : ModuleRepresentation M H)
    (c : OneCochain M H) (hc : c.IsCocycle ρ) :
    (c.baseChange K).IsCocycle (ρ.baseChange K) := by
  intro A h k
  apply (scalarExtensionCancel K M A).injective
  simpa only [OneCochain.baseChange, ModuleRepresentation.baseChange,
    ModuleRepresentation.baseChangeAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply, map_add,
    LinearEquiv.apply_symm_apply, map_mul] using
      hc (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h)
        (Lie.affineBaseChangeEquiv R K H A k)

/-- Actual base change preserves the two-cocycle equation. -/
theorem TwoCochain.baseChange_isCocycle (ρ : ModuleRepresentation M H)
    (c : TwoCochain M H) (hc : c.IsCocycle ρ) :
    (c.baseChange K).IsCocycle (ρ.baseChange K) := by
  intro A h k l
  apply (scalarExtensionCancel K M A).injective
  simpa only [TwoCochain.baseChange, ModuleRepresentation.baseChange,
    ModuleRepresentation.baseChangeAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply, map_add,
    LinearEquiv.apply_symm_apply, map_mul] using
      hc (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h)
        (Lie.affineBaseChangeEquiv R K H A k) (Lie.affineBaseChangeEquiv R K H A l)

/-- An actual base-module coboundary primitive extends to the new base. -/
theorem OneCochain.baseChange_isCoboundary (ρ : ModuleRepresentation M H)
    (c : OneCochain M H) (hc : c.IsCoboundary ρ) :
    (c.baseChange K).IsCoboundary (ρ.baseChange K) := by
  obtain ⟨m, hm⟩ := hc
  refine ⟨(1 : K) ⊗ₜ[R] m, fun A h => ?_⟩
  apply (scalarExtensionCancel K M A).injective
  simpa only [OneCochain.baseChange, ModuleRepresentation.baseChange,
    ModuleRepresentation.baseChangeAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply, map_sub,
    LinearEquiv.apply_symm_apply, scalarExtensionCancel,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul] using
      hm (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h)

/-- A natural one-cochain primitive of a two-coboundary base changes to a
natural primitive for the base-changed two-cochain. -/
theorem TwoCochain.baseChange_isCoboundary (ρ : ModuleRepresentation M H)
    (c : TwoCochain M H) (hc : c.IsCoboundary ρ) :
    (c.baseChange K).IsCoboundary (ρ.baseChange K) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨b.baseChange K, fun A h k => ?_⟩
  apply (scalarExtensionCancel K M A).injective
  simpa only [OneCochain.baseChange, TwoCochain.baseChange,
    ModuleRepresentation.baseChange, ModuleRepresentation.baseChangeAction,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply, map_add, LinearEquiv.apply_symm_apply, map_mul] using
      hb (restrictedTest K A) (Lie.affineBaseChangeEquiv R K H A h)
        (Lie.affineBaseChangeEquiv R K H A k)

end Langlands.GroupScheme.Cohomology
