import Langlands.Algebra.NonUnitalBimoduleTensorScalars
import Langlands.Algebra.NonUnitalBimoduleHomScalarsParts
import Langlands.Algebra.NonUnitalModuleDual

/-!
# Actual compatible-input tensor-dual evaluation maps

Derived internal infrastructure for Renard (9 July 2026), I.4.2. The input
compatibility is relative to the coefficients recovered from the original
right action on X. No comparison equivalence is bundled here.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalTensorDualMaps

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)

universe uS uR uX uM

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

variable {S : Type uS} {R : Type uR} {X : Type uX} {M : Type uM}
  [NonUnitalRing S] [NonUnitalRing R]
  [Module ℂ S] [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]
  [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup M] [NonUnitalModule R M]
  (hS : IsIdempotented S) (hR : IsIdempotented R)
  (hX : ActionsCommute S R X) (hSX : IsNondegenerate S X)
  (hRX : IsNondegenerate Rᵐᵒᵖ X) (hM : IsNondegenerate R M)

/-- Exactly the full dual recovered from the published residual tensor action. -/
abbrev FullDual :=
  letI := NonUnitalBimoduleTensor.leftModule hX M
  NonUnitalModuleDual.FullDual hS
    (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)

/-- Exactly its actual nondegenerate dual subtype. -/
abbrev Dual :=
  letI := NonUnitalBimoduleTensor.leftModule hX M
  NonUnitalModuleDual.Dual hS
    (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)

local instance targetAction : NonUnitalModule Rᵐᵒᵖ (NonUnitalModuleDual.Dual hR hM) :=
  NonUnitalModuleDual.dualAction hR hM

/-- The original right-module Hom into the actual nondegenerate dual. -/
abbrev Hom := NonUnitalModuleHom Rᵐᵒᵖ X (NonUnitalModuleDual.Dual hR hM)

omit [IsScalarTower ℂ S S] [SMulCommClass ℂ S S] in
/-- The two published sufficient-input formulations use the same selected module. -/
theorem inputCompatible_iff_rightSourceCompatible :
    NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX ↔
      NonUnitalBimoduleHomScalars.RightSourceCompatible ℂ (R := S) hR hRX := Iff.rfl

variable (hc : NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX)

include hRX hc in
/-- Equality of the exact S-recovered tensor module and the named tensor module. -/
theorem tensorModule_eq :
    letI := NonUnitalBimoduleTensor.leftModule hX M
    NondegenerateScalars.module ℂ hS
        (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M) =
      NondegenerateTensorScalars.module ℂ R X M hR hM :=
  NonUnitalBimoduleTensorScalars.recoveredModule_eq ℂ hR hX M hM hS hSX hRX hc

/-- The same entire functional, transferred using the proved tensor coefficient equality. -/
def coefficientFunctional (ell : FullDual (M := M) hS hX hSX) :
    letI := NondegenerateTensorScalars.module ℂ R X M hR hM
    Tensor R X M →ₗ[ℂ] ℂ := by
  letI := NonUnitalBimoduleTensor.leftModule hX M
  letI := NondegenerateScalars.module ℂ hS
    (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)
  have hs := ell.map_smul'
  letI := NondegenerateTensorScalars.module ℂ R X M hR hM
  refine { toFun := ell, map_add' := ell.map_add', map_smul' := ?_ }
  intro c t
  have heq := NonUnitalBimoduleTensorScalars.recovered_smul_eq ℂ hR hX M hM
    hS hSX hRX hc c t
  exact (congrArg ell heq.symm).trans (hs c t)

theorem coefficientFunctional_toAddMonoidHom (ell : FullDual (M := M) hS hX hSX) :
    (coefficientFunctional hS hR hX hSX hRX hM hc ell).toAddMonoidHom =
      ell.toAddMonoidHom := rfl

/-- Evaluation at x is an actual complex-linear functional on the original M. -/
def evaluate (ell : FullDual (M := M) hS hX hSX) (x : X) :
    NonUnitalModuleDual.FullDual hR hM := by
  letI := NondegenerateScalars.module ℂ hR hM
  letI := NondegenerateTensorScalars.module ℂ R X M hR hM
  refine { toFun := fun m => ell (tmul R X M x m), map_add' := ?_, map_smul' := ?_ }
  · intro m n
    exact (congrArg ell (NonUnitalModuleTensor.tmul_add R X M x m n)).trans
      (ell.map_add' _ _)
  · intro c m
    change coefficientFunctional hS hR hX hSX hRX hM hc ell
      (tmul R X M x (c • m)) = c • ell (tmul R X M x m)
    rw [← NondegenerateTensorScalars.smul_tmul_right ℂ R X M hR hM]
    exact (coefficientFunctional hS hR hX hSX hRX hM hc ell).map_smul c _

/-- Equality of the entire underlying function. -/
theorem evaluate_function (ell : FullDual (M := M) hS hX hSX) (x : X) :
    (evaluate hS hR hX hSX hRX hM hc ell x : M → ℂ) =
      fun m => ell (tmul R X M x m) := rfl

@[simp] theorem evaluate_apply (ell : FullDual (M := M) hS hX hSX) (x : X) (m : M) :
    evaluate hS hR hX hSX hRX hM hc ell x m = ell (tmul R X M x m) := rfl

theorem evaluate_add (ell : FullDual (M := M) hS hX hSX) (x : X) (m n : M) :
    evaluate hS hR hX hSX hRX hM hc ell x (m + n) =
      evaluate hS hR hX hSX hRX hM hc ell x m +
        evaluate hS hR hX hSX hRX hM hc ell x n :=
  (evaluate hS hR hX hSX hRX hM hc ell x).map_add' m n

theorem evaluate_smul (ell : FullDual (M := M) hS hX hSX) (x : X) (c : ℂ) (m : M) :
    letI := NondegenerateScalars.module ℂ hR hM
    evaluate hS hR hX hSX hRX hM hc ell x (c • m) =
      c • evaluate hS hR hX hSX hRX hM hc ell x m := by
  let := NondegenerateScalars.module ℂ hR hM
  exact (evaluate hS hR hX hSX hRX hM hc ell x).map_smul' c m

omit [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] in
include hRX in
/-- A right fixer is an actual idempotent of the original ring R. -/
theorem exists_right_idempotent (x : X) :
    ∃ e : Idempotent R, op (e : R) • x = x := by
  obtain ⟨e, he⟩ := hRX x
  refine ⟨⟨unop (e : Rᵐᵒᵖ), ?_⟩, he⟩
  exact congrArg unop e.property.eq

/-- Balancing turns that original fixer into a fixer of the evaluated functional. -/
theorem evaluate_fixed (ell : FullDual (M := M) hS hX hSX) (x : X)
    (e : Idempotent R) (he : op (e : R) • x = x) :
    letI := NonUnitalModuleDual.fullAction hR hM
    op (e : R) • evaluate hS hR hX hSX hRX hM hc ell x =
      evaluate hS hR hX hSX hRX hM hc ell x := by
  let := NondegenerateScalars.module ℂ hR hM
  apply LinearMap.ext
  intro m
  change ell (tmul R X M x ((e : R) • m)) = ell (tmul R X M x m)
  rw [← NonUnitalModuleTensor.tmul_balanced, he]

/-- Inner-dual landing is intrinsic, without nondegeneracy of the ambient full dual. -/
theorem evaluate_mem (ell : FullDual (M := M) hS hX hSX) (x : X) :
    letI := NonUnitalModuleDual.fullAction hR hM
    evaluate hS hR hX hSX hRX hM hc ell x ∈
      nondegeneratePart hR.op (NonUnitalModuleDual.FullDual hR hM) := by
  obtain ⟨e, he⟩ := exists_right_idempotent hRX x
  refine (NonUnitalModuleDual.mem_dual_iff hR hM _).2 ⟨e, ?_⟩
  intro m
  exact congrArg (fun f : NonUnitalModuleDual.FullDual hR hM => f m)
    (evaluate_fixed hS hR hX hSX hRX hM hc ell x e he)

/-- Actual ambient curry, including the original right-R intertwining law. -/
def curry (ell : FullDual (M := M) hS hX hSX) : Hom (X := X) hR hM where
  toFun x := ⟨evaluate hS hR hX hSX hRX hM hc ell x,
    evaluate_mem hS hR hX hSX hRX hM hc ell x⟩
  map_zero' := by
    let := NondegenerateScalars.module ℂ hR hM
    let := NonUnitalBimoduleTensor.leftModule hX M
    let := NondegenerateScalars.module ℂ hS
      (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    exact (congrArg ell (NonUnitalModuleTensor.zero_tmul R X M m)).trans ell.map_zero
  map_add' x y := by
    let := NondegenerateScalars.module ℂ hR hM
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    exact (congrArg ell (NonUnitalModuleTensor.add_tmul R X M x y m)).trans
      (ell.map_add' _ _)
  map_smul' r x := by
    let := NondegenerateScalars.module ℂ hR hM
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    change ell (tmul R X M (r • x) m) = ell (tmul R X M x (unop r • m))
    exact congrArg ell (NonUnitalModuleTensor.tmul_balanced R X M (unop r) x m)

@[simp] theorem curry_apply (ell : FullDual (M := M) hS hX hSX) (x : X) (m : M) :
    (curry hS hR hX hSX hRX hM hc ell x).val m = ell (tmul R X M x m) := rfl

/-- Entire two-variable function after the original dual inclusion. -/
theorem curry_function (ell : FullDual (M := M) hS hX hSX) :
    (fun x m => (curry hS hR hX hSX hRX hM hc ell x).val m) =
      fun x m => ell (tmul R X M x m) := rfl

/-- The actual biadditive evaluation pairing of an original right intertwiner. -/
def pairing (h : Hom (X := X) hR hM) : X →+ M →+ ℂ where
  toFun x := (h x).val.toAddMonoidHom
  map_zero' := by ext m; exact congrArg (fun f : NonUnitalModuleDual.Dual hR hM => f.val m) h.map_zero
  map_add' x y := by ext m; exact congrArg (fun f : NonUnitalModuleDual.Dual hR hM => f.val m) (h.map_add x y)

@[simp] theorem pairing_apply (h : Hom (X := X) hR hM) (x : X) (m : M) :
    pairing hR hM h x m = (h x).val m := rfl

/-- Its balancing is precisely the original right-R intertwining law. -/
theorem pairing_balanced (h : Hom (X := X) hR hM) :
    NonUnitalModuleTensor.IsBalanced R (pairing hR hM h) := by
  intro r x m
  exact congrArg (fun f : NonUnitalModuleDual.Dual hR hM => f.val m)
    (h.map_smul (op r) x)

/-- Evaluation is bilinear for exactly MX and MM, using automatic linearity of h. -/
def bilinearPairing (h : Hom (X := X) hR hM) :
    letI := NondegenerateScalars.module ℂ hR.op hRX
    letI := NondegenerateScalars.module ℂ hR hM
    X →ₗ[ℂ] M →ₗ[ℂ] ℂ := by
  letI := NondegenerateScalars.module ℂ hR.op hRX
  letI := NondegenerateScalars.module ℂ hR hM
  refine { toFun := fun x => (h x).val, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    exact congrArg Subtype.val (h.map_add x y)
  · intro c x
    have heq := NondegenerateScalars.map_smul ℂ hR.op hRX
      (NonUnitalModuleDual.isNondegenerate hR hM) h c x
    exact (congrArg Subtype.val heq).trans
      (NonUnitalModuleDual.canonical_smul_val hR hM c (h x))

theorem bilinearPairing_toBiadditive (h : Hom (X := X) hR hM) :
    letI := NondegenerateScalars.module ℂ hR.op hRX
    letI := NondegenerateScalars.module ℂ hR hM
    NondegenerateTensorScalars.toBiadditive (bilinearPairing hR hRX hM h) =
      pairing hR hM h := rfl

/-- The actual additive balanced quotient lift with no external lift certificate. -/
def uncurryAdd (h : Hom (X := X) hR hM) : Tensor R X M →+ ℂ :=
  NonUnitalModuleTensor.lift R (pairing hR hM h) (pairing_balanced hR hM h)

/-- Its actual coefficient-linear refinement on the named tensor module. -/
def uncurryCoefficient (h : Hom (X := X) hR hM) :
    letI := NondegenerateTensorScalars.module ℂ R X M hR hM
    Tensor R X M →ₗ[ℂ] ℂ :=
  NondegenerateTensorScalars.linearLift ℂ R X M hR hRX hM
    (bilinearPairing hR hRX hM h) (pairing_balanced hR hM h)

theorem uncurryCoefficient_toAddMonoidHom (h : Hom (X := X) hR hM) :
    (uncurryCoefficient hR hRX hM h).toAddMonoidHom = uncurryAdd hR hM h := rfl

/-- Actual ambient uncurry, transferred by the proved tensor module equality. -/
def uncurry (h : Hom (X := X) hR hM) : FullDual (M := M) hS hX hSX := by
  letI := NonUnitalBimoduleTensor.leftModule hX M
  letI := NondegenerateScalars.module ℂ hS
    (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)
  refine
    { toFun := uncurryAdd hR hM h
      map_add' := (uncurryAdd hR hM h).map_add
      map_smul' := ?_ }
  intro c t
  have heq := NonUnitalBimoduleTensorScalars.recovered_smul_eq ℂ hR hX M hM
    hS hSX hRX hc c t
  exact (congrArg (uncurryAdd hR hM h) heq).trans
    (by
      let := NondegenerateTensorScalars.module ℂ R X M hR hM
      exact (uncurryCoefficient hR hRX hM h).map_smul' c t)

/-- The entire underlying additive map is the actual original quotient lift. -/
theorem uncurry_toAddMonoidHom (h : Hom (X := X) hR hM) :
    (uncurry hS hR hX hSX hRX hM hc h).toAddMonoidHom =
      NonUnitalModuleTensor.lift R (pairing hR hM h) (pairing_balanced hR hM h) := rfl

theorem uncurry_function (h : Hom (X := X) hR hM) :
    (uncurry hS hR hX hSX hRX hM hc h : Tensor R X M → ℂ) =
      NonUnitalModuleTensor.lift R (pairing hR hM h) (pairing_balanced hR hM h) := rfl

@[simp] theorem uncurry_tmul (h : Hom (X := X) hR hM) (x : X) (m : M) :
    uncurry hS hR hX hSX hRX hM hc h (tmul R X M x m) = (h x).val m := rfl

end Langlands.Algebra.NonUnitalTensorDualMaps
