import Langlands.Algebra.NondegenerateTensorScalars
import Langlands.Algebra.NondegenerateTensorFunctor

/-!
# Compatible coefficient-linear residual actions on original tensors

Derived internal infrastructure for Renard (9 July 2026), I.2.1–I.2.3.
The extra input compatibility is relative to the precise right-recovered
coefficient module on the first factor. All tensor structures remain the
published original ones.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalBimoduleTensorScalars

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)

universe uk uS uR uX uY

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

variable (k : Type uk) {S : Type uS} {R : Type uR}
  [CommRing k] [NonUnitalRing S] [NonUnitalRing R]
  [Module k R] [IsScalarTower k R R] [SMulCommClass k R R]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hR : IsIdempotented R) (hX : ActionsCommute S R X)
  (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y]
  (hY : IsNondegenerate R Y)

/-- The published tensor map, refined by the published canonical tensor coefficients. -/
noncomputable def linearEnd (s : S) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    Module.End k (Tensor R X Y) :=
  NondegenerateTensorScalars.linearMap k R hR hY hY
    (hX.leftActionHom s) (NonUnitalModuleHom.id R Y)

/-- Equality of the entire linear maps, for exactly the named tensor coefficients. -/
theorem linearEnd_eq (s : S) :
    linearEnd k hR hX Y hY s =
      NondegenerateTensorScalars.linearMap k R hR hY hY
        (hX.leftActionHom s) (NonUnitalModuleHom.id R Y) := rfl

/-- The entire original additive endomorphism is retained. -/
theorem linearEnd_toAddMonoidHom (s : S) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    (linearEnd k hR hX Y hY s).toAddMonoidHom =
      NonUnitalBimoduleTensor.leftScalar hX Y s := rfl

/-- Its entire additive map is the original balanced tensor map. -/
theorem linearEnd_toAddMonoidHom_eq_map (s : S) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    (linearEnd k hR hX Y hY s).toAddMonoidHom =
      NonUnitalModuleTensor.map R (hX.leftActionHom s) (NonUnitalModuleHom.id R Y) := rfl

@[simp] theorem linearEnd_tmul (s : S) (x : X) (y : Y) :
    linearEnd k hR hX Y hY s (tmul R X Y x y) = tmul R X Y (s • x) y := rfl

/-- The linear refinement acts by the exact original residual action on every tensor. -/
theorem linearEnd_apply (s : S) (t : Tensor R X Y) :
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    linearEnd k hR hX Y hY s t = s • t := rfl

/-- The original residual action commutes with the named tensor coefficients. -/
theorem action_smul (c : k) (s : S) (t : Tensor R X Y) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    s • (c • t) = c • (s • t) := by
  let _ := NondegenerateTensorScalars.module k R X Y hR hY
  exact (linearEnd k hR hX Y hY s).map_smul c t

/-- Named commutation adapter; no input coefficient compatibility is used here. -/
theorem smulCommClass :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    SMulCommClass k S (Tensor R X Y) := by
  let _ := NondegenerateTensorScalars.module k R X Y hR hY
  let _ := NonUnitalBimoduleTensor.leftModule hX Y
  exact ⟨fun c s t => (action_smul k hR hX Y hY c s t).symm⟩

section Compatible

variable [Module k S]

/-- The sufficient input law, with exactly the right-recovered coefficients on X. -/
abbrev InputCompatible (hRX : IsNondegenerate Rᵐᵒᵖ X) : Prop :=
  letI := NondegenerateTensorScalars.rightModule k hR hRX
  IsScalarTower k S X

/-- The input law stated without typeclass inference on X's coefficients. -/
theorem inputCompatible_iff (hRX : IsNondegenerate Rᵐᵒᵖ X) :
    InputCompatible k (S := S) hR hRX ↔
      (letI := NondegenerateTensorScalars.rightModule k hR hRX
       ∀ (c : k) (s : S) (x : X), (c • s) • x = c • (s • x)) := by
  let _ := NondegenerateTensorScalars.rightModule k hR hRX
  exact ⟨fun h => h.smul_assoc, fun h => ⟨h⟩⟩

/-- Coefficient linearity in the acting algebra element, extended from pure tensors. -/
theorem scalar_action (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (hcompat : InputCompatible k (S := S) hR hRX)
    (c : k) (s : S) (t : Tensor R X Y) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    (c • s) • t = c • (s • t) := by
  let _ := NondegenerateTensorScalars.rightModule k hR hRX
  let _ := NondegenerateTensorScalars.leftModule k hR hY
  let _ := NondegenerateTensorScalars.module k R X Y hR hY
  let _ := NonUnitalBimoduleTensor.leftModule hX Y
  let _ : IsScalarTower k S X := hcompat
  have h : NonUnitalBimoduleTensor.leftScalar hX Y (c • s) =
      (DistribSMul.toAddMonoidHom (Tensor R X Y) c).comp
        (NonUnitalBimoduleTensor.leftScalar hX Y s) :=
    NonUnitalModuleTensor.hom_ext R fun x y => by
      change tmul R X Y ((c • s) • x) y = c • tmul R X Y (s • x) y
      rw [smul_assoc c s x]
      exact (NondegenerateTensorScalars.smul_tmul_left k R X Y hR hRX hY c (s • x) y).symm
  exact DFunLike.congr_fun h t

/-- Named scalar-tower adapter for the exact tensor coefficients and residual action. -/
theorem isScalarTower (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (hcompat : InputCompatible k (S := S) hR hRX) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    IsScalarTower k S (Tensor R X Y) := by
  let _ := NondegenerateTensorScalars.module k R X Y hR hY
  let _ := NonUnitalBimoduleTensor.leftModule hX Y
  exact ⟨scalar_action k hR hX Y hY hRX hcompat⟩

/-- The original residual action bundled as an actual nonunital coefficient-algebra hom. -/
noncomputable def action (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (hcompat : InputCompatible k (S := S) hR hRX) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    S →ₙₐ[k] Module.End k (Tensor R X Y) :=
  letI := NondegenerateTensorScalars.module k R X Y hR hY
  letI := NonUnitalBimoduleTensor.leftModule hX Y
  letI := isScalarTower k hR hX Y hY hRX hcompat
  letI := smulCommClass k hR hX Y hY
  NonUnitalModule.toLinearEndHom k

/-- The whole per-element linear endomorphism agrees with the published refinement. -/
theorem action_apply_eq_linearEnd (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (hcompat : InputCompatible k (S := S) hR hRX) (s : S) :
    action k hR hX Y hY hRX hcompat s = linearEnd k hR hX Y hY s := by
  let _ := NondegenerateTensorScalars.module k R X Y hR hY
  exact LinearMap.ext fun _ => rfl

/-- The entire additive endomorphism is the exact original residual scalar map. -/
theorem action_toAddMonoidHom (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (hcompat : InputCompatible k (S := S) hR hRX) (s : S) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    (action k hR hX Y hY hRX hcompat s).toAddMonoidHom =
      NonUnitalBimoduleTensor.leftScalar hX Y s := rfl

@[simp] theorem action_tmul (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (hcompat : InputCompatible k (S := S) hR hRX) (s : S) (x : X) (y : Y) :
    action k hR hX Y hY hRX hcompat s (tmul R X Y x y) = tmul R X Y (s • x) y := rfl

/-- Equality of the complete original action structures, not just pure-tensor values. -/
theorem ofLinearEndHom_action (hRX : IsNondegenerate Rᵐᵒᵖ X)
    (hcompat : InputCompatible k (S := S) hR hRX) :
    letI := NondegenerateTensorScalars.module k R X Y hR hY
    NonUnitalModule.ofLinearEndHom (action k hR hX Y hY hRX hcompat) =
      NonUnitalBimoduleTensor.leftModule hX Y := by
  let _ := NondegenerateTensorScalars.module k R X Y hR hY
  let _ := NonUnitalBimoduleTensor.leftModule hX Y
  let _ := isScalarTower k hR hX Y hY hRX hcompat
  let _ := smulCommClass k hR hX Y hY
  exact NonUnitalModule.ofLinearEndHom_toLinearEndHom

section Recovered

variable [IsScalarTower k S S] [SMulCommClass k S S]

/-- Intrinsic uniqueness compares the two actual Module structures on the same group. -/
theorem recoveredModule_eq (hS : IsIdempotented S) (hSX : IsNondegenerate S X)
    (hRX : IsNondegenerate Rᵐᵒᵖ X) (hcompat : InputCompatible k (S := S) hR hRX) :
    letI := NonUnitalBimoduleTensor.leftModule hX Y
    NondegenerateScalars.module k hS
        (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y) =
      NondegenerateTensorScalars.module k R X Y hR hY := by
  let _ := NonUnitalBimoduleTensor.leftModule hX Y
  let _ := NondegenerateTensorScalars.module k R X Y hR hY
  let _ := isScalarTower k hR hX Y hY hRX hcompat
  exact NondegenerateScalars.module_eq_of_compatible k hS
    (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y)

/-- The coefficient actions agree on all tensors, with both named modules explicit. -/
theorem recovered_smul_eq (hS : IsIdempotented S) (hSX : IsNondegenerate S X)
    (hRX : IsNondegenerate Rᵐᵒᵖ X) (hcompat : InputCompatible k (S := S) hR hRX)
    (c : k) (t : Tensor R X Y) :
    (letI := NonUnitalBimoduleTensor.leftModule hX Y
     letI := NondegenerateScalars.module k hS
       (NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y)
     c • t) =
    (letI := NondegenerateTensorScalars.module k R X Y hR hY
     c • t) := by
  exact congrArg (fun m : Module k (Tensor R X Y) => letI := m; c • t)
    (recoveredModule_eq k hR hX Y hY hS hSX hRX hcompat)

end Recovered
end Compatible

end Langlands.Algebra.NonUnitalBimoduleTensorScalars
