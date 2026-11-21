import Langlands.Automorphic.CuspidalHilbertActionCompatibility
import Langlands.Automorphic.CuspidalHilbertIntertwinerCore
import Langlands.Automorphic.AdelicHilbertCoordinateActions

/-! # Source-vector values of the two completed operators -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Operator

namespace Langlands.Automorphic.OperatorUnitaryFormCore

variable {G K A V X : Type*} [Group G] [Group K] [Group A] [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {κ : Representation ℂ K V} {D : X → Module.End ℂ V}
  (b : OperatorUnitaryFormCore ρ κ D)
  (U : A →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion)) (ιG : G → A) (ιK : K → A)

/-- Evaluating the compatible bounded actions on an embedded source vector gives
the images of the prescribed algebraic actions. -/
theorem completedActions_toHilbert
    (h : b.BoundedActionCompatibility U ιG ιK) :
    (∀ g v, U (ιG g) (b.toHilbert v) = b.toHilbert (ρ g v)) ∧
      (∀ k v, U (ιK k) (b.toHilbert v) = b.toHilbert (κ k v)) :=
  ⟨fun g v => (h.1 g (b.toHilbert v)).trans (b.completedFiniteOperator_toHilbert g v),
    fun k v => (h.2 k (b.toHilbert v)).trans (b.completedCompactOperator_toHilbert k v)⟩

end Langlands.Automorphic.OperatorUnitaryFormCore

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Global Langlands.Automorphic.CuspidalFixedSmoothDensity

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}
  {V X : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V} {D : X → Module.End ℂ V}
  {b : OperatorUnitaryFormCore ρ κ D} (B : AdelicCompletion b)

/-- The finite and compact coordinate actions carry source vectors exactly
to the Hilbert images of their original translates. -/
theorem coordinateActions_toHilbert :
    (∀ d v, finiteHilbertAction F n B.action d (b.toHilbert v) = b.toHilbert (ρ d v)) ∧
      (∀ k v, b.toHilbert (κ k v) =
        infiniteHilbertAction F n B.action (archimedeanGLCoordinates F n k.val) (b.toHilbert v)) := by
  have h := b.completedActions_toHilbert B.action (AdelicGL.ofFinite F n)
    (fun k : standardInfiniteCompact F n => AdelicGL.ofInfinite F n k.val) B.boundedCompatibility
  exact ⟨h.1, fun k v => (h.2 k v).symm.trans
    (infiniteHilbertAction_compactCoordinates_apply F n B.action k (b.toHilbert v)).symm⟩

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
