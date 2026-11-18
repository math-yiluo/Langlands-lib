import Langlands.GroupScheme.HomScheme.AdicSystemBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Algebraizations of compatible adic Hom systems on test schemes -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A : Type u} [CommRing A] {I : Ideal A}
  {H G : GroupScheme (Spec (CommRingCat.of A))}

namespace System

/-- A family of homomorphisms over a test scheme `V` algebraizes a compatible system when its
evaluation on every test scheme over `V` that lies over some adic thickening is the
evaluation of the corresponding member of the system. -/
def IsAlgebraization (s : System I H G) {V : Over (Spec (CommRingCat.of A))}
    (a : RelativeHom H G V) : Prop :=
  ∀ (n : ℕ) {T : Over (Spec (CommRingCat.of A))} (t : T ⟶ V)
    (u : T.left ⟶ quotientSpec I n) (hu : u ≫ quotientMap I n = T.hom),
    evaluate t a = evaluate (Over.homMk u hu : T ⟶ Over.mk (quotientMap I n)) (s.hom n)

/-- Algebraizations are stable under evaluation along test-scheme maps. -/
theorem isAlgebraization_evaluate {s : System I H G} {V W : Over (Spec (CommRingCat.of A))}
    {a : RelativeHom H G V} (ha : s.IsAlgebraization a) (w : W ⟶ V) :
    s.IsAlgebraization (evaluate w a) := by
  intro n T t u hu
  rw [← evaluate_comp]
  exact ha n (t ≫ w) u hu

/-- The constant family of an actual homomorphism algebraizes its restriction system. -/
theorem isAlgebraization_restrict (f : H ⟶ G) (V : Over (Spec (CommRingCat.of A))) :
    (restrict I H G f).IsAlgebraization ((baseChange V.hom).map f) := by
  intro n T t u hu
  rw [evaluate_baseChange, restrict_hom]
  exact (evaluate_baseChange (Over.homMk u hu : T ⟶ Over.mk (quotientMap I n)) f).symm

end System

end Langlands.GroupScheme.HomScheme.Adic
