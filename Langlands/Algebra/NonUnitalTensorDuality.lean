import Langlands.Algebra.NonUnitalTensorDualMapsParts
import Langlands.Algebra.NonUnitalModuleDualFunctor
import Langlands.Algebra.NondegenerateRightHomFunctor

/-! # Compatible-input tensor–dual natural isomorphism -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalTensorDuality

open CategoryTheory MulOpposite
open NonUnitalModuleTensor (Tensor tmul)
open NonUnitalTensorDualMaps

universe uS uR uX v

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

variable {S : Type uS} {R : Type uR} {X : Type uX}
  [NonUnitalRing S] [NonUnitalRing R]
  [Module ℂ S] [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]
  [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hS : IsIdempotented S) (hR : IsIdempotented R)
  (hX : ActionsCommute S R X) (hSX : IsNondegenerate S X)
  (hRX : IsNondegenerate Rᵐᵒᵖ X)
  (hc : NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX)

/-- Uncurrying and currying on the actual nondegenerate Hom part are inverse. -/
theorem curryPart_uncurryPart (M : NondegenerateModuleCat.{uR, v} R)
    (h : HomPart hS hR hX M.property) :
    curryPart hS hR hX hSX hRX M.property hc
      (uncurryPart hS hR hX hSX hRX M.property hc h) = h := by
  apply Subtype.ext
  apply NonUnitalModuleHom.ext
  intro x
  apply NonUnitalModuleDual.dual_ext hR M.property
  intro m
  rfl

/-- Currying and uncurrying on the actual tensor dual are inverse. -/
theorem uncurryPart_curryPart (M : NondegenerateModuleCat.{uR, v} R)
    (ell : Dual (M := M.obj) hS hX hSX) :
    uncurryPart hS hR hX hSX hRX M.property hc
      (curryPart hS hR hX hSX hRX M.property hc ell) = ell := by
  apply Subtype.ext
  exact full_ext hS hX hSX (fun _ _ => rfl)

set_option maxHeartbeats 1200000 in
/-- Evaluation identifies the exact published Hom part and tensor dual objects. -/
def componentIso (M : NondegenerateModuleCat.{uR, v} R) :
    (NondegenerateRightHomFunctor.restrictedFunctor hX hS).obj
        (NonUnitalModuleDual.dualObject hR M) ≅
      NonUnitalModuleDual.dualObject hS
        ((NondegenerateTensorFunctor.restrictedFunctor hS hX hSX).obj M) where
  hom := ObjectProperty.homMk (uncurryPartHom hS hR hX hSX hRX M.property hc)
  inv := ObjectProperty.homMk (curryPartHom hS hR hX hSX hRX M.property hc)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact curryPart_uncurryPart hS hR hX hSX hRX hc M
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact uncurryPart_curryPart hS hR hX hSX hRX hc M

/-- The compatible-input comparison, natural in the original left R-module. -/
def naturalIso :
    NonUnitalModuleDual.leftToRightFunctor.{uR, v} hR ⋙
        NondegenerateRightHomFunctor.restrictedFunctor hX hS ≅
      (NondegenerateTensorFunctor.restrictedFunctor.{uS, uR, uX, v} hS hX hSX).op ⋙
        NonUnitalModuleDual.leftToRightFunctor hS :=
  NatIso.ofComponents (fun M => componentIso hS hR hX hSX hRX hc M.unop) (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro h
    apply Subtype.ext
    apply full_ext hS hX hSX
    intro x m
    rfl)

end Langlands.Algebra.NonUnitalTensorDuality
