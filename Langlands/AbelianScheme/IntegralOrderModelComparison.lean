import Langlands.AbelianScheme.OrderSaturationExistence
import Langlands.AbelianScheme.RelativeIntegralActionComparison

/-! # Original rational algebra actions and their integral order models -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory AlgebraicGeometry Module

namespace Langlands.AbelianScheme.IntegralOrderModel

variable {S : Scheme.{u}} {A : AbelianScheme S}
  {R : Type v} [Ring R] [Algebra ℚ R]
  {O : Subalgebra ℤ R} [Submodule.IsLattice ℚ O.toSubmodule]
  {I : Type w} (b : Basis I ℤ O) (α : R →ₐ[ℚ] End0 A)
  (M : IntegralOrderModel (IntegralOrderExtension.restrict (O := O) α))

/-- The actual forward isogeny's rationalization intertwines every element of the
original rational algebra, not only its full integer order. -/
theorem rationalExtension_intertwines (x : R) :
    comp0 A A M.B (α x) (homToHom0 M.inverseData.hom) =
      comp0 A M.B M.B (homToHom0 M.inverseData.hom)
        (integralActionRationalExtension M.B b M.action x) := by
  let L : R →ₗ[ℚ] Hom0 A M.B :=
    ((comp0 A A M.B).flip (homToHom0 M.inverseData.hom)).comp α.toLinearMap
  let Q : R →ₗ[ℚ] Hom0 A M.B :=
    ((comp0 A M.B M.B) (homToHom0 M.inverseData.hom)).comp
      (integralActionRationalExtension M.B b M.action).toLinearMap
  have h : L = Q := by
    apply (b.extendOfIsLattice (M := O.toSubmodule) ℚ).ext
    intro i
    change comp0 A A M.B
        (α (b.extendOfIsLattice (M := O.toSubmodule) ℚ i))
        (homToHom0 M.inverseData.hom) =
      comp0 A M.B M.B (homToHom0 M.inverseData.hom)
        (integralActionRationalExtension M.B b M.action
          (b.extendOfIsLattice (M := O.toSubmodule) ℚ i))
    simp only [Basis.extendOfIsLattice_apply, integralActionRationalExtension_coe]
    exact (M.intertwines (b i)).symm
  exact DFunLike.congr_fun h x

/-- The original rational algebra action is equivariantly isomorphic to the full
rational extension of the actual integral order model. -/
def rationalAlgebraIso :
    RationalAlgebraAction.of A α ≅
      RationalAlgebraAction.of M.B (integralActionRationalExtension M.B b M.action) :=
  RationalAlgebraAction.isoMk M.inverseData.toIso
    (rationalExtension_intertwines b α M)

/-- The forward comparison is the rationalization of the actual quotient isogeny. -/
@[simp] theorem rationalAlgebraIso_hom :
    RationalAlgebraAction.hom0 (rationalAlgebraIso b α M).hom =
      homToHom0 M.inverseData.hom := rfl

/-- The inverse comparison retains its actual inverse-multiple map and denominator. -/
@[simp] theorem rationalAlgebraIso_inv :
    RationalAlgebraAction.hom0 (rationalAlgebraIso b α M).inv =
      (M.inverseData.multiple : ℚ)⁻¹ • homToHom0 M.inverseData.inv := rfl

/-- Equality belongs to the existing quotient by actual equivariant rational isomorphisms. -/
theorem rationalAction_classOf :
    RationalAlgebraAction.classOf (RationalAlgebraAction.of A α) =
      RationalAlgebraAction.classOf
        (RationalAlgebraAction.of M.B (integralActionRationalExtension M.B b M.action)) :=
  RationalAlgebraAction.classOf_eq_iff.mpr ⟨rationalAlgebraIso b α M⟩

end Langlands.AbelianScheme.IntegralOrderModel
