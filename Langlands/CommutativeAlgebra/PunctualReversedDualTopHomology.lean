import Langlands.CommutativeAlgebra.FiniteFreeReversedDual
import Langlands.CommutativeAlgebra.PunctualDualCokernel
import Langlands.CommutativeAlgebra.PunctualMinimalModel

/-! # Top homology of the reversed dual of a punctual complex -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency.types false in
/-- The top homology of a reversed dual is the cokernel of the dual
first differential when the original complex is supported in nonnegative degrees. -/
def reversedDualTopHomologyIsoCokernel (g : ℤ)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hGE : L.IsStrictlyGE 0) :
    (reversedDual g L).homology g ≅
      cokernel (ModuleCat.ofHom (L.d 0 1).hom.dualMap) := by
  let D := reversedDual g L
  have hLE : D.IsStrictlyLE g := by
    simpa using reversedDual_isStrictlyLE g 0 L hGE
  have := hLE
  have hnext : D.d g (g + 1) = 0 :=
    (D.isZero_of_isStrictlyLE g (g + 1) (by omega)).eq_of_tgt _ _
  let e := D.isoHomologyι g (g + 1) (CochainComplex.next ℤ g) hnext ≪≫
    (D.sc g).opcyclesIsoCokernel
  have h₀ : g - g = 0 := sub_self _
  have h₁ : g - (ComplexShape.up ℤ).prev g = 1 := by
    rw [CochainComplex.prev]
    omega
  let e₀ : D.X g ≅ ModuleCat.of R (Module.Dual R (L.X 0)) :=
    (L.XIsoOfEq h₀).toLinearEquiv.dualMap.symm.toModuleIso
  let e₁ : D.X ((ComplexShape.up ℤ).prev g) ≅
      ModuleCat.of R (Module.Dual R (L.X 1)) :=
    (L.XIsoOfEq h₁).toLinearEquiv.dualMap.symm.toModuleIso
  refine e ≪≫ cokernel.mapIso _ _ e₁ e₀ ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change Module.Dual R (L.X (g - (ComplexShape.up ℤ).prev g)) at f
  ext x
  change f ((L.d (g - g) (g - (ComplexShape.up ℤ).prev g)).hom
      ((L.XIsoOfEq h₀).inv.hom x)) =
    f ((L.XIsoOfEq h₁).inv.hom ((L.d 0 1).hom x))
  apply congrArg f
  have hd : (L.XIsoOfEq h₀).inv ≫ L.d (g - g) (g - (ComplexShape.up ℤ).prev g) =
      L.d 0 1 ≫ (L.XIsoOfEq h₁).inv := by simp
  exact congrArg (fun z => z.hom x) hd

/-- The order-ideal criterion identifies this homology with the residue field. -/
def reversedDualTopHomologyIsoResidueField [IsLocalRing R] (g : ℤ)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hGE : L.IsStrictlyGE 0)
    (e₀ : L.X 0 ≃ₗ[R] R)
    (hI : firstDifferentialOrderIdeal L e₀ = maximalIdeal R) :
    (reversedDual g L).homology g ≅ ModuleCat.of R (ResidueField R) :=
  reversedDualTopHomologyIsoCokernel g L hGE ≪≫
    firstDifferentialDualCokernelIsoResidueField L e₀ hI

/-- Minimality and the first-order quotient test determine the top dual homology. -/
def punctualModelReversedDualTopHomologyIsoResidueField
    [IsLocalRing R] [IsNoetherianRing R]
    {g : ℕ} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (M : PunctualMinimalModel R g K)
    (hK : ∀ J : Ideal R, maximalIdeal R ^ 2 ≤ J → J ⋖ maximalIdeal R →
      IsEmpty (((baseChange (Ideal.Quotient.mk J)).obj K).homology 0 ≅
        ModuleCat.of (R ⧸ J) (R ⧸ J))) :
    (reversedDual (g : ℤ) M.complex).homology (g : ℤ) ≅
      ModuleCat.of R (ResidueField R) := by
  have := (M.finiteFree.2 1).2
  exact reversedDualTopHomologyIsoResidueField (g : ℤ) M.complex M.strictlyGE
    M.zeroEquiv (firstDifferentialOrderIdeal_eq_maximal M.complex M.strictlyGE
      M.zeroEquiv (M.minimal 0 1)
      (firstOrder_nonfree_of_homotopyEquiv M.complex K M.equiv hK))

end Langlands.CommutativeAlgebra
