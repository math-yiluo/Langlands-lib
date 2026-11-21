import Langlands.Geometry.FormalGroup.PDivisibleGroupMorphisms
import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeHom
import Langlands.Geometry.FormalGroup.OrderAction
import Langlands.GroupScheme.Torus.Lattice

/-! # Formal module maps on their p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {π : O}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom

/-- Restriction of integral formal maps to the actual finite scalar kernels is additive. -/
theorem scalarTorsionSchemeMap_add (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    (f g : Hom M N) (n : ℕ) :
    (f + g).scalarTorsionSchemeMap hM hN n =
      f.scalarTorsionSchemeMap hM hN n + g.scalarTorsionSchemeMap hM hN n := by
  let U := hM.torsionKernelModel n
  let V := hN.torsionKernelModel n
  let a : U.commGroupScheme ⟶ V.commGroupScheme := f.scalarTorsionSchemeMap hM hN n
  let b : U.commGroupScheme ⟶ V.commGroupScheme := g.scalarTorsionSchemeMap hM hN n
  apply FiniteKernelModel.hom_ext_affinePoints (K := U) (L := V)
  intro A x
  let z := U.affinePointsEquiv A (Additive.ofMul x)
  have hsum : (f + g).scalarTorsionPointsMap π n A z =
      f.scalarTorsionPointsMap π n A z + g.scalarTorsionPointsMap π n A z := by
    apply Subtype.ext
    let θ := IsScalarTower.toAlgHom O R A
    have h : (f + g).map θ = f.map θ + g.map θ := (Hom.mapLinear θ).map_add f g
    change ((f + g).map θ).onPoints z.val = (f.map θ).onPoints z.val + (g.map θ).onPoints z.val
    rw [h]
    exact (f.map θ).onPoints_add (g.map θ) z.val
  have he : Additive.ofMul (x ≫ (a + b).toMul.hom.hom) =
      Additive.ofMul (x ≫ a.toMul.hom.hom) + Additive.ofMul (x ≫ b.toMul.hom.hom) :=
    congrArg Additive.ofMul (GroupScheme.comp_groupHom_add x a b)
  change V.affinePointsEquiv A (Additive.ofMul (x ≫
      ((f + g).scalarTorsionSchemeMap hM hN n).toMul.hom.hom)) =
    V.affinePointsEquiv A (Additive.ofMul (x ≫ (a + b).toMul.hom.hom))
  calc
    _ = (f + g).scalarTorsionPointsMap π n A z :=
      (f + g).scalarTorsionSchemeMap_affinePoints hM hN n x
    _ = f.scalarTorsionPointsMap π n A z + g.scalarTorsionPointsMap π n A z := hsum
    _ = V.affinePointsEquiv A (Additive.ofMul (x ≫ a.toMul.hom.hom)) +
        V.affinePointsEquiv A (Additive.ofMul (x ≫ b.toMul.hom.hom)) :=
      (congrArg₂ (· + ·) (f.scalarTorsionSchemeMap_affinePoints hM hN n x)
        (g.scalarTorsionSchemeMap_affinePoints hM hN n x)).symm
    _ = _ := (map_add (V.affinePointsEquiv A) _ _).symm.trans (congrArg (V.affinePointsEquiv A) he.symm)

variable {p : ℕ} [Fact p.Prime]

/-- A formal map induces a morphism of the actual p-divisible groups. -/
def pDivisibleMap (f : Hom M N) (hM : M.IsPiDivisible (p : O)) (hN : N.IsPiDivisible (p : O)) :
    hM.pDivisibleGroup ⟶ hN.pDivisibleGroup :=
  PDivisibleGroup.Hom.ofComponents (f.scalarTorsionSchemeMap hM hN)
    (fun i => f.scalarTorsionSchemeMap_inclusion hM hN i)
    (fun i => f.scalarTorsionSchemeMap_transition hM hN i)

@[simp] theorem pDivisibleMap_app (f : Hom M N) (hM : M.IsPiDivisible (p : O))
    (hN : N.IsPiDivisible (p : O)) (n : ℕ) :
    (f.pDivisibleMap hM hN).app n = f.scalarTorsionSchemeMap hM hN n := rfl

@[simp] theorem pDivisibleMap_id (hM : M.IsPiDivisible (p : O)) :
    (Hom.id M).pDivisibleMap hM hM = 𝟙 hM.pDivisibleGroup :=
  PDivisibleGroup.Hom.ext (scalarTorsionSchemeMap_id hM)

@[simp] theorem pDivisibleMap_comp (g : Hom N P) (f : Hom M N) (hM : M.IsPiDivisible (p : O))
    (hN : N.IsPiDivisible (p : O)) (hP : P.IsPiDivisible (p : O)) :
    (g.comp f).pDivisibleMap hM hP = f.pDivisibleMap hM hN ≫ g.pDivisibleMap hN hP :=
  PDivisibleGroup.Hom.ext (scalarTorsionSchemeMap_comp hM hN hP g f)

@[simp] theorem pDivisibleMap_add (f g : Hom M N) (hM : M.IsPiDivisible (p : O))
    (hN : N.IsPiDivisible (p : O)) :
    (f + g).pDivisibleMap hM hN = f.pDivisibleMap hM hN + g.pDivisibleMap hM hN :=
  PDivisibleGroup.Hom.ext (scalarTorsionSchemeMap_add hM hN f g)

/-- Restriction to the actual p-divisible group is an additive map on Hom groups. -/
def pDivisibleMapAdd (hM : M.IsPiDivisible (p : O)) (hN : N.IsPiDivisible (p : O)) :
    Hom M N →+ (hM.pDivisibleGroup ⟶ hN.pDivisibleGroup) :=
  AddMonoidHom.mk' (fun f => f.pDivisibleMap hM hN) (fun f g => pDivisibleMap_add f g hM hN)

/-- Restriction is a ring homomorphism on the formal endomorphisms. -/
def pDivisibleEnd (hM : M.IsPiDivisible (p : O)) : Hom M M →+* End hM.pDivisibleGroup where
  __ := pDivisibleMapAdd hM hM
  map_one' := pDivisibleMap_id hM
  map_mul' g f := pDivisibleMap_comp g f hM hM hM

end Hom

/-- The order acts on the p-divisible group through the actual endomorphisms
on the finite scalar kernels. -/
def OrderAction.pDivisibleAction {A : Type w} [Ring A] [Algebra O A]
    (E : OrderAction A M) {p : ℕ} [Fact p.Prime] (hM : M.IsPiDivisible (p : O)) :
    A →+* End hM.pDivisibleGroup :=
  (Hom.pDivisibleEnd hM).comp E.action

end Langlands.FormalGroup.ModuleLaw
