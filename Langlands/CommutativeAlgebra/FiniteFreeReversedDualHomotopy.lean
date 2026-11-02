import Langlands.CommutativeAlgebra.FiniteFreeReversedDual
import Mathlib.Algebra.Homology.Homotopy

/-! # Transposed chain maps and homotopies on reversed duals -/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R]

/-- The transpose of a cochain map, as a map between reversed duals in the opposite
direction. In degree `i` it is the transpose of the degree-`g - i` component. -/
def reversedDualMap (g : ℤ) {C D : CochainComplex (ModuleCat.{u} R) ℤ} (φ : C ⟶ D) :
    reversedDual g D ⟶ reversedDual g C where
  f i := ModuleCat.ofHom (φ.f (g - i)).hom.dualMap
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change Module.Dual R (D.X (g - i)) at f
    change @Eq (Module.Dual R (C.X (g - j))) _ _
    apply LinearMap.ext
    intro x
    change f ((φ.f (g - i)).hom ((C.d (g - j) (g - i)).hom x)) =
      f ((D.d (g - j) (g - i)).hom ((φ.f (g - j)).hom x))
    have h := congrArg (fun z => z.hom x) (φ.comm (g - j) (g - i))
    change (D.d (g - j) (g - i)).hom ((φ.f (g - j)).hom x) =
      (φ.f (g - i)).hom ((C.d (g - j) (g - i)).hom x) at h
    rw [h]

@[simp] theorem reversedDualMap_f_apply (g : ℤ) {C D : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : C ⟶ D) (i : ℤ) (f : Module.Dual R (D.X (g - i))) (x : C.X (g - i)) :
    (show Module.Dual R (C.X (g - i)) from ((reversedDualMap g φ).f i).hom f) x =
      f ((φ.f (g - i)).hom x) := rfl

@[simp] theorem reversedDualMap_id (g : ℤ) (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    reversedDualMap g (𝟙 C) = 𝟙 (reversedDual g C) := by
  ext i f
  rfl

theorem reversedDualMap_comp (g : ℤ) {C D E : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : C ⟶ D) (ψ : D ⟶ E) :
    reversedDualMap g (φ ≫ ψ) = reversedDualMap g ψ ≫ reversedDualMap g φ := by
  ext i f
  rfl

/-- Reversed duality as a functor on the opposite category of cochain complexes. -/
@[simps]
def reversedDualFunctor (g : ℤ) :
    (CochainComplex (ModuleCat.{u} R) ℤ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj C := reversedDual g C.unop
  map φ := reversedDualMap g φ.unop
  map_id C := reversedDualMap_id g C.unop
  map_comp φ ψ := reversedDualMap_comp g ψ.unop φ.unop

set_option backward.isDefEq.respectTransparency.types false in
/-- A homotopy between cochain maps transposes to a homotopy between the transposed maps
on reversed duals. The roles of the two boundary terms are exchanged. -/
def reversedDualHomotopy (g : ℤ) {C D : CochainComplex (ModuleCat.{u} R) ℤ} {φ ψ : C ⟶ D}
    (h : Homotopy φ ψ) : Homotopy (reversedDualMap g φ) (reversedDualMap g ψ) where
  hom i j := ModuleCat.ofHom (h.hom (g - j) (g - i)).hom.dualMap
  zero i j hij := by
    have hji : ¬ (ComplexShape.up ℤ).Rel (g - i) (g - j) := by
      simp only [ComplexShape.up_Rel] at hij ⊢
      omega
    rw [h.zero _ _ hji]
    ext f x
    change f (0 : D.X (g - i)) = 0
    exact map_zero f
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    have hc := h.comm (g - i)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (g - i) (g - i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (g - i - 1) (g - i) by simp)] at hc
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change Module.Dual R (D.X (g - i)) at f
    change @Eq (Module.Dual R (C.X (g - i))) _ _
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun z => z.hom x) hc
    change (φ.f (g - i)).hom x = (h.hom (g - i + 1) (g - i)).hom
      ((C.d (g - i) (g - i + 1)).hom x) +
      (D.d (g - i - 1) (g - i)).hom
        ((h.hom (g - i) (g - i - 1)).hom x) + (ψ.f (g - i)).hom x at hx
    have hi₁ : g - (i + 1) = g - i - 1 := by omega
    have hi₂ : g - (i - 1) = g - i + 1 := by omega
    change f ((φ.f (g - i)).hom x) = f ((D.d (g - (i + 1)) (g - i)).hom
      ((h.hom (g - i) (g - (i + 1))).hom x)) +
      f ((h.hom (g - (i - 1)) (g - i)).hom
        ((C.d (g - i) (g - (i - 1))).hom x)) + f ((ψ.f (g - i)).hom x)
    rw [hi₁, hi₂, hx]
    simp only [map_add]
    abel

/-- A homotopy equivalence transposes to a homotopy equivalence between reversed duals,
in the opposite direction. -/
def reversedDualHomotopyEquiv (g : ℤ) {C D : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv C D) : HomotopyEquiv (reversedDual g D) (reversedDual g C) where
  hom := reversedDualMap g e.hom
  inv := reversedDualMap g e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (reversedDualMap_comp g e.inv e.hom).symm).trans
      ((reversedDualHomotopy g e.homotopyInvHomId).trans
        (Homotopy.ofEq (reversedDualMap_id g D)))
  homotopyInvHomId :=
    (Homotopy.ofEq (reversedDualMap_comp g e.hom e.inv).symm).trans
      ((reversedDualHomotopy g e.homotopyHomInvId).trans
        (Homotopy.ofEq (reversedDualMap_id g C)))

@[simp] theorem reversedDualHomotopyEquiv_hom (g : ℤ)
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv C D) :
    (reversedDualHomotopyEquiv g e).hom = reversedDualMap g e.hom := rfl

@[simp] theorem reversedDualHomotopyEquiv_inv (g : ℤ)
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv C D) :
    (reversedDualHomotopyEquiv g e).inv = reversedDualMap g e.inv := rfl

/-- Homotopy equivalent complexes have isomorphic reversed-dual homology in every degree. -/
def reversedDualHomologyIsoOfHomotopyEquiv (g : ℤ)
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv C D) (i : ℤ) :
    (reversedDual g D).homology i ≅ (reversedDual g C).homology i :=
  (reversedDualHomotopyEquiv g e).toHomologyIso i

/-- Isomorphic complexes have isomorphic reversed duals. -/
def reversedDualIsoOfIso (g : ℤ) {C D : CochainComplex (ModuleCat.{u} R) ℤ} (e : C ≅ D) :
    reversedDual g D ≅ reversedDual g C where
  hom := reversedDualMap g e.hom
  inv := reversedDualMap g e.inv
  hom_inv_id := by
    rw [← reversedDualMap_comp, e.inv_hom_id, reversedDualMap_id]
  inv_hom_id := by
    rw [← reversedDualMap_comp, e.hom_inv_id, reversedDualMap_id]

end Langlands.CommutativeAlgebra
