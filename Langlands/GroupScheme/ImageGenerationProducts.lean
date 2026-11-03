import Langlands.GroupScheme.ImageGeneration
import Langlands.GroupScheme.Products
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn

/-! # Actual finite powers and ordered product morphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {G K : GroupScheme B} {V : Over B}

/-- A finite power of an arbitrary scheme over the base. -/
abbrev finitePower (V : Over B) (n : ℕ) : Over B := ∏ᶜ fun _ : Fin n => V

/-- Points of the actual finite power are ordered families of source points. -/
def finitePowerPointsEquiv (V : Over B) (n : ℕ) (T : Over B) :
    (T ⟶ finitePower V n) ≃ (Fin n → (T ⟶ V)) where
  toFun x i := x ≫ Pi.π (fun _ : Fin n => V) i
  invFun x := Pi.lift x
  left_inv x := by
    apply Pi.hom_ext
    intro i
    exact Pi.lift_comp_π _ i
  right_inv x := by
    funext i
    exact Pi.lift_comp_π x i

@[simp] theorem finitePowerPointsEquiv_apply (V : Over B) (n : ℕ) (T : Over B)
    (x : T ⟶ finitePower V n) (i : Fin n) :
    finitePowerPointsEquiv V n T x i = x ≫ Pi.π (fun _ : Fin n => V) i := rfl

@[simp] theorem finitePowerPointsEquiv_symm_π (V : Over B) (n : ℕ) (T : Over B)
    (x : Fin n → (T ⟶ V)) (i : Fin n) :
    (finitePowerPointsEquiv V n T).symm x ≫ Pi.π (fun _ : Fin n => V) i = x i :=
  Pi.lift_comp_π x i

theorem finitePowerPointsEquiv_naturality (V : Over B) (n : ℕ)
    {T T' : Over B} (a : T' ⟶ T) (x : T ⟶ finitePower V n) :
    finitePowerPointsEquiv V n T' (a ≫ x) =
      fun i => a ≫ finitePowerPointsEquiv V n T x i := by
  funext i
  exact Category.assoc a x (Pi.π (fun _ : Fin n => V) i)

/-- Ordered multiplication of the images of the `n` coordinates. The source
need not carry a group law. -/
def orderedPowerMap (f : V ⟶ G.X) (n : ℕ) : finitePower V n ⟶ G.X :=
  (List.ofFn fun i : Fin n => Pi.π (fun _ : Fin n => V) i ≫ f).prod

private def precompHom {T W : Over B} (a : T ⟶ W) :
    (W ⟶ G.X) →* (T ⟶ G.X) where
  toFun x := a ≫ x
  map_one' := MonObj.comp_one a
  map_mul' := MonObj.comp_mul a

/-- Evaluation on every test scheme, retaining the order of the factors. -/
theorem orderedPowerMap_points (f : V ⟶ G.X) (n : ℕ)
    {T : Over B} (x : T ⟶ finitePower V n) :
    x ≫ orderedPowerMap f n =
      (List.ofFn fun i : Fin n => (x ≫ Pi.π (fun _ : Fin n => V) i) ≫ f).prod := by
  simpa only [orderedPowerMap, List.map_ofFn, precompHom, MonoidHom.coe_mk,
    OneHom.coe_mk, Function.comp_def, Category.assoc] using
    (map_list_prod (precompHom x)
      (List.ofFn fun i : Fin n => Pi.π (fun _ : Fin n => V) i ≫ f))

/-- Ordered products commute with actual homomorphisms of the target groups. -/
theorem orderedPowerMap_comp (f : V ⟶ G.X) (j : G ⟶ K) (n : ℕ) :
    orderedPowerMap f n ≫ j.hom.hom = orderedPowerMap (f ≫ j.hom.hom) n := by
  simpa only [orderedPowerMap, List.map_ofFn, IsMonHom.monoidHom,
    MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_def, Category.assoc] using
    (map_list_prod (IsMonHom.monoidHom j.hom.hom (finitePower V n))
      (List.ofFn fun i : Fin n => Pi.π (fun _ : Fin n => V) i ≫ f))

@[simp] theorem orderedPowerMap_zero (f : V ⟶ G.X) : orderedPowerMap f 0 = 1 := by
  simp [orderedPowerMap]

namespace GeneratedImage

variable {f : V ⟶ G.X} (D : GeneratedImage f)

/-- The ordered product map into the actual generated representative. -/
def powerMap (n : ℕ) : finitePower V n ⟶ D.group.X := orderedPowerMap D.factor n

theorem powerMap_comp (n : ℕ) :
    D.powerMap n ≫ D.inclusion.hom.hom = orderedPowerMap f n := by
  rw [powerMap, orderedPowerMap_comp, D.factor_comp]

theorem powerMap_comp_points (n : ℕ) {T : Over B} (x : T ⟶ finitePower V n) :
    (x ≫ D.powerMap n) ≫ D.inclusion.hom.hom = x ≫ orderedPowerMap f n := by
  rw [Category.assoc, D.powerMap_comp]

theorem powerMap_points (n : ℕ) {T : Over B} (x : T ⟶ finitePower V n) :
    x ≫ D.powerMap n =
      (List.ofFn fun i : Fin n =>
        (x ≫ Pi.π (fun _ : Fin n => V) i) ≫ D.factor).prod :=
  orderedPowerMap_points D.factor n x

end GeneratedImage

end Langlands.GroupScheme
