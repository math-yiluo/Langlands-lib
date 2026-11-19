import Langlands.Geometry.FormalGroup.ScalarTorsionTower

/-! # Compatible families of actual scalar torsion points -/

noncomputable section
universe u v w

namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable {M : ModuleLaw O R σ} {A B : CommAlgCat.{v} R}

/-- The linear map underlying the actual affine torsion transition. -/
abbrev torsionTransitionLinear (M : ModuleLaw O R σ) (π : O)
    {m n : ℕ} (h : m ≤ n) (A : CommAlgCat.{v} R) :
    (M.scalarHom (π ^ n)).kernelPoints A →ₗ[O] (M.scalarHom (π ^ m)).kernelPoints A :=
  ((M.torsionTransition π h).app A).hom

/-- The module of compatible families in the actual scalar-power point kernels on `A`. -/
def scalarTatePoints (M : ModuleLaw O R σ) (π : O) (A : CommAlgCat.{v} R) :
    Submodule O (∀ n : ℕ, (M.scalarHom (π ^ n)).kernelPoints A) where
  carrier := {x | ∀ m n : ℕ, ∀ h : m ≤ n, M.torsionTransitionLinear π h A (x n) = x m}
  zero_mem' := fun m n h => map_zero (M.torsionTransitionLinear π h A)
  add_mem' := by
    intro x y hx hy m n h
    change M.torsionTransitionLinear π h A (x n + y n) = x m + y m
    rw [map_add, hx m n h, hy m n h]
  smul_mem' := by
    intro a x hx m n h
    change M.torsionTransitionLinear π h A (a • x n) = a • x m
    rw [map_smul, hx m n h]

namespace scalarTatePoints

variable {π : O}

/-- The projection to the actual scalar-power kernel at one index. -/
def eval (n : ℕ) : M.scalarTatePoints π A →ₗ[O] (M.scalarHom (π ^ n)).kernelPoints A :=
  (LinearMap.proj n).comp (M.scalarTatePoints π A).subtype

@[simp]
theorem eval_apply (x : M.scalarTatePoints π A) (n : ℕ) : eval n x = x.val n := rfl

@[simp]
theorem transition_eval (x : M.scalarTatePoints π A) {m n : ℕ} (h : m ≤ n) :
    M.torsionTransitionLinear π h A (eval n x) = eval m x :=
  x.property m n h

@[ext]
theorem ext {x y : M.scalarTatePoints π A} (h : ∀ n : ℕ, eval n x = eval n y) : x = y :=
  Subtype.ext (funext h)

variable {V : Type w} [AddCommGroup V] [Module O V]

/-- The universal map of a compatible family into the actual inverse limit. -/
def lift (f : ∀ n : ℕ, V →ₗ[O] (M.scalarHom (π ^ n)).kernelPoints A)
    (h : ∀ m n : ℕ, ∀ hmn : m ≤ n, ∀ x : V,
      M.torsionTransitionLinear π hmn A (f n x) = f m x) :
    V →ₗ[O] M.scalarTatePoints π A where
  toFun x := ⟨fun n => f n x, fun m n hmn => h m n hmn x⟩
  map_add' x y := ext fun n => map_add (f n) x y
  map_smul' a x := ext fun n => map_smul (f n) a x

@[simp]
theorem eval_lift (f : ∀ n : ℕ, V →ₗ[O] (M.scalarHom (π ^ n)).kernelPoints A)
    (h : ∀ m n : ℕ, ∀ hmn : m ≤ n, ∀ x : V,
      M.torsionTransitionLinear π hmn A (f n x) = f m x) (x : V) (n : ℕ) :
    eval n (lift f h x) = f n x := rfl

/-- All projections determine a linear map into the inverse limit. -/
theorem linearMap_ext {f g : V →ₗ[O] M.scalarTatePoints π A}
    (h : ∀ n : ℕ, (eval n).comp f = (eval n).comp g) : f = g := by
  apply LinearMap.ext
  intro x
  exact ext (fun n => LinearMap.congr_fun (h n) x)

/-- Actual coefficient test maps act term by term on compatible families. -/
def mapAlgebra (φ : A ⟶ B) : M.scalarTatePoints π A →ₗ[O] M.scalarTatePoints π B :=
  lift (fun n => ((M.scalarHom (π ^ n)).kernelMap φ).comp (eval n)) (by
    intro m n h x
    have hnat := ConcreteCategory.congr_hom ((M.torsionTransition π h).naturality φ) (eval n x)
    change M.torsionTransitionLinear π h B ((M.scalarHom (π ^ n)).kernelMap φ (eval n x)) =
      (M.scalarHom (π ^ m)).kernelMap φ (M.torsionTransitionLinear π h A (eval n x)) at hnat
    rw [transition_eval] at hnat
    exact hnat)

@[simp]
theorem eval_mapAlgebra (φ : A ⟶ B) (x : M.scalarTatePoints π A) (n : ℕ) :
    eval n (mapAlgebra φ x) = (M.scalarHom (π ^ n)).kernelMap φ (eval n x) := rfl

end scalarTatePoints

open scalarTatePoints in
/-- The modules of compatible scalar torsion points are functorial in the test algebra. -/
def scalarTatePointFunctor (M : ModuleLaw O R σ) (π : O) :
    CommAlgCat.{v} R ⥤ ModuleCat.{v} O where
  obj A := ModuleCat.of O (M.scalarTatePoints π A)
  map φ := ModuleCat.ofHom (mapAlgebra φ)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply scalarTatePoints.ext
    intro n
    apply Subtype.ext
    exact M.algebraMapPoints_id (eval n x).val
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply scalarTatePoints.ext
    intro n
    apply Subtype.ext
    exact M.algebraMapPoints_comp φ.hom ψ.hom (eval n x).val

namespace Hom
open scalarTatePoints

variable {τ υ : Type} [Finite τ] [Finite υ]
variable {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable (π : O)

/-- An integral formal module map acts on the actual torsion kernels. -/
def scalarTorsionPointsMap (f : Hom M N) (n : ℕ) (A : CommAlgCat.{v} R) :
    (M.scalarHom (π ^ n)).kernelPoints A →ₗ[O] (N.scalarHom (π ^ n)).kernelPoints A where
  toFun x := ⟨f.onAlgebraPoints x.val, by
    apply (N.mem_scalarKernel (π ^ n) A _).mpr
    rw [← map_smul, (M.mem_scalarKernel (π ^ n) A x.val).mp x.property, map_zero]⟩
  map_add' x y := Subtype.ext (map_add f.onAlgebraPoints x.val y.val)
  map_smul' a x := Subtype.ext (map_smul f.onAlgebraPoints a x.val)

/-- The same formal homomorphism acts term by term on the inverse limit. -/
def scalarTatePointMap (f : Hom M N) (A : CommAlgCat.{v} R) :
    M.scalarTatePoints π A →ₗ[O] N.scalarTatePoints π A :=
  lift (fun n => (f.scalarTorsionPointsMap π n A).comp (eval n)) (by
    intro m n h x
    apply Subtype.ext
    have hval := congrArg Subtype.val (transition_eval x h)
    change ((M.torsionTransition π h).app A (eval n x)).val = (eval m x).val at hval
    change ((N.torsionTransition π h).app A
        (f.scalarTorsionPointsMap π n A (eval n x))).val =
      f.onAlgebraPoints (eval m x).val
    erw [torsionTransition_app_val, ← hval, torsionTransition_app_val]
    exact (map_smul f.onAlgebraPoints _ _).symm)

@[simp]
theorem eval_scalarTatePointMap (f : Hom M N) (x : M.scalarTatePoints π A) (n : ℕ) :
    eval n (f.scalarTatePointMap π A x) = f.scalarTorsionPointsMap π n A (eval n x) := rfl

/-- Integral maps of formal modules give natural maps between the affine inverse limits. -/
def scalarTatePointNatTrans (f : Hom M N) :
    M.scalarTatePointFunctor π ⟶ N.scalarTatePointFunctor π where
  app A := ModuleCat.ofHom (f.scalarTatePointMap π A)
  naturality A B φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply scalarTatePoints.ext
    intro n
    apply Subtype.ext
    exact (f.onAlgebraPoints_natural φ.hom (eval n x).val).symm

@[simp]
theorem scalarTatePointMap_id :
    (Hom.id M).scalarTatePointMap π A = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply scalarTatePoints.ext
  intro n
  apply Subtype.ext
  exact Hom.onAlgebraPoints_id (eval n x).val

theorem scalarTatePointMap_comp (g : Hom N P) (f : Hom M N) :
    (g.comp f).scalarTatePointMap π A =
      (g.scalarTatePointMap π A).comp (f.scalarTatePointMap π A) := by
  apply LinearMap.ext
  intro x
  apply scalarTatePoints.ext
  intro n
  apply Subtype.ext
  exact Hom.onAlgebraPoints_comp g f (eval n x).val

/-- The point-limit construction acts linearly on formal homomorphisms. -/
def scalarTatePointLinear (A : CommAlgCat.{v} R) :
    Hom M N →ₗ[O] (M.scalarTatePoints π A →ₗ[O] N.scalarTatePoints π A) where
  toFun f := f.scalarTatePointMap π A
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply scalarTatePoints.ext
    intro n
    apply Subtype.ext
    let φ := IsScalarTower.toAlgHom O R A
    change ((f + g).map φ).onPoints (eval n x).val =
      (f.map φ).onPoints (eval n x).val + (g.map φ).onPoints (eval n x).val
    have h : (f + g).map φ = f.map φ + g.map φ := (Hom.mapLinear φ).map_add f g
    rw [h]
    exact Hom.onPoints_add (f.map φ) (g.map φ) (eval n x).val
  map_smul' a f := by
    apply LinearMap.ext
    intro x
    apply scalarTatePoints.ext
    intro n
    apply Subtype.ext
    exact Hom.onAlgebraPoints_smul a f (eval n x).val

end Hom

end Langlands.FormalGroup.ModuleLaw
