import Langlands.Geometry.FormalGroup.NilpotentAlgebras
import Langlands.Geometry.FormalGroup.ModuleBaseChange

/-! # Actual kernels and scalar torsion on formal-module points -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom

variable {A B C : CommAlgCat.{w} R}

@[simp]
theorem onAlgebraPoints_id (x : M.AlgebraPoint A) :
    (id M).onAlgebraPoints x = x := by
  change (M.map (IsScalarTower.toAlgHom O R A)).Point Empty at x
  change ((id M).map (IsScalarTower.toAlgHom O R A)).onPoints x = x
  rw [map_id, onPoints_id]

@[simp]
theorem onAlgebraPoints_comp (g : Hom N P) (f : Hom M N) (x : M.AlgebraPoint A) :
    (g.comp f).onAlgebraPoints x = g.onAlgebraPoints (f.onAlgebraPoints x) := by
  change (M.map (IsScalarTower.toAlgHom O R A)).Point Empty at x
  change ((g.comp f).map (IsScalarTower.toAlgHom O R A)).onPoints x =
    (g.map (IsScalarTower.toAlgHom O R A)).onPoints
      ((f.map (IsScalarTower.toAlgHom O R A)).onPoints x)
  rw [map_comp, onPoints_comp]

@[simp]
theorem onAlgebraPoints_smul (a : O) (f : Hom M N) (x : M.AlgebraPoint A) :
    (a • f).onAlgebraPoints x = a • f.onAlgebraPoints x := by
  change (M.map (IsScalarTower.toAlgHom O R A)).Point Empty at x
  have h := (mapLinear (M := M) (N := N) (IsScalarTower.toAlgHom O R A)).map_smul a f
  change (a • f).map (IsScalarTower.toAlgHom O R A) =
    a • f.map (IsScalarTower.toAlgHom O R A) at h
  change ((a • f).map (IsScalarTower.toAlgHom O R A)).onPoints x =
    a • (f.map (IsScalarTower.toAlgHom O R A)).onPoints x
  rw [h, onPoints_smul]

/-- The actual O-submodule of points killed by a formal homomorphism. -/
def kernelPoints (f : Hom M N) (A : CommAlgCat.{w} R) :
    Submodule O (M.AlgebraPoint A) :=
  LinearMap.ker f.onAlgebraPoints

@[simp]
theorem mem_kernelPoints (f : Hom M N) (x : M.AlgebraPoint A) :
    x ∈ f.kernelPoints A ↔ f.onAlgebraPoints x = 0 := Iff.rfl

/-- Restriction of an algebra map to points of the actual kernel. -/
def kernelMap (f : Hom M N) (φ : A ⟶ B) :
    f.kernelPoints A →ₗ[O] f.kernelPoints B where
  toFun x := ⟨M.algebraMapPoints φ.hom x, by
    rw [mem_kernelPoints, ← onAlgebraPoints_natural f φ.hom, x.property, map_zero]⟩
  map_add' x y := Subtype.ext (map_add (M.algebraMapPoints φ.hom) x.val y.val)
  map_smul' a x := Subtype.ext (map_smul (M.algebraMapPoints φ.hom) a x.val)

@[simp]
theorem kernelMap_val (f : Hom M N) (φ : A ⟶ B) (x : f.kernelPoints A) :
    (f.kernelMap φ x).val = M.algebraMapPoints φ.hom x := rfl

/-- The kernel is a module-valued functor on all coefficient algebras. -/
def kernelPointFunctor (f : Hom M N) : CommAlgCat.{w} R ⥤ ModuleCat.{w} O where
  obj A := ModuleCat.of O (f.kernelPoints A)
  map φ := ModuleCat.ofHom (f.kernelMap φ)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change f.kernelPoints A at x
    apply Subtype.ext
    exact M.algebraMapPoints_id x.val
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change f.kernelPoints _ at x
    apply Subtype.ext
    exact M.algebraMapPoints_comp φ.hom ψ.hom x.val

/-- The kernel inclusion is the inclusion of the actual point submodules. -/
def kernelι (f : Hom M N) : f.kernelPointFunctor ⟶ M.algebraPointFunctor where
  app A := ModuleCat.ofHom (f.kernelPoints A).subtype
  naturality _ _ φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

@[simp]
theorem kernelι_comp (f : Hom M N) :
    f.kernelι ≫ f.algebraPointNatTrans = 0 := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact x.property

/-- A natural map annihilated by f factors through its actual kernel functor. -/
def kernelLift (f : Hom M N) {T : CommAlgCat.{w} R ⥤ ModuleCat.{w} O}
    (a : T ⟶ M.algebraPointFunctor) (h : a ≫ f.algebraPointNatTrans = 0) :
    T ⟶ f.kernelPointFunctor where
  app A := ModuleCat.ofHom {
    toFun x := ⟨(a.app A).hom x, by
      have hx := congrArg (fun t => (t.app A).hom x) h
      exact hx⟩
    map_add' x y := Subtype.ext ((a.app A).hom.map_add x y)
    map_smul' b x := Subtype.ext ((a.app A).hom.map_smul b x) }
  naturality A B φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun t => t.hom x) (a.naturality φ)

@[simp]
theorem kernelLift_ι (f : Hom M N) {T : CommAlgCat.{w} R ⥤ ModuleCat.{w} O}
    (a : T ⟶ M.algebraPointFunctor) (h : a ≫ f.algebraPointNatTrans = 0) :
    f.kernelLift a h ≫ f.kernelι = a := rfl

/-- Factorization through the kernel is unique. -/
theorem kernelLift_unique (f : Hom M N) {T : CommAlgCat.{w} R ⥤ ModuleCat.{w} O}
    (a : T ⟶ M.algebraPointFunctor) (h : a ≫ f.algebraPointNatTrans = 0)
    (b : T ⟶ f.kernelPointFunctor) (hb : b ≫ f.kernelι = a) :
    b = f.kernelLift a h := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun t => (t.app A).hom x) hb

/-- Kernels of composites map to the kernel of the second homomorphism. -/
def kernelCompMap (g : Hom N P) (f : Hom M N) :
    (g.comp f).kernelPointFunctor ⟶ g.kernelPointFunctor :=
  g.kernelLift ((g.comp f).kernelι ≫ f.algebraPointNatTrans) (by
    apply NatTrans.ext
    funext A
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (g.comp f).kernelPoints A at x
    exact (onAlgebraPoints_comp g f x.val).symm.trans x.property)

@[simp]
theorem kernelCompMap_val (g : Hom N P) (f : Hom M N)
    (x : (g.comp f).kernelPoints A) :
    ((kernelCompMap g f).app A x).val = f.onAlgebraPoints x.val := rfl

/-- Restrict the constructed kernel functor to Nilp. -/
def nilpKernelPointFunctor (f : Hom M N) (π : R) :
    Nilp.{v, w} R π ⥤ ModuleCat.{w} O :=
  Nilp.forget R π ⋙ f.kernelPointFunctor

end Hom

/-- The formal O-linear endomorphism given by a scalar in O. -/
def scalarHom (M : ModuleLaw O R σ) (a : O) : Hom M M := a • Hom.id M

@[simp]
theorem scalarHom_onAlgebraPoints (M : ModuleLaw O R σ) (a : O)
    (A : CommAlgCat.{w} R) (x : M.AlgebraPoint A) :
    (M.scalarHom a).onAlgebraPoints x = a • x := by
  simp only [scalarHom, Hom.onAlgebraPoints_smul, Hom.onAlgebraPoints_id]

/-- Scalar torsion is the actual kernel of scalar multiplication. -/
def torsionPointFunctor (M : ModuleLaw O R σ) (a : O) :
    CommAlgCat.{w} R ⥤ ModuleCat.{w} O :=
  (M.scalarHom a).kernelPointFunctor

@[simp]
theorem mem_scalarKernel (M : ModuleLaw O R σ) (a : O)
    (A : CommAlgCat.{w} R) (x : M.AlgebraPoint A) :
    x ∈ (M.scalarHom a).kernelPoints A ↔ a • x = 0 := by
  rw [Hom.mem_kernelPoints, scalarHom_onAlgebraPoints]

end Langlands.FormalGroup.ModuleLaw
