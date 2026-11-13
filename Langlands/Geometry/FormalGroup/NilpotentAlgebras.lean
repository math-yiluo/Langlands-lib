import Langlands.Geometry.FormalGroup.ModuleMorphism
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Nilpotent coefficient algebras and formal module point functors -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup

open CategoryTheory

variable (R : Type u) [CommRing R] (π : R)

/-- The image of the distinguished element is nilpotent. -/
def nilpotentAlgebraProperty : ObjectProperty (CommAlgCat.{v} R) :=
  fun A => IsNilpotent (algebraMap R A π)

/-- The full category of coefficient algebras in which π is nilpotent. -/
abbrev Nilp := (nilpotentAlgebraProperty.{u, v} R π).FullSubcategory

namespace Nilp

/-- Construct an object from an algebra and its actual nilpotence condition. -/
def of (A : Type v) [CommRing A] [Algebra R A]
    (h : IsNilpotent (algebraMap R A π)) : Nilp R π :=
  ⟨CommAlgCat.of R A, h⟩

/-- Forget the nilpotence condition. All algebra homomorphisms are retained. -/
def forget : Nilp.{u, v} R π ⥤ CommAlgCat.{v} R :=
  (nilpotentAlgebraProperty R π).ι

variable {R π}

theorem nilpotent (A : Nilp.{u, v} R π) :
    IsNilpotent (algebraMap R A.obj π) := A.property

end Nilp

namespace ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable (M : ModuleLaw O R σ)
variable {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra O A] [Algebra R A] [IsScalarTower O R A]
variable [Algebra O B] [Algebra R B] [IsScalarTower O R B]
variable [Algebra O C] [Algebra R C] [IsScalarTower O R C]

/-- Algebra homomorphisms act O-linearly on the actual nilpotent points. -/
def algebraMapPoints (f : A →ₐ[R] B) :
    M.AlgebraPoint A →ₗ[O] M.AlgebraPoint B where
  toFun := SeriesPoint.map f.toRingHom
  map_add' := (M.groupLaw.algebraMapPoints f).map_add
  map_smul' a x := by
    change SeriesPoint A σ Empty at x
    change (SeriesPoint.eval ((M.action a).toCoordinateMap.map (algebraMap R A)) x).map
      f.toRingHom = SeriesPoint.eval
        ((M.action a).toCoordinateMap.map (algebraMap R B)) (x.map f.toRingHom)
    rw [SeriesPoint.map_eval, CoordinateMap.map_ringHom_comp]
    have h : f.toRingHom.comp (algebraMap R A) = algebraMap R B :=
      RingHom.ext f.commutes
    rw [h]

@[simp]
theorem algebraMapPoints_id (x : M.AlgebraPoint A) :
    M.algebraMapPoints (AlgHom.id R A) x = x := by
  change SeriesPoint A σ Empty at x
  exact SeriesPoint.map_id x

@[simp]
theorem algebraMapPoints_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (x : M.AlgebraPoint A) :
    M.algebraMapPoints (g.comp f) x = M.algebraMapPoints g (M.algebraMapPoints f x) := by
  change SeriesPoint A σ Empty at x
  exact (SeriesPoint.map_comp f.toRingHom g.toRingHom x).symm

/-- Evaluate an O-linear formal map over an extending coefficient algebra. -/
def Hom.onAlgebraPoints {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
    (f : Hom M N) : M.AlgebraPoint A →ₗ[O] N.AlgebraPoint A :=
  (f.map (IsScalarTower.toAlgHom O R A)).onPoints

theorem Hom.onAlgebraPoints_natural {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
    (f : Hom M N) (φ : A →ₐ[R] B) (x : M.AlgebraPoint A) :
    N.algebraMapPoints φ (f.onAlgebraPoints x) =
      f.onAlgebraPoints (M.algebraMapPoints φ x) := by
  change SeriesPoint A σ Empty at x
  change (SeriesPoint.eval (f.toHom.toCoordinateMap.map (algebraMap R A)) x).map
    φ.toRingHom = SeriesPoint.eval (f.toHom.toCoordinateMap.map (algebraMap R B))
      (x.map φ.toRingHom)
  rw [SeriesPoint.map_eval, CoordinateMap.map_ringHom_comp]
  have h : φ.toRingHom.comp (algebraMap R A) = algebraMap R B :=
    RingHom.ext φ.commutes
  rw [h]

section Functors

/-- The structural O-algebra on a coefficient R-algebra, used only in this section. -/
abbrev coefficientAlgebra (A : CommAlgCat.{w} R) : Algebra O A :=
  Algebra.compHom A (algebraMap O R)

attribute [local instance] coefficientAlgebra

/-- The scalar tower for the structural composite O → R → A. -/
theorem coefficientScalarTower (A : CommAlgCat.{w} R) : IsScalarTower O R A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] coefficientScalarTower

/-- The formal O-module as a module-valued functor on coefficient algebras. -/
def algebraPointFunctor : CommAlgCat.{w} R ⥤ ModuleCat.{w} O where
  obj A := ModuleCat.of O (M.AlgebraPoint A)
  map f := ModuleCat.ofHom (M.algebraMapPoints f.hom)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact M.algebraMapPoints_id x
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact M.algebraMapPoints_comp f.hom g.hom x

/-- Restrict the actual point functor to algebras in which π is nilpotent. -/
def nilpPointFunctor (π : R) : Nilp.{v, w} R π ⥤ ModuleCat.{w} O :=
  Nilp.forget R π ⋙ M.algebraPointFunctor

/-- A formal O-linear homomorphism induces a natural transformation of point functors. -/
def Hom.algebraPointNatTrans {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
    (f : Hom M N) : M.algebraPointFunctor ⟶ N.algebraPointFunctor where
  app A := ModuleCat.ofHom f.onAlgebraPoints
  naturality _ _ φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.onAlgebraPoints_natural φ.hom x).symm

end Functors

end ModuleLaw

end Langlands.FormalGroup
