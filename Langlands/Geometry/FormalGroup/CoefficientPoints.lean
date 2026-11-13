import Langlands.Geometry.FormalGroup.KernelTransport

/-! # Restriction of coefficient algebras and actual point comparisons -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- An S-algebra viewed as an R-algebra along the actual coefficient map. -/
def restrictCoefficientAlgebra (φ : R →ₐ[O] S) (A : CommAlgCat.{v} S) :
    CommAlgCat.{v} R :=
  letI : Algebra R A := Algebra.compHom A φ.toRingHom
  CommAlgCat.of R A

/-- Restriction retains the underlying map and checks its R-linearity. -/
def restrictCoefficientMap (φ : R →ₐ[O] S) {A B : CommAlgCat.{v} S} (ψ : A ⟶ B) :
    restrictCoefficientAlgebra φ A ⟶ restrictCoefficientAlgebra φ B :=
  { hom' := {
    __ := ψ.hom.toRingHom
    commutes' r := ψ.hom.commutes (φ r) } }

/-- Restriction of coefficient algebras along an O-algebra map. -/
def restrictCoefficientFunctor (φ : R →ₐ[O] S) : CommAlgCat.{v} S ⥤ CommAlgCat.{v} R where
  obj := restrictCoefficientAlgebra φ
  map := restrictCoefficientMap φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A base-changed law and the original law have the same actual points on
an extending coefficient algebra, with their actual O-module structures. -/
def coefficientPointEquiv (M : ModuleLaw O R σ) (φ : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) :
    (M.map φ).AlgebraPoint A ≃ₗ[O] M.AlgebraPoint (restrictCoefficientAlgebra φ A) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    change SeriesPoint.eval ((M.groupLaw.addition.map φ.toRingHom).map
      (algebraMap S A)) (x.pair y) = SeriesPoint.eval
      (M.groupLaw.addition.map ((algebraMap S A).comp φ.toRingHom)) (x.pair y)
    rw [CoordinateMap.map_ringHom_comp]
  map_smul' a x := by
    change SeriesPoint.eval (((M.action a).toCoordinateMap.map φ.toRingHom).map
      (algebraMap S A)) x = SeriesPoint.eval
      ((M.action a).toCoordinateMap.map ((algebraMap S A).comp φ.toRingHom)) x
    rw [CoordinateMap.map_ringHom_comp]

/-- Actual formal-map evaluation respects the coefficient point comparison. -/
theorem Hom.coefficientPointEquiv_natural (f : Hom M N) (φ : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) (x : (M.map φ).AlgebraPoint A) :
    N.coefficientPointEquiv φ A ((f.map φ).onAlgebraPoints x) =
      f.onAlgebraPoints (M.coefficientPointEquiv φ A x) := by
  change SeriesPoint.eval ((f.toHom.toCoordinateMap.map φ.toRingHom).map
    (algebraMap S A)) x = SeriesPoint.eval
    (f.toHom.toCoordinateMap.map ((algebraMap S A).comp φ.toRingHom)) x
  rw [CoordinateMap.map_ringHom_comp]

/-- The point comparison commutes with every S-algebra map. -/
theorem coefficientPointEquiv_algebraMap (M : ModuleLaw O R σ) (φ : R →ₐ[O] S)
    {A B : CommAlgCat.{v} S} (ψ : A ⟶ B) (x : (M.map φ).AlgebraPoint A) :
    M.coefficientPointEquiv φ B ((M.map φ).algebraMapPoints ψ.hom x) =
      M.algebraMapPoints (restrictCoefficientMap φ ψ).hom
        (M.coefficientPointEquiv φ A x) := rfl

/-- The actual point kernel after base change is the original kernel on the
restricted test algebra. -/
def Hom.coefficientKernelEquiv (f : Hom M N) (φ : R →ₐ[O] S)
    (A : CommAlgCat.{v} S) :
    (f.map φ).kernelPoints A ≃ₗ[O]
      f.kernelPoints (restrictCoefficientAlgebra φ A) where
  toFun x := ⟨M.coefficientPointEquiv φ A x.val, by
    rw [Hom.mem_kernelPoints, ← f.coefficientPointEquiv_natural, x.property, map_zero]⟩
  invFun x := ⟨(M.coefficientPointEquiv φ A).symm x.val, by
    rw [Hom.mem_kernelPoints]
    apply (N.coefficientPointEquiv φ A).injective
    rw [f.coefficientPointEquiv_natural, LinearEquiv.apply_symm_apply, x.property,
      map_zero]⟩
  left_inv x := Subtype.ext ((M.coefficientPointEquiv φ A).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((M.coefficientPointEquiv φ A).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((M.coefficientPointEquiv φ A).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((M.coefficientPointEquiv φ A).map_smul a x.val)

/-- The kernel comparison is natural in all extending coefficient algebras. -/
def Hom.coefficientKernelIso (f : Hom M N) (φ : R →ₐ[O] S) :
    (f.map φ).kernelSetFunctor ≅ restrictCoefficientFunctor φ ⋙ f.kernelSetFunctor :=
  NatIso.ofComponents
    (fun A => (f.coefficientKernelEquiv φ A).toEquiv.toIso)
    (fun _ => by
      apply ConcreteCategory.hom_ext
      intro x
      rfl)

end Langlands.FormalGroup.ModuleLaw
