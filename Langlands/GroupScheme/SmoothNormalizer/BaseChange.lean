import Langlands.GroupScheme.SmoothNormalizer.OpenSubgroup
import Langlands.GroupScheme.CorepresentedNormalizer

/-! # Base change of a corepresented subgroup functor to an algebra

For an `R`-algebra `A`, restriction of scalars sends `A`-algebras to `R`-algebras. A group functor
on `R`-algebras corepresented by `D`, evaluated on `A`-algebras, is corepresented over `A` by
`A ⊗[R] D`.
-/

universe u

open CategoryTheory TensorProduct Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.SmoothNormalizer

variable {R : CommRingCat.{u}}

section Restrict

variable (A : CommAlgCat.{u} R)

/-- The `R`-algebra structure on an `A`-algebra, through `A`. -/
abbrev resAlgebra (X : Type u) [CommRing X] [Algebra A X] : Algebra R X :=
  ((algebraMap A X).comp (algebraMap R A)).toAlgebra

/-- Restriction of scalars from `A`-algebras to `R`-algebras. -/
def res : CommAlgCat.{u} (CommRingCat.of A) ⥤ CommAlgCat.{u} R where
  obj X := letI := resAlgebra A X; CommAlgCat.of R X
  map {X Y} f := letI := resAlgebra A X; letI := resAlgebra A Y; CommAlgCat.ofHom
    { f.hom.toRingHom with commutes' := fun r => f.hom.commutes (algebraMap R A r) }

@[simp] theorem res_map_hom_apply {X Y : CommAlgCat.{u} (CommRingCat.of A)} (f : X ⟶ Y) (x : X) :
    ((res A).map f).hom x = f.hom x := rfl

/-- The structure map `A → X` of an `A`-algebra, as a map of `R`-algebras. -/
def toRes (X : CommAlgCat.{u} (CommRingCat.of A)) : A ⟶ (res A).obj X :=
  letI := resAlgebra A X
  CommAlgCat.ofHom { algebraMap A X with commutes' := fun _ => rfl }

@[simp] theorem toRes_hom_apply (X : CommAlgCat.{u} (CommRingCat.of A)) (a : A) :
    (toRes A X).hom a = algebraMap A X a := rfl

theorem toRes_comp_res_map {X Y : CommAlgCat.{u} (CommRingCat.of A)} (f : X ⟶ Y) :
    toRes A X ≫ (res A).map f = toRes A Y := by
  apply CommAlgCat.hom_ext
  ext a
  exact f.hom.commutes a

end Restrict

section Corep

variable (A : CommAlgCat.{u} R) {G : CommAlgCat.{u} R ⥤ GrpCat.{u}} {D : CommAlgCat.{u} R}
  (eG : (G ⋙ forget GrpCat).CorepresentableBy D)

/-- The base change `A ⊗[R] D`, as an `A`-algebra. -/
abbrev baseChangeAlg (D : CommAlgCat.{u} R) : CommAlgCat.{u} (CommRingCat.of A) :=
  CommAlgCat.of (CommRingCat.of A) (A ⊗[R] D)

/-- Restriction of an `A`-algebra map out of `A ⊗[R] D` to `D`, as a map of `R`-algebras. -/
def restrictRight {X : CommAlgCat.{u} (CommRingCat.of A)} (φ : baseChangeAlg A D ⟶ X) :
    D ⟶ (res A).obj X :=
  letI := resAlgebra A X
  CommAlgCat.ofHom
    { φ.hom.toRingHom.comp (Algebra.TensorProduct.includeRight : D →ₐ[R] A ⊗[R] D).toRingHom with
      commutes' := fun r => by
        change φ.hom ((1 : A) ⊗ₜ[R] algebraMap R D r) = algebraMap A X (algebraMap R A r)
        rw [← φ.hom.commutes (algebraMap R A r)]
        congr 1
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_one_eq_one_tmul] }

@[simp] theorem restrictRight_hom_apply {X : CommAlgCat.{u} (CommRingCat.of A)}
    (φ : baseChangeAlg A D ⟶ X) (d : D) :
    (restrictRight A φ).hom d = φ.hom ((1 : A) ⊗ₜ[R] d) := rfl

/-- The `A`-algebra map out of `A ⊗[R] D` extending an `R`-algebra map out of `D`. -/
def extendRight {X : CommAlgCat.{u} (CommRingCat.of A)} (ψ : D ⟶ (res A).obj X) :
    baseChangeAlg A D ⟶ X :=
  CommAlgCat.ofHom
    { (Algebra.TensorProduct.lift (toRes A X).hom ψ.hom fun _ _ => .all _ _).toRingHom with
      commutes' := fun a => by
        change (Algebra.TensorProduct.lift (toRes A X).hom ψ.hom fun _ _ => .all _ _)
          (a ⊗ₜ[R] (1 : D)) = algebraMap A X a
        rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        rfl }

theorem extendRight_hom_tmul {X : CommAlgCat.{u} (CommRingCat.of A)}
    (ψ : D ⟶ (res A).obj X) (a : A) (d : D) :
    (extendRight A ψ).hom (a ⊗ₜ[R] d) = (toRes A X).hom a * ψ.hom d := rfl

theorem restrictRight_extendRight {X : CommAlgCat.{u} (CommRingCat.of A)}
    (ψ : D ⟶ (res A).obj X) : restrictRight A (extendRight A ψ) = ψ := by
  apply CommAlgCat.hom_ext
  ext d
  rw [restrictRight_hom_apply, extendRight_hom_tmul, map_one, one_mul]

theorem extendRight_restrictRight {X : CommAlgCat.{u} (CommRingCat.of A)}
    (φ : baseChangeAlg A D ⟶ X) : extendRight A (restrictRight A φ) = φ := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  induction (x : A ⊗[R] D) using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a d =>
    change algebraMap (CommRingCat.of A) X a * φ.hom ((1 : A) ⊗ₜ[R] d) = φ.hom (a ⊗ₜ[R] d)
    rw [← φ.hom.commutes a, ← map_mul]
    congr 1
    change (a ⊗ₜ[R] (1 : D)) * ((1 : A) ⊗ₜ[R] d) = a ⊗ₜ[R] d
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem restrictRight_comp {X Y : CommAlgCat.{u} (CommRingCat.of A)}
    (φ : baseChangeAlg A D ⟶ X) (f : X ⟶ Y) :
    restrictRight A (φ ≫ f) = restrictRight A φ ≫ (res A).map f := rfl

/-- **Corepresentation of the base change.** The points over `A`-algebras of a functor
corepresented by `D` are corepresented over `A` by `A ⊗[R] D`. -/
def baseChangeCorep : ((res A ⋙ G) ⋙ forget GrpCat).CorepresentableBy (baseChangeAlg A D) where
  homEquiv {X} :=
    { toFun := fun φ => eG.homEquiv (restrictRight A φ)
      invFun := fun x => extendRight A (eG.homEquiv.symm x)
      left_inv := fun φ => by
        simp only [Equiv.symm_apply_apply, extendRight_restrictRight]
      right_inv := fun x => by
        simp only [restrictRight_extendRight, Equiv.apply_symm_apply] }
  homEquiv_comp {X Y} f φ := by
    change eG.homEquiv (restrictRight A (φ ≫ f)) = G.map ((res A).map f)
      (eG.homEquiv (restrictRight A φ))
    rw [restrictRight_comp]
    exact eG.homEquiv_comp _ _

theorem baseChangeCorep_symm (X : CommAlgCat.{u} (CommRingCat.of A))
    (x : G.obj ((res A).obj X)) :
    (baseChangeCorep A eG).homEquiv.symm x = extendRight A (eG.homEquiv.symm x) := rfl

theorem restrictRight_baseChangeCorep_symm (X : CommAlgCat.{u} (CommRingCat.of A))
    (x : G.obj ((res A).obj X)) :
    restrictRight A ((baseChangeCorep A eG).homEquiv.symm x) = eG.homEquiv.symm x := by
  rw [baseChangeCorep_symm, restrictRight_extendRight]

end Corep

end Langlands.GroupScheme.SmoothNormalizer
