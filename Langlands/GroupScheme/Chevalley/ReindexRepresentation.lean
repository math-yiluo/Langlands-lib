import Langlands.GroupScheme.MatrixRepresentation
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Reindexing actual matrix representations and their coordinate lines -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix Classical

namespace Langlands.GroupScheme.Chevalley

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (e : I ≃ J)

/-- Change the finite coordinate index of an invertible matrix. -/
def reindexGL {A : Type*} [CommRing A] : GL I A →* GL J A :=
  (Units.mapEquiv (Matrix.reindexRingEquiv A e).toMulEquiv).toMonoidHom

@[simp] theorem reindexGL_apply {A : Type*} [CommRing A] (g : GL I A) (i j : J) :
    reindexGL e g i j = g (e.symm i) (e.symm j) := rfl

/-- A coordinate line has the same unit-scalar stabilizer after reindexing. -/
theorem reindexGL_basisLine_iff {A : Type*} [CommRing A] (g : GL I A) (t : I) :
    (∃ u : Aˣ, (reindexGL e g : Matrix J J A) *ᵥ Pi.single (e t) 1 =
      (u : A) • (Pi.single (e t) (1 : A) : J → A)) ↔
    (∃ u : Aˣ, (g : Matrix I I A) *ᵥ Pi.single t 1 =
      (u : A) • (Pi.single t (1 : A) : I → A)) := by
  apply exists_congr
  intro u
  constructor
  · intro h
    funext i
    have hi := congrFun h (e i)
    simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
      reindexGL_apply, Equiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    by_cases hit : i = t
    · subst i
      simpa using hi
    · simpa [hit, e.injective.ne hit] using hi
  · intro h
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    have hi := congrFun h i
    simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
      reindexGL_apply, Equiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    by_cases hit : i = t
    · subst i
      simpa using hi
    · simpa [hit, e.injective.ne hit] using hi

variable (R : CommRingCat.{u})

/-- Reindexing is natural in the coefficient algebra. -/
def reindexNat : GeneralLinear.functor I R ⟶ GeneralLinear.functor J R where
  app A := GrpCat.ofHom (reindexGL e)
  naturality A A' f := by
    ext g : 2
    apply Units.ext
    ext i j
    rfl

/-- The actual group-scheme homomorphism changing a finite coordinate index. -/
def reindexGroupHom : GeneralLinear.groupScheme I R ⟶ GeneralLinear.groupScheme J R :=
  Corepresented.groupSchemeMap (GeneralLinear.corepresentableBy I R)
    (GeneralLinear.corepresentableBy J R) (reindexNat e R)

/-- Reindex an actual matrix representation. -/
def reindexRepresentation {G : GroupScheme (Spec R)} (ρ : MatrixRepresentation G I) :
    MatrixRepresentation G J :=
  ρ ≫ reindexGroupHom e R

theorem reindexRepresentation_pointMatrix {G : GroupScheme (Spec R)}
    (ρ : MatrixRepresentation G I) (T : Over (Spec R)) (x : T ⟶ G.X) :
    (reindexRepresentation e R ρ).pointMatrix T x = reindexGL e (ρ.pointMatrix T x) :=
  Corepresented.groupSchemeMap_points (GeneralLinear.corepresentableBy I R)
    (GeneralLinear.corepresentableBy J R) (reindexNat e R) (x ≫ ρ.hom.hom)

end Langlands.GroupScheme.Chevalley
