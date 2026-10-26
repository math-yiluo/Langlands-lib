import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Polynomial-Proj projective space over a commutative ring -/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

/-- The homogeneous coordinate ring of finite projective `n`-space over `R`. -/
abbrev ProjectiveCoordinateRing (R : Type u) [CommRing R] (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) R

/-- The standard total-degree grading, with every coordinate variable of degree one. -/
def projectiveSpaceGrading (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → Submodule R (ProjectiveCoordinateRing R n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

instance projectiveSpaceGradedAlgebra (R : Type u) [CommRing R] (n : ℕ) :
    GradedAlgebra (projectiveSpaceGrading R n) :=
  MvPolynomial.gradedAlgebra

/-- Constants, regarded as elements of the degree-zero ring of the coordinate ring. -/
def projectiveSpaceConstants (R : Type u) [CommRing R] (n : ℕ) :
    R →+* projectiveSpaceGrading R n 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
  map_one' := by apply Subtype.ext; exact map_one MvPolynomial.C
  map_mul' r s := by apply Subtype.ext; exact map_mul MvPolynomial.C r s
  map_zero' := by apply Subtype.ext; exact map_zero MvPolynomial.C
  map_add' r s := by apply Subtype.ext; exact map_add MvPolynomial.C r s

@[simp]
lemma projectiveSpaceConstants_coe (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    (projectiveSpaceConstants R n r : ProjectiveCoordinateRing R n) = MvPolynomial.C r :=
  rfl

/-- Projective `n`-space over `R`, constructed as the Proj of its graded polynomial ring. -/
def ProjectiveSpace (R : Type u) [CommRing R] (n : ℕ) : Scheme.{u} :=
  Proj (projectiveSpaceGrading R n)

/-- The structural morphism of projective space, induced by the constant coefficients. -/
def projectiveSpaceToSpec (R : Type u) [CommRing R] (n : ℕ) :
    ProjectiveSpace R n ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projectiveSpaceGrading R n) ≫
    Spec.map (CommRingCat.ofHom (projectiveSpaceConstants R n))

/-- The standard coordinate open `D₊(Xᵢ)` as an actual open of projective space. -/
def projectiveSpaceCoordinateOpen (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveSpace R n).Opens :=
  Proj.basicOpen (projectiveSpaceGrading R n) (MvPolynomial.X i)

lemma projectiveSpace_X_mem (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ projectiveSpaceGrading R n 1 :=
  MvPolynomial.isHomogeneous_X R i

@[simp]
lemma mem_projectiveSpaceCoordinateOpen (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) (x : ProjectiveSpace R n) :
    x ∈ projectiveSpaceCoordinateOpen R n i ↔ MvPolynomial.X i ∉ x.asHomogeneousIdeal :=
  Iff.rfl

/-- H-projectivity over an affine ring base: a closed immersion into some finite projective
space, commuting with the specified structure morphism. This is the finite-projective-space
convention of Stacks Definition 29.44.1(2). -/
def IsHProjective {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace R n),
    IsClosedImmersion i ∧ i ≫ projectiveSpaceToSpec R n = p

end Langlands.AlgebraicGeometry
