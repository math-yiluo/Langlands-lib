import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.AffinePoints

/-! # Translation and invariant coefficient averaging on diagonalizable groups -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable.Averaging

variable (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]

/-- Affine points of the diagonalizable group are unit-valued characters. -/
def pointsEquiv (A : Type u) [CommRing A] [Algebra R A] :
    Lie.AffinePoints (groupScheme R Λ).toGrp A ≃* (Multiplicative Λ →* Aˣ) :=
  Corepresented.affinePointsEquiv (functor R Λ) (grpCorepresentation R Λ) (CommAlgCat.of R A)

/-- The identity of the representing spectrum is the universal point. -/
def universalPoint : Lie.AffinePoints (groupScheme R Λ).toGrp (AddMonoidAlgebra R Λ) :=
  𝟙 (groupScheme R Λ).X

@[simp] theorem pointsEquiv_universalPoint :
    pointsEquiv R Λ _ (universalPoint R Λ) = monomialUnits R Λ := by
  have h := Corepresented.affinePointsEquiv_map (functor R Λ) (grpCorepresentation R Λ)
    (algebra R Λ) (𝟙 (algebra R Λ))
  rw [op_id, CategoryTheory.Functor.map_id] at h
  exact h

variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

theorem pointsEquiv_naturality (f : A →ₐ[R] B)
    (t : Lie.AffinePoints (groupScheme R Λ).toGrp A) :
    pointsEquiv R Λ B (Lie.affineMap _ f t) =
      (Units.map f.toMonoidHom).comp (pointsEquiv R Λ A t) :=
  Corepresented.affinePointsEquiv_naturality _ _ (CommAlgCat.ofHom f) t

/-- The coefficient inclusion into the group algebra. -/
abbrev const (A : Type u) [CommRing A] [Algebra R A] :
    A →ₐ[R] AddMonoidAlgebra A Λ :=
  IsScalarTower.toAlgHom R A (AddMonoidAlgebra A Λ)

/-- Scalar extension of the representing group algebra. -/
abbrev scalars (A : Type u) [CommRing A] [Algebra R A] :
    AddMonoidAlgebra R Λ →ₐ[R] AddMonoidAlgebra A Λ :=
  AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId R A)

/-- The universal point after extension of coefficients to `A`. -/
abbrev point (A : Type u) [CommRing A] [Algebra R A] :
    Lie.AffinePoints (groupScheme R Λ).toGrp (AddMonoidAlgebra A Λ) :=
  Lie.affineMap _ (scalars R Λ A) (universalPoint R Λ)

/-- Translation scales each monomial by its value under the given character. -/
def translation (r : Multiplicative Λ →* Aˣ) :
    AddMonoidAlgebra A Λ →ₐ[A] AddMonoidAlgebra A Λ :=
  AddMonoidAlgebra.lift A _ Λ
    ((AddMonoidAlgebra.of A Λ) *
      ((algebraMap A (AddMonoidAlgebra A Λ)).toMonoidHom.comp ((Units.coeHom A).comp r)))

@[simp] theorem translation_single (r : Multiplicative Λ →* Aˣ) (m : Λ) (a : A) :
    translation Λ r (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single m (a * (r (.ofAdd m) : A)) := by
  simp [translation, Algebra.smul_def, AddMonoidAlgebra.of_apply,
    AddMonoidAlgebra.single_mul_single]

/-- Translation scales coefficients individually, including for torsion characters. -/
theorem coeff_translation (r : Multiplicative Λ →* Aˣ) (x : AddMonoidAlgebra A Λ) (m : Λ) :
    (translation Λ r x).coeff m = x.coeff m * (r (.ofAdd m) : A) := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul]
  | single n a =>
      rw [translation_single]
      by_cases h : n = m
      · subst m; simp
      · simp [Ne.symm h]

/-- The degree-zero coefficient is translation invariant in every characteristic. -/
theorem coeff_zero_translation (r : Multiplicative Λ →* Aˣ) (x : AddMonoidAlgebra A Λ) :
    (translation Λ r x).coeff 0 = x.coeff 0 := by
  rw [coeff_translation, ofAdd_zero, map_one, Units.val_one, mul_one]

/-- Translation fixes the coefficient ring. -/
theorem translation_comp_const (r : Multiplicative Λ →* Aˣ) :
    ((translation Λ r).restrictScalars R).comp (const R Λ A) = const R Λ A :=
  AlgHom.ext fun a => (translation Λ r).commutes a

/-- Translating the universal point is multiplication by the given constant point. -/
theorem translation_point (r : Lie.AffinePoints (groupScheme R Λ).toGrp A) :
    Lie.affineMap _ ((translation Λ (pointsEquiv R Λ A r)).restrictScalars R) (point R Λ A) =
      Lie.affineMap _ (const R Λ A) r * point R Λ A := by
  apply (pointsEquiv R Λ _).injective
  rw [pointsEquiv_naturality, pointsEquiv_naturality, pointsEquiv_universalPoint, map_mul,
    pointsEquiv_naturality, pointsEquiv_naturality, pointsEquiv_universalPoint]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change translation Λ (pointsEquiv R Λ A r)
      (AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId R A) (AddMonoidAlgebra.single m.toAdd 1)) =
    AddMonoidAlgebra.single 0 (pointsEquiv R Λ A r m : A) *
      AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId R A) (AddMonoidAlgebra.single m.toAdd 1)
  simp

/-- Constant points are fixed under translation of the averaging variable. -/
theorem translation_const (r : Multiplicative Λ →* Aˣ) {G : GroupScheme (Spec R)}
    (x : Lie.AffinePoints G A) :
    Lie.affineMap _ ((translation Λ r).restrictScalars R)
      (Lie.affineMap _ (const R Λ A) x) = Lie.affineMap _ (const R Λ A) x := by
  rw [← Lie.affineMap_comp, translation_comp_const]

end Langlands.GroupScheme.Diagonalizable.Averaging
