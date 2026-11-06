import Langlands.GroupScheme.Reductive.HomogeneousPolynomialRepresentation

/-! # Coefficient-change naturality of homogeneous polynomial representations -/

noncomputable section

universe u v w z

namespace Langlands.GroupScheme.HomogeneousPolynomial

open MvPolynomial Matrix

variable {n : Type u} [Fintype n]
  {R : Type v} [CommSemiring R] {S : Type w} [CommSemiring S]
  {T : Type z} [CommSemiring T]

/-- Changing coefficients preserves the matrix-column linear forms. -/
theorem map_variableImage (f : R →+* S) (A : Matrix n n R) (i : n) :
    MvPolynomial.map f (variableImage A i) = variableImage (A.map f) i := by
  simp [variableImage]

/-- Matrix substitution commutes with every homomorphism of coefficient semirings. -/
theorem map_substitution (f : R →+* S) (A : Matrix n n R) (p : MvPolynomial n R) :
    MvPolynomial.map f (substitution A p) =
      substitution (A.map f) (MvPolynomial.map f p) := by
  change MvPolynomial.map f (eval₂ C (variableImage A) p) =
    eval₂ C (variableImage (A.map f)) (MvPolynomial.map f p)
  rw [MvPolynomial.map_eval₂]
  have h : MvPolynomial.map f ∘ variableImage A = variableImage (A.map f) :=
    funext (map_variableImage f A)
  rw [h]

/-- The actual semilinear map on homogeneous submodules induced by coefficient change. -/
def coefficientMap (m : ℕ) (f : R →+* S) :
    homogeneousSubmodule n R m →ₛₗ[f] homogeneousSubmodule n S m where
  toFun p := ⟨MvPolynomial.map f p, p.property.map f⟩
  map_add' p q := Subtype.ext
    (map_add (MvPolynomial.map f) (p : MvPolynomial n R) (q : MvPolynomial n R))
  map_smul' r p := by
    apply Subtype.ext
    change MvPolynomial.map f (r • (p : MvPolynomial n R)) =
      f r • MvPolynomial.map f (p : MvPolynomial n R)
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

omit [Fintype n] in
@[simp]
theorem coefficientMap_coe (m : ℕ) (f : R →+* S)
    (p : homogeneousSubmodule n R m) :
    (coefficientMap m f p : MvPolynomial n S) = MvPolynomial.map f p :=
  rfl

omit [Fintype n] in
@[simp]
theorem coefficientMap_id (m : ℕ) (p : homogeneousSubmodule n R m) :
    coefficientMap m (RingHom.id R) p = p := by
  apply Subtype.ext
  exact MvPolynomial.map_id (p : MvPolynomial n R)

omit [Fintype n] in
theorem coefficientMap_comp (m : ℕ) (f : R →+* S) (g : S →+* T)
    (p : homogeneousSubmodule n R m) :
    coefficientMap m g (coefficientMap m f p) = coefficientMap m (g.comp f) p := by
  apply Subtype.ext
  exact MvPolynomial.map_map _ _ _

/-- Coefficient change intertwines the actual homogeneous matrix operators. -/
theorem coefficientMap_homogeneousMap (m : ℕ) (f : R →+* S) (A : Matrix n n R)
    (p : homogeneousSubmodule n R m) :
    coefficientMap m f (homogeneousMap m A p) =
      homogeneousMap m (A.map f) (coefficientMap m f p) := by
  apply Subtype.ext
  exact map_substitution f A p

section SpecialLinear

variable {R' : Type v} [CommRing R'] {S' : Type w} [CommRing S']
  [DecidableEq n]

/-- Coefficient change also intertwines the actual special-linear-group actions. -/
theorem coefficientMap_specialLinearRepresentation (m : ℕ) (f : R' →+* S')
    (g : Matrix.SpecialLinearGroup n R') (p : homogeneousSubmodule n R' m) :
    coefficientMap m f (specialLinearRepresentation m g p) =
      specialLinearRepresentation m (Matrix.SpecialLinearGroup.map f g)
        (coefficientMap m f p) := by
  apply Subtype.ext
  exact map_substitution f (g : Matrix n n R') p

end SpecialLinear

end Langlands.GroupScheme.HomogeneousPolynomial
