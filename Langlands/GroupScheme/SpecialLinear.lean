import Langlands.GroupScheme.GeneralLinear
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # The special linear group scheme from determinant-one coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

section Algebra

variable (n : Type) [Fintype n] [DecidableEq n] (R : Type u) [CommRing R]

/-- The matrix of independent polynomial entry variables. -/
def genericMatrix : Matrix n n (MvPolynomial (n × n) R) :=
  Matrix.of fun i j => X (i, j)

/-- The ideal imposing determinant one. -/
def ideal : Ideal (MvPolynomial (n × n) R) :=
  Ideal.span {Matrix.det (genericMatrix n R) - 1}

/-- The determinant-one coordinate ring, with no inverse variables. -/
abbrev CoordinateRing : Type u := MvPolynomial (n × n) R ⧸ ideal n R

/-- The quotient map to determinant-one coordinates. -/
abbrev quotient : MvPolynomial (n × n) R →ₐ[R] CoordinateRing n R :=
  Ideal.Quotient.mkₐ R (ideal n R)

variable {n R}

/-- An entry specialization kills the defining ideal exactly when its determinant is one. -/
theorem ideal_le_ker {S : Type u} [CommRing S] [Algebra R S]
    (f : MvPolynomial (n × n) R →ₐ[R] S)
    (h : Matrix.det (f.mapMatrix (genericMatrix n R)) = 1) :
    ideal n R ≤ RingHom.ker f := by
  rw [ideal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one,
    AlgHom.map_det, h, sub_self]

variable (n R)

/-- The matrix of quotient entry coordinates has determinant one. -/
theorem quotient_det : Matrix.det ((quotient n R).mapMatrix (genericMatrix n R)) = 1 := by
  have h : quotient n R (Matrix.det (genericMatrix n R) - 1) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  rwa [map_sub, map_one, AlgHom.map_det, sub_eq_zero] at h

/-- The universal determinant-one matrix. -/
def universal : Matrix.SpecialLinearGroup n (CoordinateRing n R) :=
  ⟨(quotient n R).mapMatrix (genericMatrix n R), quotient_det n R⟩

@[simp] theorem universal_apply (i j : n) :
    universal n R i j = quotient n R (X (i, j)) := rfl

variable {n R} {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Specialization of the universal determinant-one matrix along an algebra map. -/
def point (f : CoordinateRing n R →ₐ[R] S) : Matrix.SpecialLinearGroup n S :=
  Matrix.SpecialLinearGroup.map f.toRingHom (universal n R)

@[simp] theorem point_apply (f : CoordinateRing n R →ₐ[R] S) (i j : n) :
    point f i j = f (quotient n R (X (i, j))) := rfl

/-- Specialization is natural in the target algebra. -/
theorem point_comp (f : CoordinateRing n R →ₐ[R] S) (g : S →ₐ[R] T) :
    point (g.comp f) = Matrix.SpecialLinearGroup.map g.toRingHom (point f) := rfl

@[simp] theorem point_id : point (AlgHom.id R (CoordinateRing n R)) = universal n R := rfl

/-- The values of the entry variables at a determinant-one matrix. -/
def values (g : Matrix.SpecialLinearGroup n S) : n × n → S :=
  fun ij => g ij.1 ij.2

theorem aeval_mapMatrix_genericMatrix (g : Matrix.SpecialLinearGroup n S) :
    (aeval (R := R) (values g)).mapMatrix (genericMatrix n R) =
      (g : Matrix n n S) := by
  ext i j
  simp [genericMatrix, values]

/-- The algebra map classifying a determinant-one matrix. -/
def classify (g : Matrix.SpecialLinearGroup n S) : CoordinateRing n R →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval (values g)) fun _ ha =>
    RingHom.mem_ker.mp <| ideal_le_ker _
      (by rw [aeval_mapMatrix_genericMatrix]; exact g.property) ha

theorem classify_comp_quotient (g : Matrix.SpecialLinearGroup n S) :
    (classify (R := R) g).comp (quotient n R) = aeval (values g) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem classify_quotient (g : Matrix.SpecialLinearGroup n S)
    (f : MvPolynomial (n × n) R) :
    classify g (quotient n R f) = aeval (values g) f :=
  AlgHom.congr_fun (classify_comp_quotient g) f

@[simp] theorem classify_entry (g : Matrix.SpecialLinearGroup n S) (i j : n) :
    classify (R := R) g (quotient n R (X (i, j))) = g i j := by
  rw [classify_quotient, aeval_X]
  rfl

/-- Algebra maps out of the coordinate ring are exactly determinant-one matrices. -/
def homEquiv : (CoordinateRing n R →ₐ[R] S) ≃ Matrix.SpecialLinearGroup n S where
  toFun := point
  invFun := classify
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, classify_entry]
    rfl
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact classify_entry g i j

@[simp] theorem classify_point (f : CoordinateRing n R →ₐ[R] S) : classify (point f) = f :=
  homEquiv.left_inv f

@[simp] theorem point_classify (g : Matrix.SpecialLinearGroup n S) :
    point (classify (R := R) g) = g := homEquiv.right_inv g

/-- Classifying a coefficient-changed matrix is composing its classifying map. -/
theorem classify_map (g : Matrix.SpecialLinearGroup n S) (f : S →ₐ[R] T) :
    classify (Matrix.SpecialLinearGroup.map f.toRingHom g) = f.comp (classify (R := R) g) := by
  apply homEquiv.injective
  change point _ = point _
  rw [point_comp, point_classify, point_classify]

@[simp] theorem classify_universal :
    classify (universal n R) = AlgHom.id R (CoordinateRing n R) := by
  rw [← point_id, classify_point]

end Algebra

section Scheme

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

/-- The functor of determinant-one matrices, with entrywise coefficient change. -/
def functor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj S := GrpCat.of (Matrix.SpecialLinearGroup n S)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id S := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl

@[simp] theorem functor_obj (S : CommAlgCat.{u} R) :
    (functor n R).obj S = GrpCat.of (Matrix.SpecialLinearGroup n S) := rfl

theorem functor_map_apply {S T : CommAlgCat.{u} R} (f : S ⟶ T)
    (g : Matrix.SpecialLinearGroup n S) :
    (functor n R).map f g = Matrix.SpecialLinearGroup.map f.hom.toRingHom g := rfl

/-- The determinant-one coordinate ring as a base algebra. -/
abbrev coordinateAlgebra : CommAlgCat.{u} R := CommAlgCat.of R (CoordinateRing n R)

/-- The explicit determinant-one coordinate ring corepresents the special linear functor. -/
def corepresentableBy :
    (functor n R ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra n R) where
  homEquiv :=
    { toFun := fun f => point f.hom
      invFun := fun g => CommAlgCat.ofHom (classify g)
      left_inv := fun f => CommAlgCat.hom_ext (classify_point f.hom)
      right_inv := fun g => point_classify g }
  homEquiv_comp g f := point_comp f.hom g.hom

/-- The actual affine special linear group scheme over `Spec R`. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (functor n R) (corepresentableBy n R)

@[simp] theorem groupScheme_X :
    (groupScheme n R).X = (algSpec R).obj (op (coordinateAlgebra n R)) := rfl

theorem groupScheme_left :
    (groupScheme n R).X.left = Spec (CommRingCat.of (CoordinateRing n R)) := rfl

theorem groupScheme_hom :
    (groupScheme n R).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing n R))) := rfl

instance isAffine_groupScheme : IsAffine (groupScheme n R).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (CoordinateRing n R))))

instance isAffineHom_groupScheme : IsAffineHom (groupScheme n R).X.hom :=
  isAffineHom_of_isAffine _

/-- The global function giving an entry of the universal determinant-one matrix. -/
def entrySection (i j : n) : Γ((groupScheme n R).X.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).inv (quotient n R (X (i, j)))

/-- Scheme points over every relative test scheme are determinant-one matrices over its
actual global sections. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme n R).X) ≃* Matrix.SpecialLinearGroup n Γ(T.left, ⊤) :=
  Corepresented.pointsEquiv (functor n R) (corepresentableBy n R) T

variable {n R}

/-- The point comparison uses the algebra map from the relative spectrum adjunction. -/
theorem pointsEquiv_apply (T : Over (Spec R)) (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv n R T x =
      point (((algΓAlgSpecAdjunction R).homEquiv T (op (coordinateAlgebra n R))).symm x).unop.hom :=
  rfl

/-- The adjoint algebra map pulls back global functions along the scheme point. -/
theorem adjunction_homEquiv_symm_apply (T : Over (Spec R)) (x : T ⟶ (groupScheme n R).X)
    (b : CoordinateRing n R) :
    (((algΓAlgSpecAdjunction R).homEquiv T (op (coordinateAlgebra n R))).symm x).unop.hom b =
      x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).inv b) := by
  change T ⟶ (algSpec R).obj (op (coordinateAlgebra n R)) at x
  rw [Adjunction.homEquiv_counit]
  rfl

/-- Entries of a scheme point are the pullbacks of the corresponding global entry functions. -/
theorem pointsEquiv_apply_apply (T : Over (Spec R)) (x : T ⟶ (groupScheme n R).X) (i j : n) :
    pointsEquiv n R T x i j = x.left.appTop (entrySection n R i j) :=
  adjunction_homEquiv_symm_apply T x _

/-- Restriction of scheme points applies the pullback on global sections entrywise. -/
theorem pointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme n R).X) :
    pointsEquiv n R T' (a ≫ x) =
      Matrix.SpecialLinearGroup.map a.left.appTop.hom (pointsEquiv n R T x) :=
  Corepresented.pointsEquiv_naturality _ _ a x

/-- A special-linear scheme point is determined by its matrix entries. -/
theorem points_ext {T : Over (Spec R)} {x y : T ⟶ (groupScheme n R).X}
    (h : ∀ i j, pointsEquiv n R T x i j = pointsEquiv n R T y i j) : x = y :=
  (pointsEquiv n R T).injective (Matrix.SpecialLinearGroup.ext _ _ h)

variable (n R) in
/-- On affine tests the point comparison takes values directly in the test algebra. -/
def affinePointsEquiv (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶ (groupScheme n R).X) ≃* Matrix.SpecialLinearGroup n S :=
  Corepresented.affinePointsEquiv (functor n R) (corepresentableBy n R) S

@[simp] theorem affinePointsEquiv_map (S : CommAlgCat.{u} R) (f : coordinateAlgebra n R ⟶ S) :
    affinePointsEquiv n R S ((algSpec R).map f.op) = point f.hom :=
  Corepresented.affinePointsEquiv_map _ _ S f

/-- The affine point with prescribed determinant-one matrix is the spectrum of its classifier. -/
theorem affinePointsEquiv_symm_apply (S : CommAlgCat.{u} R)
    (g : Matrix.SpecialLinearGroup n S) :
    (affinePointsEquiv n R S).symm g = (algSpec R).map (CommAlgCat.ofHom (classify g)).op := by
  apply (affinePointsEquiv n R S).injective
  rw [MulEquiv.apply_symm_apply, affinePointsEquiv_map]
  exact (point_classify g).symm

/-- Inclusion of determinant-one matrices into invertible matrices is a natural map. -/
def toGeneralLinear : functor n R ⟶ GeneralLinear.functor n R where
  app S := GrpCat.ofHom Matrix.SpecialLinearGroup.toGL
  naturality S T f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Units.ext
    rfl

variable (n R) in
/-- The actual homomorphism from the special linear group scheme into the general linear one. -/
def inclusion : groupScheme n R ⟶ GeneralLinear.groupScheme n R :=
  Corepresented.groupSchemeMap (corepresentableBy n R) (GeneralLinear.corepresentableBy n R)
    toGeneralLinear

/-- The inclusion on every test scheme is the usual determinant-one matrix inclusion. -/
theorem pointsEquiv_inclusion (T : Over (Spec R)) (x : T ⟶ (groupScheme n R).X) :
    GeneralLinear.pointsEquiv n R T (x ≫ (inclusion n R).hom.hom) =
      Matrix.SpecialLinearGroup.toGL (pointsEquiv n R T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

end Scheme

end Langlands.GroupScheme.SpecialLinear
