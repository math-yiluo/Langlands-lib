import Langlands.GroupScheme.Dynamic.UnipotentGrading
import Langlands.GroupScheme.Reductive.GradedPrimitiveCoordinate

/-! # Primitive homogeneous coordinates on dynamic unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented.UnipotentPrimitive

open AffineLine

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {A : CommAlgCat.{u} R}

/-- The affine test-scheme point associated to an algebra point. -/
def affinePoint (y : F.obj A) : RingCoordinates.specOver R A ⟶ (groupScheme F e).X :=
  (affinePointsEquiv F e A).symm y

theorem algHom_affinePoint (y : F.obj A) :
    RingCoordinates.algHom (affinePoint e y) = coord e y := by
  obtain ⟨φ, rfl⟩ := e.homEquiv.surjective y
  have h : affinePoint e (e.homEquiv φ) = (algSpec R).map φ.op :=
    (affinePointsEquiv F e A).symm_apply_eq.2 (affinePointsEquiv_map F e A φ).symm
  change RingCoordinates.algHom (affinePoint e (e.homEquiv φ)) =
    (e.homEquiv.symm (e.homEquiv φ)).hom
  rw [h, Equiv.symm_apply_apply]
  ext b
  exact pointRing_algSpecMap φ b

theorem pointRing_affinePoint (y : F.obj A) (b : B) :
    pointRing (affinePoint e y) b = coord e y b :=
  congrArg (fun φ : B →ₐ[R] A => φ b) (algHom_affinePoint e y)

theorem affinePoint_mul (y y' : F.obj A) :
    affinePoint e (y * y') = affinePoint e y * affinePoint e y' :=
  (affinePointsEquiv F e A).symm.map_mul y y'

theorem affinePoint_one : affinePoint e (1 : F.obj A) = 1 :=
  (affinePointsEquiv F e A).symm.map_one

variable {e} (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- The algebra-valued points of the dynamic unipotent group. -/
abbrev unipotentFunctor : CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  cutFunctor (isCutOutBy_affineSubgroups (isAffineCutOutBy_unipotent χ))

/-- The actual quotient algebra corepresents the dynamic unipotent group. -/
abbrev unipotentCorepresentation :
    (unipotentFunctor χ ⋙ forget GrpCat).CorepresentableBy
      (quotientAlgebra (unipotentIdeal χ)) :=
  cutCorepresentableBy (isCutOutBy_affineSubgroups (isAffineCutOutBy_unipotent χ))

theorem coord_val (y : (unipotentFunctor χ).obj A) (b : B) :
    coord e y.val b = coord (unipotentCorepresentation χ) y (unipQuot χ b) := rfl

/-- The quotient coaction followed by evaluation of its coefficients at a point. -/
def orbitAlgHom (y : (unipotentFunctor χ).obj A) :
    quotientAlgebra (unipotentIdeal χ) →ₐ[R] LaurentPolynomial A where
  __ := (AddMonoidAlgebra.mapRingHom ℤ
    (coord (unipotentCorepresentation χ) y).toRingHom).comp (unipCoaction χ)
  commutes' r := by
    change AddMonoidAlgebra.mapRingHom ℤ
      (coord (unipotentCorepresentation χ) y).toRingHom
      (unipCoaction χ (algebraMap R _ r)) = _
    rw [(isGrading_unipCoaction χ).map_algebraMap,
      ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single]
    change AddMonoidAlgebra.single 0
      (coord (unipotentCorepresentation χ) y (algebraMap R _ r)) = _
    rw [AlgHom.commutes]
    rfl

/-- The Laurent orbit point, constructed from the actual quotient coaction. -/
def orbitFun (y : (unipotentFunctor χ).obj A) :
    (unipotentFunctor χ).obj (CommAlgCat.of R (LaurentPolynomial A)) :=
  ofCoord (unipotentCorepresentation χ) (orbitAlgHom χ y)

theorem coord_orbitFun (y : (unipotentFunctor χ).obj A)
    (b : quotientAlgebra (unipotentIdeal χ)) :
    coord (unipotentCorepresentation χ) (orbitFun χ y) b =
      AddMonoidAlgebra.mapRingHom ℤ (coord (unipotentCorepresentation χ) y).toRingHom
        (unipCoaction χ b) := by
  rw [orbitFun, coord_ofCoord]
  rfl

/-- The constant inclusion of a test algebra into its Laurent polynomial algebra. -/
def constHom : A →ₐ[R] LaurentPolynomial A :=
  (Algebra.ofId A (LaurentPolynomial A)).restrictScalars R

theorem affinePoint_orbitFun (y : (unipotentFunctor χ).obj A) :
    affinePoint e (orbitFun χ y).val =
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial A))))
          (unitT A) ≫ χ.hom.hom) *
        (RingCoordinates.specMapOver (constHom (R := R) (A := A)) ≫ affinePoint e y.val) *
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial A))))
          (unitT A) ≫ χ.hom.hom)⁻¹ := by
  have hconst :
      pointRing (RingCoordinates.specMapOver (constHom (R := R) (A := A)) ≫
        affinePoint e y.val) =
      CommRingCat.ofHom (LaurentPolynomial.C.comp (coord e y.val).toRingHom) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change RingCoordinates.algHom
      (RingCoordinates.specMapOver (constHom (R := R) (A := A)) ≫ affinePoint e y.val) b = _
    rw [RingCoordinates.algHom_comp, algHom_affinePoint]
    rfl
  apply hom_ext_of_pointRing
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  rw [pointRing_conj, hconst, pointRing_affinePoint, coord_val, coord_orbitFun,
    unipCoaction_mk]
  change AddMonoidAlgebra.mapRingHom ℤ (coord (unipotentCorepresentation χ) y).toRingHom
      (AddMonoidAlgebra.mapRingHom ℤ (unipQuot χ) ((coaction χ).hom b)) =
    LaurentPolynomial.eval₂ (RingHom.id _) (unitT A)
      (AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C.comp (coord e y.val).toRingHom)
        ((coaction χ).hom b))
  rw [eval₂_T_mapRingHom]
  ext n
  rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_mapRingHom,
    AddMonoidAlgebra.coeff_mapRingHom]
  rfl

set_option maxHeartbeats 800000 in
/-- The quotient-coaction orbit map is multiplicative, as follows from actual conjugation. -/
def orbitHom : (unipotentFunctor χ).obj A →*
    (unipotentFunctor χ).obj (CommAlgCat.of R (LaurentPolynomial A)) where
  toFun := orbitFun χ
  map_one' := by
    apply Subtype.ext
    apply (affinePointsEquiv F e (CommAlgCat.of R (LaurentPolynomial A))).symm.injective
    change affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e
      (orbitFun (A := A) χ (1 : (unipotentFunctor χ).obj A)).val =
      affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e (1 : F.obj _)
    rw [affinePoint_orbitFun]
    change _ * (RingCoordinates.specMapOver _ ≫ affinePoint (A := A) e (1 : F.obj A)) * _ =
      affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e (1 : F.obj _)
    simp only [affinePoint_one, MonObj.comp_one, mul_one, mul_inv_cancel]
  map_mul' y y' := by
    apply Subtype.ext
    apply (affinePointsEquiv F e (CommAlgCat.of R (LaurentPolynomial A))).symm.injective
    change affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e
      (orbitFun (A := A) χ (y * y')).val =
      affinePoint (A := CommAlgCat.of R (LaurentPolynomial A)) e
        ((orbitFun (A := A) χ y).val * (orbitFun (A := A) χ y').val)
    rw [affinePoint_mul, affinePoint_orbitFun, affinePoint_orbitFun, affinePoint_orbitFun]
    change _ * (RingCoordinates.specMapOver _ ≫ affinePoint e (y.val * y'.val)) * _ = _
    rw [affinePoint_mul, MonObj.comp_mul]
    group

set_option maxHeartbeats 800000 in
/-- A homogeneous generator of the actual dynamic unipotent coordinate algebra
has additive values on every algebra point. -/
theorem coord_mul {d : ℕ} (hd : 0 < d) {x : quotientAlgebra (unipotentIdeal χ)}
    (hx : x ∈ CommutativeAlgebra.GradedLine.homog (isGrading_unipCoaction χ) d)
    (hgen : Function.Surjective (Polynomial.aeval x :
      R[X] →ₐ[R] quotientAlgebra (unipotentIdeal χ)))
    (y y' : (unipotentFunctor χ).obj A) :
    coord (unipotentCorepresentation χ) (y * y') x =
      coord (unipotentCorepresentation χ) y x + coord (unipotentCorepresentation χ) y' x :=
  GradedPrimitive.coord_mul_of_homogeneous_generator (unipotentCorepresentation χ)
    (isGrading_unipCoaction χ) hd hx hgen (orbitHom (A := A) χ)
    (coord_orbitFun (A := A) χ) y y'

/-- The homogeneous generator is additive on points of every test scheme. -/
theorem appTop_mul {d : ℕ} (hd : 0 < d) {x : quotientAlgebra (unipotentIdeal χ)}
    (hx : x ∈ CommutativeAlgebra.GradedLine.homog (isGrading_unipCoaction χ) d)
    (hgen : Function.Surjective (Polynomial.aeval x :
      R[X] →ₐ[R] quotientAlgebra (unipotentIdeal χ)))
    {T : Over (Spec R)} (y y' : T ⟶ (unipotentScheme χ).X) :
    (y * y').left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (quotientAlgebra (unipotentIdeal χ)))).inv x) =
      y.left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (quotientAlgebra (unipotentIdeal χ)))).inv x) +
        y'.left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (quotientAlgebra (unipotentIdeal χ)))).inv x) := by
  have h := coord_mul χ hd hx hgen
    (pointsEquiv (unipotentFunctor χ) (unipotentCorepresentation χ) T y)
    (pointsEquiv (unipotentFunctor χ) (unipotentCorepresentation χ) T y')
  rw [← map_mul] at h
  change ((unipotentCorepresentation χ).homEquiv.symm
      (pointsEquiv (unipotentFunctor χ) (unipotentCorepresentation χ) T (y * y'))).hom x =
    ((unipotentCorepresentation χ).homEquiv.symm
      (pointsEquiv (unipotentFunctor χ) (unipotentCorepresentation χ) T y)).hom x +
    ((unipotentCorepresentation χ).homEquiv.symm
      (pointsEquiv (unipotentFunctor χ) (unipotentCorepresentation χ) T y')).hom x at h
  rw [homEquiv_symm_pointsEquiv_apply (e := unipotentCorepresentation χ) T (y * y') x,
    homEquiv_symm_pointsEquiv_apply (e := unipotentCorepresentation χ) T y x,
    homEquiv_symm_pointsEquiv_apply (e := unipotentCorepresentation χ) T y' x] at h
  exact h

end Langlands.GroupScheme.Corepresented.UnipotentPrimitive
