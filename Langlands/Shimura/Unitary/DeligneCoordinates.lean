import Langlands.Shimura.Unitary.Deligne
import Mathlib.RingTheory.FinitePresentation
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace Langlands.Shimura.DeligneTorus

open MvPolynomial CategoryTheory
open scoped QuadraticAlgebra

/-- Coordinates of a quadratic element and its inverse. -/
inductive Variable
  | re | im | invRe | invIm
  deriving DecidableEq

def Variable.code : Variable → Bool × Bool
  | .re => (false, false)
  | .im => (false, true)
  | .invRe => (true, false)
  | .invIm => (true, true)

instance : Finite Variable := Finite.of_injective Variable.code (by
  intro v w h
  cases v <;> cases w <;> simp_all [Variable.code])

/-- Polynomial coordinates before imposing invertibility. -/
abbrev PolynomialRing := MvPolynomial Variable ℝ

/-- The real part of the product is one. -/
def realRelation : PolynomialRing :=
  X Variable.re * X Variable.invRe - X Variable.im * X Variable.invIm - 1

/-- The imaginary part of the product vanishes. -/
def imagRelation : PolynomialRing :=
  X Variable.re * X Variable.invIm + X Variable.im * X Variable.invRe

/-- The two inverse equations in quadratic coordinates. -/
def coordinateIdeal : Ideal PolynomialRing := Ideal.span {realRelation, imagRelation}

theorem coordinateIdeal_fg : coordinateIdeal.FG := by
  exact ⟨{realRelation, imagRelation}, by simp [coordinateIdeal]⟩

/-- A finite presentation for the coordinate algebra of the Deligne torus. -/
abbrev CoordinateRing := PolynomialRing ⧸ coordinateIdeal

instance : Algebra.FinitePresentation ℝ CoordinateRing :=
  Algebra.FinitePresentation.quotient coordinateIdeal_fg

/-- The polynomial quotient map. -/
abbrev quotient : PolynomialRing →ₐ[ℝ] CoordinateRing := Ideal.Quotient.mkₐ ℝ coordinateIdeal

/-- Images of the four coordinate functions in the quotient. -/
def coord (v : Variable) : CoordinateRing := quotient (X v)

theorem coord_real_relation :
    coord .re * coord .invRe - coord .im * coord .invIm = 1 := by
  have h : quotient realRelation = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa [realRelation, coord, sub_eq_zero] using h

theorem coord_imag_relation :
    coord .re * coord .invIm + coord .im * coord .invRe = 0 := by
  have h : quotient imagRelation = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa [imagRelation, coord] using h

/-- The actual universal quadratic unit over the coordinate algebra. -/
def universalPoint : Points CoordinateRing where
  val := ⟨coord .re, coord .im⟩
  inv := ⟨coord .invRe, coord .invIm⟩
  val_inv := by
    ext
    · change coord .re * coord .invRe + (-1 : CoordinateRing) * coord .im * coord .invIm = 1
      calc
        _ = coord .re * coord .invRe - coord .im * coord .invIm := by ring
        _ = 1 := coord_real_relation
    · simpa [QuadraticAlgebra.im_mul, add_comm, mul_comm] using coord_imag_relation
  inv_val := by
    rw [mul_comm]
    ext
    · change coord .re * coord .invRe + (-1 : CoordinateRing) * coord .im * coord .invIm = 1
      calc
        _ = coord .re * coord .invRe - coord .im * coord .invIm := by ring
        _ = 1 := coord_real_relation
    · simpa [QuadraticAlgebra.im_mul, add_comm, mul_comm] using coord_imag_relation

variable {S : Type u} {T : Type v} [CommRing S] [Algebra ℝ S]
  [CommRing T] [Algebra ℝ T]

/-- Specialize the universal quadratic unit along an algebra map. -/
def point (f : CoordinateRing →ₐ[ℝ] S) : Points S :=
  Units.map (map f.toRingHom).toMonoidHom universalPoint

@[simp] theorem point_re (f : CoordinateRing →ₐ[ℝ] S) :
    (point f : Complexification S).re = f (coord .re) := rfl

@[simp] theorem point_im (f : CoordinateRing →ₐ[ℝ] S) :
    (point f : Complexification S).im = f (coord .im) := rfl

@[simp] theorem point_inv_re (f : CoordinateRing →ₐ[ℝ] S) :
    (((point f)⁻¹ : Points S) : Complexification S).re = f (coord .invRe) := rfl

@[simp] theorem point_inv_im (f : CoordinateRing →ₐ[ℝ] S) :
    (((point f)⁻¹ : Points S) : Complexification S).im = f (coord .invIm) := rfl

/-- Coordinates assigned to the generators by a quadratic unit. -/
def values (z : Points S) : Variable → S
  | .re => (z : Complexification S).re
  | .im => (z : Complexification S).im
  | .invRe => ((z⁻¹ : Points S) : Complexification S).re
  | .invIm => ((z⁻¹ : Points S) : Complexification S).im

theorem eval_realRelation (z : Points S) : aeval (values z) realRelation = 0 := by
  have h := congrArg QuadraticAlgebra.re z.val_inv
  change (z : Complexification S).re * ((z⁻¹ : Points S) : Complexification S).re +
    (-1 : S) * (z : Complexification S).im * ((z⁻¹ : Points S) : Complexification S).im = 1 at h
  simpa [realRelation, values, sub_eq_add_neg, neg_mul] using (sub_eq_zero.mpr h)

theorem eval_imagRelation (z : Points S) : aeval (values z) imagRelation = 0 := by
  have h := congrArg QuadraticAlgebra.im z.val_inv
  change (z : Complexification S).re * ((z⁻¹ : Points S) : Complexification S).im +
    (z : Complexification S).im * ((z⁻¹ : Points S) : Complexification S).re +
    (0 : S) * (z : Complexification S).im * ((z⁻¹ : Points S) : Complexification S).im = 0 at h
  simpa only [imagRelation, map_add, _root_.map_mul, aeval_X, values, zero_mul, add_zero] using h

/-- Every actual quadratic unit satisfies both defining equations. -/
theorem coordinateIdeal_le_ker (z : Points S) :
    coordinateIdeal ≤ RingHom.ker (aeval (values z)) := by
  refine Ideal.span_le.mpr ?_
  intro p hp
  rcases hp with rfl | hp
  · exact RingHom.mem_ker.mpr (eval_realRelation z)
  · have hp' : p = imagRelation := Set.mem_singleton_iff.mp hp
    subst p
    exact RingHom.mem_ker.mpr (eval_imagRelation z)

/-- The algebra homomorphism classifying a quadratic unit. -/
def classify (z : Points S) : CoordinateRing →ₐ[ℝ] S :=
  Ideal.Quotient.liftₐ _ (aeval (values z)) fun _ hp =>
    RingHom.mem_ker.mp (coordinateIdeal_le_ker z hp)

@[simp] theorem classify_quotient (z : Points S) (p : PolynomialRing) :
    classify z (quotient p) = aeval (values z) p := rfl

@[simp] theorem classify_coord (z : Points S) (v : Variable) :
    classify z (coord v) = values z v := by
  change classify z (quotient (X v)) = _
  rw [classify_quotient, aeval_X]

/-- The coordinate algebra classifies exactly the actual quadratic units. -/
def homEquiv : (CoordinateRing →ₐ[ℝ] S) ≃ Points S where
  toFun := point
  invFun := classify
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro v
    change classify (point f) (coord v) = f (coord v)
    rw [classify_coord]
    cases v <;> rfl
  right_inv z := by
    apply Units.ext
    ext <;> simp [values]

@[simp] theorem classify_point (f : CoordinateRing →ₐ[ℝ] S) : classify (point f) = f :=
  homEquiv.left_inv f

@[simp] theorem point_classify (z : Points S) : point (classify z) = z :=
  homEquiv.right_inv z

/-- Specialization is natural under every real algebra homomorphism. -/
theorem point_comp (f : CoordinateRing →ₐ[ℝ] S) (g : S →ₐ[ℝ] T) :
    point (g.comp f) = Units.map (map g.toRingHom).toMonoidHom (point f) := by
  apply Units.ext
  ext <;> rfl

/-- Classifying maps are natural under every real algebra homomorphism. -/
theorem classify_map (g : S →ₐ[ℝ] T) (z : Points S) :
    classify (Units.map (map g.toRingHom).toMonoidHom z) = g.comp (classify z) := by
  apply homEquiv.injective
  simp only [Equiv.coe_fn_mk, homEquiv, point_classify, point_comp]

/-- The coordinate ring as a real algebra object. -/
abbrev coordinateAlgebra : CommAlgCat ℝ := CommAlgCat.of ℝ CoordinateRing

/-- The Deligne-torus point functor is corepresented by its explicit coordinate algebra. -/
def corepresentableBy : (functor.{0} ⋙ forget GrpCat).CorepresentableBy coordinateAlgebra where
  homEquiv :=
    { toFun := fun f => point f.hom
      invFun := fun z => CommAlgCat.ofHom (classify z)
      left_inv := fun f => CommAlgCat.hom_ext (classify_point f.hom)
      right_inv := fun z => point_classify z }
  homEquiv_comp g f := point_comp f.hom g.hom

/-- The natural representation isomorphism on commutative real algebras. -/
def coyonedaIso : coyoneda.obj (Opposite.op coordinateAlgebra) ≅ functor.{0} ⋙ forget GrpCat :=
  corepresentableBy.toIso

/-- The affine real scheme given by the representing coordinate algebra. -/
def scheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of CoordinateRing)

/-- The structural morphism to the real base. -/
def structureMap : scheme ⟶ AlgebraicGeometry.Spec (CommRingCat.of ℝ) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℝ CoordinateRing))

end Langlands.Shimura.DeligneTorus
