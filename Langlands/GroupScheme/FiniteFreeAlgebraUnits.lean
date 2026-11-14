import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.CorepresentedSmoothGeometry
import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange
import Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel
import Langlands.GroupScheme.GeneralLinear
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

/-! # Unit group schemes of finite free, possibly noncommutative algebras over a ring -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteFreeAlgebraUnits

variable {R : CommRingCat.{u}} {A : Type u} [Ring A] [Algebra R A]

variable (R) in
/-- Coordinate ring of the affine space attached to a finite basis. -/
abbrev coordinateRing (n : ℕ) := MvPolynomial (Fin n) R

variable {n : ℕ} (b : Module.Basis (Fin n) R A)

/-- The generic element, with polynomial coordinates in the first tensor factor. -/
def genericElement : coordinateRing R n ⊗[R] A :=
  ∑ i, MvPolynomial.X i ⊗ₜ[R] b i

/-- The determinant of multiplication by the generic element. -/
def determinant : coordinateRing R n :=
  Algebra.norm (coordinateRing R n) (genericElement b)

lemma determinant_eq_matrix_det :
    determinant b =
      (Algebra.leftMulMatrix (b.baseChange (coordinateRing R n)) (genericElement b)).det :=
  Algebra.norm_eq_matrix_det _ _

/-- The away-localization whose spectrum is the determinant-open candidate. -/
abbrev candidateRing := Localization.Away (determinant b)

/-- The generic element after passing to the determinant-open coordinate ring. -/
def localizedGenericElement : candidateRing b ⊗[R] A :=
  Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom R (coordinateRing R n) (candidateRing b))
    (AlgHom.id R A) (genericElement b)

lemma localizedGenericElement_eq_sum :
    localizedGenericElement b =
      ∑ i, algebraMap (coordinateRing R n) (candidateRing b) (MvPolynomial.X i) ⊗ₜ[R] b i := by
  simp [localizedGenericElement, genericElement]

section ChangeCoefficients

variable {S C : Type u} [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]
  (φ : S →ₐ[R] C)

/-- Multiplication matrices commute with a change in the coefficient tensor factor. -/
lemma leftMulMatrix_map (x : S ⊗[R] A) :
    Algebra.leftMulMatrix (b.baseChange C)
        (Algebra.TensorProduct.map φ (AlgHom.id R A) x) =
      (Algebra.leftMulMatrix (b.baseChange S) x).map φ := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    ext i j
    simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy, Matrix.map_add]

include b in
/-- The finite-free norm commutes with this coefficient change. -/
lemma norm_map (x : S ⊗[R] A) :
    Algebra.norm C (Algebra.TensorProduct.map φ (AlgHom.id R A) x) =
      φ (Algebra.norm S x) := by
  rw [Algebra.norm_eq_matrix_det (b.baseChange C),
    leftMulMatrix_map b φ, Algebra.norm_eq_matrix_det (b.baseChange S)]
  exact (φ.map_det _).symm

end ChangeCoefficients

/-- The localized generic element is invertible, including for the zero algebra. -/
lemma localizedGenericElement_isUnit : IsUnit (localizedGenericElement b) := by
  let : Module.Free (candidateRing b) (candidateRing b ⊗[R] A) :=
    Module.Free.of_basis (b.baseChange (candidateRing b))
  let : Module.Finite (candidateRing b) (candidateRing b ⊗[R] A) :=
    Module.Finite.of_basis (b.baseChange (candidateRing b))
  apply (Algebra.lmul_isUnit_iff (R := candidateRing b)).mp
  apply (LinearMap.isUnit_iff_isUnit_det _).mpr
  change IsUnit (Algebra.norm (candidateRing b) (localizedGenericElement b))
  rw [localizedGenericElement, norm_map b]
  exact IsLocalization.Away.algebraMap_isUnit (determinant b)

/-- A unit with the localized generic element as its underlying value. -/
def algebraicUniversalUnit : (candidateRing b ⊗[R] A)ˣ :=
  (localizedGenericElement_isUnit b).unit

@[simp]
lemma algebraicUniversalUnit_val :
    (algebraicUniversalUnit b : candidateRing b ⊗[R] A) = localizedGenericElement b :=
  (localizedGenericElement_isUnit b).unit_spec

/-- The determinant-open coordinate ring is smooth over the base ring. -/
instance candidateRing_smooth : Algebra.Smooth R (candidateRing b) := by
  let : Algebra.Smooth (coordinateRing R n) (candidateRing b) :=
    Algebra.Smooth.of_isLocalization_Away (determinant b)
  exact Algebra.Smooth.comp R (coordinateRing R n) (candidateRing b)

variable {B : Type u} [CommRing B] [Algebra R B]

/-- Evaluate the generic element under a polynomial coefficient map. -/
def evaluatedElement (φ : coordinateRing R n →ₐ[R] B) : B ⊗[R] A :=
  Algebra.TensorProduct.map φ (AlgHom.id R A) (genericElement b)

lemma evaluatedElement_eq_sum (φ : coordinateRing R n →ₐ[R] B) :
    evaluatedElement b φ = ∑ i, φ (MvPolynomial.X i) ⊗ₜ[R] b i := by
  simp [evaluatedElement, genericElement]

@[simp]
lemma evaluatedElement_repr (φ : coordinateRing R n →ₐ[R] B) (i : Fin n) :
    (b.baseChange B).repr (evaluatedElement b φ) i = φ (MvPolynomial.X i) := by
  simp [evaluatedElement_eq_sum, map_sum, Module.Basis.repr_self, Finsupp.single_apply]

lemma evaluatedElement_injective : Function.Injective (evaluatedElement b (B := B)) := by
  intro φ ψ h
  apply MvPolynomial.algHom_ext
  intro i
  simpa using congrArg (fun x => (b.baseChange B).repr x i) h

/-- The coefficient homomorphism determined by a tensor element. -/
def coefficientMap (x : B ⊗[R] A) : coordinateRing R n →ₐ[R] B :=
  MvPolynomial.aeval fun i => (b.baseChange B).repr x i

@[simp]
lemma evaluatedElement_coefficientMap (x : B ⊗[R] A) :
    evaluatedElement b (coefficientMap b x) = x := by
  apply (b.baseChange B).repr.injective
  ext i
  simp [coefficientMap]

lemma norm_evaluatedElement (φ : coordinateRing R n →ₐ[R] B) :
    Algebra.norm B (evaluatedElement b φ) = φ (determinant b) :=
  norm_map b φ (genericElement b)

lemma coefficientMap_determinant_isUnit (x : (B ⊗[R] A)ˣ) :
    IsUnit (coefficientMap b (x : B ⊗[R] A) (determinant b)) := by
  let := Module.Free.of_basis (b.baseChange B)
  let := Module.Finite.of_basis (b.baseChange B)
  rw [← norm_evaluatedElement, evaluatedElement_coefficientMap]
  exact (LinearMap.isUnit_iff_isUnit_det _).mp
    ((Algebra.lmul_isUnit_iff (R := B)).mpr x.isUnit)

/-- The unique localization map encoded by a unit tensor. -/
def unitCoefficientMap (x : (B ⊗[R] A)ˣ) : candidateRing b →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (determinant b) (coefficientMap_determinant_isUnit b x)

@[simp]
lemma unitCoefficientMap_algebraMap (x : (B ⊗[R] A)ˣ) (r : coordinateRing R n) :
    unitCoefficientMap b x (algebraMap (coordinateRing R n) (candidateRing b) r) =
      coefficientMap b (x : B ⊗[R] A) r := by
  exact IsLocalization.Away.lift_eq (determinant b)
    (coefficientMap_determinant_isUnit b x) r

/-- Pull back the algebraic universal unit by a candidate-ring homomorphism. -/
def algebraicPoint (φ : candidateRing b →ₐ[R] B) : (B ⊗[R] A)ˣ :=
  Units.map (Algebra.TensorProduct.map φ (AlgHom.id R A)).toMonoidHom
    (algebraicUniversalUnit b)

lemma algebraicPoint_val (φ : candidateRing b →ₐ[R] B) :
    (algebraicPoint b φ : B ⊗[R] A) =
      evaluatedElement b (φ.comp (Algebra.algHom R (coordinateRing R n) (candidateRing b))) := by
  simp [algebraicPoint, algebraicUniversalUnit_val, localizedGenericElement_eq_sum,
    evaluatedElement_eq_sum, Algebra.algHom]

@[simp]
lemma algebraicPoint_unitCoefficientMap (x : (B ⊗[R] A)ˣ) :
    algebraicPoint b (unitCoefficientMap b x) = x := by
  apply Units.ext
  rw [algebraicPoint_val]
  have h : (unitCoefficientMap b x).comp
      (Algebra.algHom R (coordinateRing R n) (candidateRing b)) =
      coefficientMap b (x : B ⊗[R] A) := by
    apply AlgHom.ext
    intro r
    exact unitCoefficientMap_algebraMap b x r
  rw [h, evaluatedElement_coefficientMap]

lemma algebraicPoint_injective : Function.Injective (algebraicPoint b (B := B)) := by
  intro φ ψ h
  apply IsLocalization.algHom_ext (Submonoid.powers (determinant b))
  apply evaluatedElement_injective b
  simpa only [algebraicPoint_val] using congrArg Units.val h

/-- Finite-free determinant coordinates represent units on every algebra. -/
def algebraicPointEquiv : (candidateRing b →ₐ[R] B) ≃ (B ⊗[R] A)ˣ where
  toFun := algebraicPoint b
  invFun := unitCoefficientMap b
  left_inv _φ := algebraicPoint_injective b (algebraicPoint_unitCoefficientMap b _)
  right_inv := algebraicPoint_unitCoefficientMap b

variable {C : Type u} [CommRing C] [Algebra R C]

/-- Specializing the universal unit commutes with every coefficient-algebra map. -/
theorem algebraicPoint_comp (φ : candidateRing b →ₐ[R] B) (f : B →ₐ[R] C) :
    algebraicPoint b (f.comp φ) =
      Units.map (Algebra.TensorProduct.map f (AlgHom.id R A)).toMonoidHom
        (algebraicPoint b φ) := by
  apply Units.ext
  simp [algebraicPoint_val, evaluatedElement_eq_sum]

variable (R A) in
/-- The unit functor `S ↦ (S ⊗[R] A)ˣ` of a possibly noncommutative algebra. -/
def functor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj S := GrpCat.of (S ⊗[R] A)ˣ
  map f := GrpCat.ofHom (Units.map
    (Algebra.TensorProduct.map f.hom (AlgHom.id R A)).toMonoidHom)
  map_id S := by
    ext x
    simp
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    exact AlgHom.congr_fun
      (Algebra.TensorProduct.map_comp g.hom f.hom (AlgHom.id R A) (AlgHom.id R A)) x

/-- The determinant-open coordinate ring as a commutative base algebra. -/
abbrev coordinateAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (candidateRing b)

/-- The determinant-open coordinates corepresent the units. -/
def corepresentableBy :
    (functor R A ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra b) where
  homEquiv :=
    { toFun := fun φ => algebraicPoint b φ.hom
      invFun := fun x => CommAlgCat.ofHom (unitCoefficientMap b x)
      left_inv := fun φ => CommAlgCat.hom_ext ((algebraicPointEquiv b).left_inv φ.hom)
      right_inv := algebraicPoint_unitCoefficientMap b }
  homEquiv_comp f φ := algebraicPoint_comp b φ.hom f.hom

/-- The affine group scheme of units of the finite free algebra over `Spec R`. -/
abbrev groupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (functor R A) (corepresentableBy b)

/-- The structure morphism is the spectrum of the determinant-open coordinate algebra. -/
theorem groupScheme_hom :
    (groupScheme b).X.hom = Spec.map (CommRingCat.ofHom (algebraMap R (candidateRing b))) :=
  rfl

instance groupScheme_isAffine : IsAffine (groupScheme b).X.left := by
  change IsAffine (Spec (CommRingCat.of (candidateRing b)))
  infer_instance

instance groupScheme_isAffineHom : IsAffineHom (groupScheme b).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (candidateRing b))))
  infer_instance

theorem smooth : Smooth (groupScheme b).X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (candidateRing b))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (candidateRing b)).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

instance groupScheme_smooth : Smooth (groupScheme b).X.hom := smooth b

instance groupScheme_flat : Flat (groupScheme b).X.hom := inferInstance

instance groupScheme_locallyOfFiniteType : LocallyOfFiniteType (groupScheme b).X.hom :=
  inferInstance

/-- On every test scheme, points are units over its relative global sections. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme b).X) ≃* (((algΓ R).obj T).unop ⊗[R] A)ˣ :=
  Corepresented.pointsEquiv (functor R A) (corepresentableBy b) T

/-- The point comparison respects the relative section pullback. -/
theorem pointsEquiv_naturality {T T' : Over (Spec R)} (f : T' ⟶ T)
    (x : T ⟶ (groupScheme b).X) :
    pointsEquiv b T' (f ≫ x) =
      Units.map (Algebra.TensorProduct.map
        (((algΓ R).map f).unop.hom) (AlgHom.id R A)).toMonoidHom
        (pointsEquiv b T x) :=
  Corepresented.pointsEquiv_naturality (functor R A) (corepresentableBy b) f x

/-- Removing the global-sections tensor factor on the identity test scheme. -/
def sectionTensorEquiv :
    ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop ⊗[R] A ≃ₐ[R] A :=
  (Algebra.TensorProduct.congr (WeilGm.selfSectionsAlgEquiv R) AlgEquiv.refl).trans
    (Algebra.TensorProduct.lid R A)

/-- Sections over `Spec R` are the units of `A`. -/
def sectionUnitsEquiv : rationalPoints (groupScheme b) ≃* Aˣ :=
  (pointsEquiv b (Over.mk (𝟙 (Spec R)))).trans
    (Units.mapEquiv (sectionTensorEquiv (R := R) (A := A)).toMulEquiv)

/-! ### Base change -/

section BaseChange

variable (R' : CommRingCat.{u}) [Algebra R R']

section Algebraic

variable (S : Type u) [CommRing S] [Algebra R S] [Algebra R' S] [IsScalarTower R R' S]

variable (A) in
/-- The ring isomorphism `S ⊗[R] A ≃ S ⊗[R'] (R' ⊗[R] A)`, `s ⊗ a ↦ s ⊗ (1 ⊗ a)`. -/
def baseChangeTensorEquiv : S ⊗[R] A ≃+* S ⊗[R'] (R' ⊗[R] A) :=
  (Algebra.TensorProduct.congr ((Algebra.TensorProduct.rid R' S S).restrictScalars R)
      (AlgEquiv.refl : A ≃ₐ[R] A)).symm.toRingEquiv.trans
    (Algebra.TensorProduct.assoc R R' S S R' A).toRingEquiv

@[simp] theorem baseChangeTensorEquiv_tmul (s : S) (a : A) :
    baseChangeTensorEquiv A R' S (s ⊗ₜ[R] a) = s ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] a) := by
  simp [baseChangeTensorEquiv]

/-- The isomorphism commutes with maps of `R'`-algebras; `ψ` is the same map over `R`. -/
theorem baseChangeTensorEquiv_natural {S' : Type u} [CommRing S'] [Algebra R S'] [Algebra R' S']
    [IsScalarTower R R' S'] (φ : S →ₐ[R'] S') (ψ : S →ₐ[R] S') (h : ∀ s, ψ s = φ s)
    (w : S ⊗[R] A) :
    baseChangeTensorEquiv A R' S' (Algebra.TensorProduct.map ψ (AlgHom.id R A) w) =
      Algebra.TensorProduct.map φ (AlgHom.id R' (R' ⊗[R] A))
        (baseChangeTensorEquiv A R' S w) := by
  induction w using TensorProduct.inductionOn with
  | tmul s a => simp [h]
  | add w w' hw hw' => simp only [map_add, hw, hw']

end Algebraic

/-- Points of the base change are units of `Γ(T) ⊗[R'] (R' ⊗[R] A)`. -/
def basePointsEquiv (T : Over (Spec R')) :
    (T ⟶ ((GroupScheme.baseChange (WeilGm.baseMap R R')).obj (groupScheme b)).X) ≃*
      (((algΓ R').obj T).unop ⊗[R'] (R' ⊗[R] A))ˣ :=
  (GroupScheme.baseChangePointsEquiv (WeilGm.baseMap R R') (groupScheme b) T).trans
    ((pointsEquiv b ((Over.map (WeilGm.baseMap R R')).obj T)).trans
      (Units.mapEquiv
        (baseChangeTensorEquiv A R' (WeilGm.restrictedSections R R' T)).toMulEquiv))

theorem basePointsEquiv_apply (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange (WeilGm.baseMap R R')).obj (groupScheme b)).X) :
    basePointsEquiv b R' T x =
      Units.map (baseChangeTensorEquiv A R' (WeilGm.restrictedSections R R' T)).toMonoidHom
        (pointsEquiv b ((Over.map (WeilGm.baseMap R R')).obj T)
          (GroupScheme.baseChangePointsEquiv (WeilGm.baseMap R R') (groupScheme b) T x)) :=
  rfl

/-- The point model of the base change is natural in the test scheme. -/
theorem basePointsEquiv_naturality {T T' : Over (Spec R')} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (WeilGm.baseMap R R')).obj (groupScheme b)).X) :
    basePointsEquiv b R' T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.map ((algΓ R').map a).unop.hom
        (AlgHom.id R' (R' ⊗[R] A))).toMonoidHom
        (basePointsEquiv b R' T x) := by
  apply Units.ext
  rw [basePointsEquiv_apply, basePointsEquiv_apply,
    GroupScheme.baseChangePointsEquiv_naturality, pointsEquiv_naturality]
  set_option backward.isDefEq.respectTransparency false in
  exact baseChangeTensorEquiv_natural R' (WeilGm.restrictedSections R R' T)
    (S' := WeilGm.restrictedSections R R' T')
    ((algΓ R').map a).unop.hom ((algΓ R).map ((Over.map (WeilGm.baseMap R R')).map a)).unop.hom
    (fun _ => rfl) _

/-- Base change of the unit group of `A` along `Spec R' → Spec R` is the unit group of
`R' ⊗[R] A`, with the base-changed basis. -/
def baseChangeIso :
    (GroupScheme.baseChange (WeilGm.baseMap R R')).obj (groupScheme b) ≅
      groupScheme (b.baseChange R') :=
  isoOfPointModels (fun T : Over (Spec R') => (((algΓ R').obj T).unop ⊗[R'] (R' ⊗[R] A))ˣ)
    (fun a => Units.map (Algebra.TensorProduct.map ((algΓ R').map a).unop.hom
        (AlgHom.id R' (R' ⊗[R] A))).toMonoidHom)
    (basePointsEquiv b R') (pointsEquiv (b.baseChange R'))
    (fun a x => basePointsEquiv_naturality b R' a x)
    (fun a y => pointsEquiv_naturality (b.baseChange R') a y)

/-- On points, the isomorphism is the unit map of `Γ(T) ⊗[R] A ≃ Γ(T) ⊗[R'] (R' ⊗[R] A)`. -/
theorem baseChangeIso_hom_points (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange (WeilGm.baseMap R R')).obj (groupScheme b)).X) :
    pointsEquiv (b.baseChange R') T (x ≫ (baseChangeIso b R').hom.hom.hom) =
      basePointsEquiv b R' T x :=
  isoOfPointModels_hom (fun T : Over (Spec R') => (((algΓ R').obj T).unop ⊗[R'] (R' ⊗[R] A))ˣ)
    (fun a => Units.map (Algebra.TensorProduct.map ((algΓ R').map a).unop.hom
        (AlgHom.id R' (R' ⊗[R] A))).toMonoidHom)
    (basePointsEquiv b R') (pointsEquiv (b.baseChange R'))
    (fun a x => basePointsEquiv_naturality b R' a x)
    (fun a y => pointsEquiv_naturality (b.baseChange R') a y) T x

end BaseChange

/-! ### Geometric connectedness -/

/-- The spectrum of a polynomial ring is geometrically irreducible over the base. -/
theorem geometricallyIrreducible_spec_mvPolynomial (m : Type u) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial m R)))) := by
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [MvPolynomial.algebraMap_eq, ← AffineSpace.SpecIso_inv_over (n := m) R,
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible.{u})]
  infer_instance

/-- The spectrum of the coordinate ring is geometrically irreducible over the base. -/
theorem geometricallyIrreducible_spec_coordinateRing (n : ℕ) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R n)))) := by
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hA := geometricallyIrreducible_spec_mvPolynomial (R := R) (ULift.{u} (Fin n))
  let e : coordinateRing R n ≃ₐ[R] MvPolynomial (ULift.{u} (Fin n)) R :=
    MvPolynomial.renameEquiv R Equiv.ulift.symm
  have he : algebraMap R (coordinateRing R n) =
      (e.symm : MvPolynomial (ULift.{u} (Fin n)) R →+* coordinateRing R n).comp
        (algebraMap R (MvPolynomial (ULift.{u} (Fin n)) R)) :=
    (e.symm.toAlgHom.comp_algebraMap).symm
  have : IsIso (CommRingCat.ofHom
      (e.symm : MvPolynomial (ULift.{u} (Fin n)) R →+* coordinateRing R n)) :=
    e.symm.toRingEquiv.toCommRingCatIso.isIso_hom
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp,
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible.{u})]
  exact hA

/-- The structure morphism factors through the open immersion into affine space. -/
theorem groupScheme_hom_eq_comp :
    (groupScheme b).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (coordinateRing R n) (candidateRing b))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R n))) := by
  rw [groupScheme_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- Every fibre of the unit group scheme is geometrically irreducible: it is a nonempty open
subscheme of an affine space. -/
instance geometricallyIrreducible : GeometricallyIrreducible (groupScheme b).X.hom := by
  have hs : Surjective (groupScheme b).X.hom := surjective_hom (groupScheme b)
  have := geometricallyIrreducible_spec_coordinateRing (R := R) n
  rw [groupScheme_hom_eq_comp] at hs ⊢
  have h1 : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (coordinateRing R n) (candidateRing b)))) :=
    inferInstance
  exact @AlgebraicGeometry.instGeometricallyIrreducibleCompSchemeOfIsOpenImmersionOfSurjective
    _ _ _ _ _ h1 this hs

/-- Every fibre of the unit group scheme is geometrically connected. -/
instance geometricallyConnected : GeometricallyConnected (groupScheme b).X.hom :=
  GeometricallyIrreducible.geometricallyConnected _

/-! ### Change of algebra and the matrix algebra -/

section Congr

variable {A' : Type u} [Ring A'] [Algebra R A'] {m : ℕ} (b' : Module.Basis (Fin m) R A')
  (e : A ≃ₐ[R] A')

/-- An algebra isomorphism commutes with every change in the coefficient tensor factor. -/
theorem tensorCongr_map {S S' : Type u} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (f : S →ₐ[R] S') (w : S ⊗[R] A) :
    Algebra.TensorProduct.congr (AlgEquiv.refl : S' ≃ₐ[R] S') e
        (Algebra.TensorProduct.map f (AlgHom.id R A) w) =
      Algebra.TensorProduct.map f (AlgHom.id R A')
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[R] S) e w) := by
  induction w using TensorProduct.inductionOn with
  | tmul s a => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']

/-- Points of the unit group of `A`, modelled by units of `Γ(T) ⊗[R] A'`. -/
def congrPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme b).X) ≃* (((algΓ R).obj T).unop ⊗[R] A')ˣ :=
  (pointsEquiv b T).trans
    (Units.mapEquiv (Algebra.TensorProduct.congr
      (AlgEquiv.refl : ((algΓ R).obj T).unop ≃ₐ[R] ((algΓ R).obj T).unop) e).toMulEquiv)

theorem congrPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme b).X) :
    congrPointsEquiv b e T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.map ((algΓ R).map a).unop.hom
        (AlgHom.id R A')).toMonoidHom (congrPointsEquiv b e T x) := by
  apply Units.ext
  simp only [congrPointsEquiv, MulEquiv.trans_apply, pointsEquiv_naturality]
  exact tensorCongr_map e _ _

/-- Isomorphic finite free algebras, with arbitrary bases, have isomorphic unit group
schemes. -/
def congrIso : groupScheme b ≅ groupScheme b' :=
  isoOfPointModels (fun T : Over (Spec R) => (((algΓ R).obj T).unop ⊗[R] A')ˣ)
    (fun a => Units.map (Algebra.TensorProduct.map ((algΓ R).map a).unop.hom
      (AlgHom.id R A')).toMonoidHom)
    (congrPointsEquiv b e) (pointsEquiv b')
    (fun a x => congrPointsEquiv_naturality b e a x)
    (fun a y => pointsEquiv_naturality b' a y)

/-- On points, the isomorphism is the unit map of `Γ(T) ⊗[R] A ≃ Γ(T) ⊗[R] A'`. -/
theorem congrIso_hom_points (T : Over (Spec R)) (x : T ⟶ (groupScheme b).X) :
    pointsEquiv b' T (x ≫ (congrIso b b' e).hom.hom.hom) = congrPointsEquiv b e T x :=
  isoOfPointModels_hom (fun T : Over (Spec R) => (((algΓ R).obj T).unop ⊗[R] A')ˣ)
    (fun a => Units.map (Algebra.TensorProduct.map ((algΓ R).map a).unop.hom
      (AlgHom.id R A')).toMonoidHom)
    (congrPointsEquiv b e) (pointsEquiv b')
    (fun a x => congrPointsEquiv_naturality b e a x)
    (fun a y => pointsEquiv_naturality b' a y) T x

end Congr

section GeneralLinear

variable (R) (N : ℕ)

/-- The matrix-unit basis of `M_N(R)`, indexed by `Fin (N * N)`. -/
def matrixBasis : Module.Basis (Fin (N * N)) R (Matrix (Fin N) (Fin N) R) :=
  (Matrix.stdBasis R (Fin N) (Fin N)).reindex finProdFinEquiv

/-- Identifying `S ⊗[R] M_N(R)` with `M_N(S)` commutes with changing `S`. -/
theorem matrixEquivTensor_symm_map {S S' : Type u} [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] (f : S →ₐ[R] S') (w : S ⊗[R] Matrix (Fin N) (Fin N) R) :
    (matrixEquivTensor (Fin N) R S').symm
        (Algebra.TensorProduct.map f (AlgHom.id R (Matrix (Fin N) (Fin N) R)) w) =
      ((matrixEquivTensor (Fin N) R S).symm w).map f := by
  induction w using TensorProduct.inductionOn with
  | tmul s M =>
    ext i j
    simp [matrixEquivTensor_apply_symm, Matrix.map_apply, Matrix.smul_apply]
  | add w w' hw hw' =>
    simp only [map_add, hw, hw']
    ext i j
    simp

/-- Points of the unit group of `M_N(R)` are invertible `N × N` matrices over global
sections. -/
def matrixPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme (matrixBasis R N)).X) ≃*
      Matrix.GeneralLinearGroup (Fin N) Γ(T.left, ⊤) :=
  (pointsEquiv (matrixBasis R N) T).trans
    (Units.mapEquiv (matrixEquivTensor (Fin N) R ((algΓ R).obj T).unop).symm.toMulEquiv)

theorem matrixPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme (matrixBasis R N)).X) :
    matrixPointsEquiv R N T' (a ≫ x) =
      Matrix.GeneralLinearGroup.map a.left.appTop.hom (matrixPointsEquiv R N T x) := by
  apply Units.ext
  simp only [matrixPointsEquiv, MulEquiv.trans_apply, pointsEquiv_naturality]
  exact matrixEquivTensor_symm_map R N ((algΓ R).map a).unop.hom _

/-- The unit group scheme of the matrix algebra `M_N(R)` is the Library's `GL_N` over `R`. -/
def generalLinearIso :
    groupScheme (matrixBasis R N) ≅ GeneralLinear.groupScheme (Fin N) R :=
  isoOfPointModels (fun T : Over (Spec R) => Matrix.GeneralLinearGroup (Fin N) Γ(T.left, ⊤))
    (fun a => Matrix.GeneralLinearGroup.map a.left.appTop.hom)
    (matrixPointsEquiv R N) (GeneralLinear.pointsEquiv (Fin N) R)
    (fun a x => matrixPointsEquiv_naturality R N a x)
    (fun a y => GeneralLinear.pointsEquiv_naturality a y)

/-- On points, the isomorphism identifies `Γ(T) ⊗[R] M_N(R)` with `M_N(Γ(T))`. -/
theorem generalLinearIso_hom_points (T : Over (Spec R))
    (x : T ⟶ (groupScheme (matrixBasis R N)).X) :
    GeneralLinear.pointsEquiv (Fin N) R T (x ≫ (generalLinearIso R N).hom.hom.hom) =
      matrixPointsEquiv R N T x :=
  isoOfPointModels_hom
    (fun T : Over (Spec R) => Matrix.GeneralLinearGroup (Fin N) Γ(T.left, ⊤))
    (fun a => Matrix.GeneralLinearGroup.map a.left.appTop.hom)
    (matrixPointsEquiv R N) (GeneralLinear.pointsEquiv (Fin N) R)
    (fun a x => matrixPointsEquiv_naturality R N a x)
    (fun a y => GeneralLinear.pointsEquiv_naturality a y) T x

end GeneralLinear

end Langlands.GroupScheme.FiniteFreeAlgebraUnits
