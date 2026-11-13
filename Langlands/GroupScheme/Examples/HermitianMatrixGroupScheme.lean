import Langlands.GroupScheme.Examples.SU3GroupScheme
import Langlands.GroupScheme.Examples.HermitianMatrixPresentation

/-!
# The special unitary group scheme of an arbitrary nonsingular Hermitian matrix

For a separable quadratic extension `L/k` and a nonsingular Hermitian matrix `H` over `L`,
this module constructs the special unitary group scheme `SU(H)` over `k` as the scheme
equalizer of the identity and of the inverse-adjoint twist `g ↦ H⁻¹ (g*)⁻¹ H` on the Weil
restriction of `SL` from `L` to `k`, and identifies its points on every test scheme `T`
with the determinant-one isometries of `H` over `L ⊗_k Γ(T)`, naturally in `T`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

section Algebra

variable {A B : Type*} [CommRing A] [CommRing B] {Ix : Type*} [Fintype Ix] [DecidableEq Ix]
  {c : RingInvolution A} {d : RingInvolution B}

theorem det_adjoint (M : Matrix Ix Ix A) : (adjoint c M).det = c.bar M.det := by
  rw [adjoint, Matrix.det_transpose]
  exact (RingHom.map_det (c.bar : A →+* A) M).symm

theorem gram_mul_gram_inv (H : Form c Ix) :
    (H.gram : Matrix Ix Ix A) * ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) =
      1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem gram_inv_mul_gram (H : Form c Ix) :
    ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) * (H.gram : Matrix Ix Ix A) =
      1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem adjoint_mul_adjoint_inv (g : Matrix.SpecialLinearGroup Ix A) :
    adjoint c (g : Matrix Ix Ix A) *
        adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) = 1 := by
  rw [← adjoint_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, adjoint_one]

theorem adjoint_inv_mul_adjoint (g : Matrix.SpecialLinearGroup Ix A) :
    adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
        adjoint c (g : Matrix Ix Ix A) = 1 := by
  rw [← adjoint_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, adjoint_one]

/-- The inverse-adjoint twist `g ↦ H⁻¹ (g*)⁻¹ H` of a nonsingular Hermitian Gram matrix,
as an endomorphism of the special linear group. -/
def gramTwist (H : Form c Ix) :
    Matrix.SpecialLinearGroup Ix A →* Matrix.SpecialLinearGroup Ix A where
  toFun g := ⟨((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
      adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
        (H.gram : Matrix Ix Ix A), by
    rw [Matrix.det_mul, Matrix.det_mul, det_adjoint, Matrix.SpecialLinearGroup.det_coe,
      map_one, mul_one, ← Matrix.det_mul, gram_inv_mul_gram, Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    change ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
      adjoint c ((1⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
        (H.gram : Matrix Ix Ix A) = 1
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, adjoint_one, Matrix.mul_one,
      gram_inv_mul_gram]
  map_mul' g h := by
    apply Subtype.ext
    change ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
        adjoint c (((g * h)⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
          (H.gram : Matrix Ix Ix A) =
      (((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
        adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
          (H.gram : Matrix Ix Ix A)) *
      (((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
        adjoint c ((h⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
          (H.gram : Matrix Ix Ix A))
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, adjoint_mul]
    calc
      _ = ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
          adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
            ((H.gram : Matrix Ix Ix A) *
              ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A)) *
          adjoint c ((h⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
            (H.gram : Matrix Ix Ix A) := by
        rw [gram_mul_gram_inv, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_gramTwist (H : Form c Ix) (g : Matrix.SpecialLinearGroup Ix A) :
    ((gramTwist H g : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) =
      ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
        adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
          (H.gram : Matrix Ix Ix A) := rfl

/-- A determinant-one matrix is fixed by the Gram twist exactly when it preserves the
Hermitian pairing. -/
theorem gramTwist_eq_self_iff (H : Form c Ix) (g : Matrix.SpecialLinearGroup Ix A) :
    gramTwist H g = g ↔
      adjoint c (g : Matrix Ix Ix A) * (H.gram : Matrix Ix Ix A) * (g : Matrix Ix Ix A) =
        H.gram := by
  constructor
  · intro h
    have h' := congrArg (fun x : Matrix.SpecialLinearGroup Ix A => (x : Matrix Ix Ix A)) h
    simp only [coe_gramTwist] at h'
    calc
      _ = adjoint c (g : Matrix Ix Ix A) * (H.gram : Matrix Ix Ix A) *
          (((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
            adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
              (H.gram : Matrix Ix Ix A)) := by rw [h']
      _ = adjoint c (g : Matrix Ix Ix A) * ((H.gram : Matrix Ix Ix A) *
          ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A)) *
            adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
              (H.gram : Matrix Ix Ix A) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [gram_mul_gram_inv, Matrix.mul_one, adjoint_mul_adjoint_inv, Matrix.one_mul]
  · intro h
    apply Subtype.ext
    rw [coe_gramTwist]
    calc
      _ = ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
          adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
            (adjoint c (g : Matrix Ix Ix A) * (H.gram : Matrix Ix Ix A) *
              (g : Matrix Ix Ix A)) := by rw [h]
      _ = ((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
          (adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
            adjoint c (g : Matrix Ix Ix A)) * (H.gram : Matrix Ix Ix A) *
              (g : Matrix Ix Ix A) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [adjoint_inv_mul_adjoint, Matrix.mul_one, gram_inv_mul_gram, Matrix.one_mul]

/-- The Gram twist commutes with every involution-compatible coefficient map. -/
theorem gramTwist_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) (H : Form c Ix)
    (g : Matrix.SpecialLinearGroup Ix A) :
    Matrix.SpecialLinearGroup.map f (gramTwist H g) =
      gramTwist (H.map f hf) (Matrix.SpecialLinearGroup.map f g) := by
  apply Subtype.ext
  change (((H.gram⁻¹ : Matrix.GeneralLinearGroup Ix A) : Matrix Ix Ix A) *
      adjoint c ((g⁻¹ : Matrix.SpecialLinearGroup Ix A) : Matrix Ix Ix A) *
        (H.gram : Matrix Ix Ix A)).map f = _
  rw [coe_gramTwist, ← map_inv, Matrix.map_mul, Matrix.map_mul, ← adjoint_map f hf]
  rfl

end Algebra

namespace GroupModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Idx : Type} [Fintype Idx] [DecidableEq Idx]

attribute [local instance] SpecialLinear.WeilRoot.specialLinear_affine
  SpecialLinear.WeilRoot.specialLinear_finiteType

/-- The Weil restriction of `SL` on `Idx` from `L` to `k`. -/
abbrev ambient (Idx : Type) [Fintype Idx] [DecidableEq Idx] :
    GroupScheme (Spec (CommRingCat.of k)) :=
  SpecialLinear.WeilRoot.groupScheme (n := Idx) k L

variable (H : Form (fieldInvolution k L) Idx)

/-- The Gram twist on the points of the Weil restriction over a test scheme. -/
def twistPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (ambient k L Idx).X) →* (T ⟶ (ambient k L Idx).X) :=
  (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm.toMonoidHom.comp
    ((gramTwist (SchemeModel.tensorForm k L H T)).comp
      (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).toMonoidHom)

@[simp] theorem tensorMatrixEquiv_twistPoints (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L Idx).X) :
    SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (twistPoints k L H T x) =
      gramTwist (SchemeModel.tensorForm k L H T)
        (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x) :=
  (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).apply_symm_apply _

theorem tensorForm_map {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    (SchemeModel.tensorForm k L H T).map (SpecialLinear.WeilRoot.tensorMap k L a)
        (SU3Root.SchemeModel.tensorMap_bar k L a) =
      SchemeModel.tensorForm k L H T' := by
  apply Form.ext
  apply Units.ext
  exact SchemeModel.tensorMap_gram k L H a

/-- The Gram twist commutes with every change of test scheme. -/
theorem twistPoints_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (ambient k L Idx).X) :
    twistPoints k L H T' (a ≫ x) = a ≫ twistPoints k L H T x := by
  apply (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T').injective
  rw [tensorMatrixEquiv_twistPoints,
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality,
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality, tensorMatrixEquiv_twistPoints,
    gramTwist_map _ (SU3Root.SchemeModel.tensorMap_bar k L a), tensorForm_map]

/-- The Gram twist as a group-scheme endomorphism of the Weil restriction. -/
def twist : ambient k L Idx ⟶ ambient k L Idx :=
  homOfPoints (twistPoints k L H) (twistPoints_naturality k L H)

@[simp] theorem tensorMatrixEquiv_twist (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L Idx).X) :
    SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (x ≫ (twist k L H).hom.hom) =
      gramTwist (SchemeModel.tensorForm k L H T)
        (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x) := by
  rw [twist, comp_homOfPoints, tensorMatrixEquiv_twistPoints]

/-- The subgroup functor fixed by the Gram twist. -/
abbrev fixedFunctor : SubgroupFunctor (ambient k L Idx) :=
  endomorphismFixedSubgroup (twist k L H)

/-- Test points are fixed exactly when their tensor matrices preserve the Hermitian form. -/
theorem mem_fixedFunctor_iff (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (ambient k L Idx).X) :
    x ∈ (fixedFunctor k L H).carrier T ↔
      Preserves (SchemeModel.tensorForm k L H T)
        ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x :
          Matrix.SpecialLinearGroup Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)) :
            Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)) := by
  change x ≫ (twist k L H).hom.hom = x ↔ _
  rw [← (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).injective.eq_iff,
    tensorMatrixEquiv_twist, gramTwist_eq_self_iff]
  rfl

/-- The special unitary group scheme of `H`: the scheme equalizer of the Gram twist and
the identity of the Weil restriction. -/
def groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  (fixedFunctor k L H).representingGroupScheme
    (equalizer.ι (twist k L H).hom.hom (𝟙 (ambient k L Idx).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L H) x)

/-- The inclusion of the special unitary group into the Weil restriction. -/
def inclusion : groupScheme k L H ⟶ ambient k L Idx :=
  (fixedFunctor k L H).representingHom
    (equalizer.ι (twist k L H).hom.hom (𝟙 (ambient k L Idx).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L H) x)

@[simp] theorem inclusion_hom :
    (inclusion k L H).hom.hom =
      equalizer.ι (twist k L H).hom.hom (𝟙 (ambient k L Idx).X) :=
  (fixedFunctor k L H).representingHom_hom _ _

/-- The inclusion is a closed immersion. -/
instance inclusion_isClosedImmersion :
    IsClosedImmersion (inclusion k L H).hom.hom.left := by
  have : IsSeparated (ambient k L Idx).X.hom := inferInstance
  rw [inclusion_hom]
  exact AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
    (twist k L H).hom.hom (𝟙 (ambient k L Idx).X)

/-- The special unitary group scheme is affine. -/
instance groupScheme_isAffine : IsAffine (groupScheme k L H).X.left := by
  have : IsAffine (ambient k L Idx).X.left := inferInstance
  exact isAffine_of_isAffineHom (inclusion k L H).hom.hom.left

/-- The structure morphism of the special unitary group scheme is affine. -/
instance groupScheme_isAffineHom : IsAffineHom (groupScheme k L H).X.hom :=
  inferInstance

/-- Scheme-equalizer points are the fixed subgroup functor, multiplicatively. -/
def fixedPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (groupScheme k L H).X) ≃* (fixedFunctor k L H).carrier T where
  toEquiv := ((fixedFunctor k L H).schemeRepresentableBy
    (equalizer.ι (twist k L H).hom.hom (𝟙 (ambient k L Idx).X))
    (fun _ x => mem_endomorphismFixedSubgroup_iff_factors (twist k L H) x)).homEquiv
  map_mul' x y := by
    apply Subtype.ext
    change (x * y) ≫ _ = (x ≫ _) * (y ≫ _)
    rw [← inclusion_hom k L H, MonObj.mul_comp]

/-- Points of the tensor isometry group preserve the scalar-extended form. -/
theorem tensorPoints_preserves (T : Over (Spec (CommRingCat.of k)))
    (g : SchemeModel.tensorPoints k L H T) :
    Preserves (SchemeModel.tensorForm k L H T)
      (g.1 : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)) :=
  (Subgroup.mem_inf.mp g.2).1

/-- Points of the tensor isometry group have determinant one. -/
theorem tensorPoints_det (T : Over (Spec (CommRingCat.of k)))
    (g : SchemeModel.tensorPoints k L H T) :
    (g.1 : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)).det = 1 := by
  have h := (Subgroup.mem_inf.mp g.2).2
  rw [MonoidHom.mem_ker] at h
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

/-- A point of the tensor isometry group as a determinant-one matrix. -/
def tensorPointsToSL (T : Over (Spec (CommRingCat.of k)))
    (g : SchemeModel.tensorPoints k L H T) :
    Matrix.SpecialLinearGroup Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T) :=
  ⟨(g.1 : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)),
    tensorPoints_det k L H T g⟩

set_option maxRecDepth 2048 in
/-- The fixed subgroup functor consists exactly of the determinant-one isometries of the
scalar-extended Hermitian form. -/
def fixedTensorEquiv (T : Over (Spec (CommRingCat.of k))) :
    (fixedFunctor k L H).carrier T ≃* SchemeModel.tensorPoints k L H T where
  toFun x := ⟨Matrix.SpecialLinearGroup.toGL
      (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x.1),
    Subgroup.mem_inf.mpr ⟨(mem_fixedFunctor_iff k L H T x.1).mp x.2,
      by
        rw [MonoidHom.mem_ker]
        apply Units.ext
        exact (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x.1).2⟩⟩
  invFun g := ⟨(SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm
      (tensorPointsToSL k L H T g),
    (mem_fixedFunctor_iff k L H T _).mpr (by
      have h := congrArg
        (fun y : Matrix.SpecialLinearGroup Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T) =>
          (y : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)))
        ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).apply_symm_apply
          (tensorPointsToSL k L H T g))
      simp only at h
      rw [h]
      exact tensorPoints_preserves k L H T g)⟩
  left_inv x := by
    apply Subtype.ext
    change (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm
      (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T x.1) = x.1
    exact (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).symm_apply_apply x.1
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val
      ((SpecialLinear.WeilRoot.tensorMatrixEquiv k L T).apply_symm_apply
        (tensorPointsToSL k L H T g))
  map_mul' x y := by
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.toGL
        (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (x.1 * y.1)) = _
    rw [map_mul, map_mul]
    rfl

/-- All points of the special unitary group scheme are the determinant-one isometries of
`H` over the tensor coefficient ring. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (groupScheme k L H).X) ≃* SchemeModel.tensorPoints k L H T :=
  (fixedPointsEquiv k L H T).trans (fixedTensorEquiv k L H T)

/-- The point comparison is the tensor matrix of the ambient inclusion. -/
theorem pointsEquiv_val (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme k L H).X) :
    ((pointsEquiv k L H T x).1 : Matrix Idx Idx
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
    (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T (x ≫ (inclusion k L H).hom.hom) :
      Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)) := by
  rw [inclusion_hom]
  rfl

/-- The point comparison respects every change of test scheme. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme k L H).X) :
    ((pointsEquiv k L H T' (a ≫ x)).1 : Matrix Idx Idx
      (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      (((pointsEquiv k L H T x).1 : Matrix Idx Idx
        (SpecialLinear.WeilRoot.tensorAlgebra k L T))).map
          (SpecialLinear.WeilRoot.tensorMap k L a) := by
  rw [pointsEquiv_val, pointsEquiv_val, Category.assoc,
    SpecialLinear.WeilRoot.tensorMatrixEquiv_naturality]
  rfl

/-- The special unitary group scheme of `H` with its all-test matrix presentation. -/
def presentation : SchemeModel.Presentation k L H (groupScheme k L H) where
  pointsEquiv := pointsEquiv k L H
  matrix_naturality := pointsEquiv_naturality k L H

end GroupModel

end Langlands.GroupScheme.HermitianMatrix
