import Langlands.GroupScheme.BilinearCoordinateGroup
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Reductive.UnipotentExtension

/-! # Unipotence of bilinear coordinate groups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.BilinearCoordinate

variable (R : CommRingCat.{u}) {I : Type u} [Fintype I] (c : I → I → R)
  {n : ℕ} (b : Fin n ≃ I)

/-- The vector coordinate functions are primitive for the bilinear group law. -/
theorem vectorPrimitive :
    VectorGroup.IsPrimitiveFamily (corepresentableBy R c)
      (fun i => (X (some (b i)) : MvPolynomial (Option I) R)) := by
  intro A x y i
  simp [corepresentableBy, valuation, functor]

/-- Projection to the additive vector coordinate, in a finite indexing. -/
def vectorProjection : groupScheme R c ⟶ VectorGroup.groupScheme R n :=
  VectorGroup.quotientMap (vectorPrimitive R c b)

theorem coordinates_vectorProjection {T : Over (Spec R)} (x : T ⟶ (groupScheme R c).X)
    (i : Fin n) :
    (VectorGroup.coordinates R n T (x ≫ (vectorProjection R c b).hom.hom)).toAdd i =
      (pointsEquiv R c T x).vec (b i) := by
  change (VectorGroup.coordinates R n T
    (x ≫ (VectorGroup.quotientMap (vectorPrimitive R c b)).hom.hom)).toAdd i = _
  rw [VectorGroup.coordinates_quotientMap]
  change (aeval (valuation (pointsEquiv R c T x).vec (pointsEquiv R c T x).scalar) :
    MvPolynomial (Option I) R →ₐ[R] ((algΓ R).obj T).unop) (X (some (b i))) = _
  rw [aeval_X]
  rfl

/-- The vector variables and the one scalar variable exhaust the coordinate ring. -/
def vectorScalarVariableEquiv : Fin n ⊕ ULift.{u} Unit ≃ Option I where
  toFun := Sum.elim (fun i => some (b i)) (fun _ => none)
  invFun := Option.elim' (Sum.inr ⟨()⟩) (fun i => Sum.inl (b.symm i))
  left_inv x := by
    rcases x with i | ⟨⟨⟩⟩ <;> simp
  right_inv x := by
    cases x <;> simp

omit [Fintype I] in
theorem vectorScalarGenerators :
    Function.Bijective
      (aeval (Sum.elim (fun i => X (some (b i))) (fun _ : ULift.{u} Unit => X none)) :
        MvPolynomial (Fin n ⊕ ULift.{u} Unit) R →ₐ[R] MvPolynomial (Option I) R) := by
  have he :
      (aeval (Sum.elim (fun i => X (some (b i))) (fun _ : ULift.{u} Unit => X none)) :
        MvPolynomial (Fin n ⊕ ULift.{u} Unit) R →ₐ[R] MvPolynomial (Option I) R) =
      (renameEquiv R (vectorScalarVariableEquiv b)).toAlgHom := by
    apply algHom_ext
    intro x
    cases x <;> simp [vectorScalarVariableEquiv]
  rw [he]
  exact (renameEquiv R (vectorScalarVariableEquiv b)).bijective

theorem isAffineHom_vectorProjection : IsAffineHom (vectorProjection R c b).hom.hom.left := by
  change IsAffineHom (VectorGroup.quotientMap (vectorPrimitive R c b)).hom.hom.left
  rw [VectorGroup.quotientMap_left]
  change IsAffineHom (Spec.map (CommRingCat.ofHom
    (aeval (fun i => X (some (b i))) :
      MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Option I) R).toRingHom))
  exact isAffineHom_of_isAffine _

theorem flat_vectorProjection : Flat (vectorProjection R c b).hom.hom.left :=
  VectorGroup.flat_quotientMap (vectorPrimitive R c b) (vectorScalarGenerators R b)

theorem surjective_vectorProjection : Surjective (vectorProjection R c b).hom.hom.left :=
  VectorGroup.surjective_quotientMap (vectorPrimitive R c b) (vectorScalarGenerators R b)

theorem vectorProjection_eq_one_iff {T : Over (Spec R)} (x : T ⟶ (groupScheme R c).X) :
    x ≫ (vectorProjection R c b).hom.hom = 1 ↔ (pointsEquiv R c T x).vec = 0 := by
  constructor
  · intro hx
    funext j
    obtain ⟨i, rfl⟩ := b.surjective j
    have h := coordinates_vectorProjection R c b x i
    rw [hx, map_one] at h
    exact h.symm
  · intro hx
    apply VectorGroup.points_ext
    intro i
    rw [coordinates_vectorProjection, hx, map_one]
    rfl

/-- The pointwise projection kernel is the scalar additive coordinate. -/
def vectorProjectionKernelPointEquiv (T : Over (Spec R)) :
    (((yonedaGrp.map (vectorProjection R c b)).app (op T)).hom.ker) ≃*
      Multiplicative Γ(T.left, ⊤) where
  toFun x := Multiplicative.ofAdd (pointsEquiv R c T x.val).scalar
  invFun y := ⟨(pointsEquiv R c T).symm ⟨0, y.toAdd⟩, by
    change (pointsEquiv R c T).symm _ ≫ (vectorProjection R c b).hom.hom = 1
    rw [vectorProjection_eq_one_iff, MulEquiv.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply (pointsEquiv R c T).injective
    rw [MulEquiv.apply_symm_apply]
    apply Coordinates.ext
    · exact ((vectorProjection_eq_one_iff R c b x.val).mp x.property).symm
    · rfl
  right_inv y := by
    change Multiplicative.ofAdd (pointsEquiv R c T ((pointsEquiv R c T).symm _)).scalar = y
    rw [MulEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (pointsEquiv R c T (x.val * y.val)).scalar = _
    rw [map_mul]
    change Multiplicative.ofAdd
      ((pointsEquiv R c T x.val).scalar + (pointsEquiv R c T y.val).scalar +
        form _ (pointsEquiv R c T x.val).vec (pointsEquiv R c T y.val).vec) = _
    rw [(vectorProjection_eq_one_iff R c b x.val).mp x.property, form_zero_left, add_zero]
    rfl

/-- Scalar coordinates on the actual scheme-theoretic projection kernel. -/
def vectorProjectionKernelCoordinates (T : Over (Spec R)) :
    (T ⟶ (kernel (vectorProjection R c b)).X) ≃* Multiplicative Γ(T.left, ⊤) :=
  (kernelPointsEquiv (vectorProjection R c b) T).trans
    (vectorProjectionKernelPointEquiv R c b T)

theorem vectorProjectionKernelCoordinates_naturality
    {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (kernel (vectorProjection R c b)).X) :
    (vectorProjectionKernelCoordinates R c b T' (a ≫ x)).toAdd =
      a.left.appTop (vectorProjectionKernelCoordinates R c b T x).toAdd := by
  change (pointsEquiv R c T' ((a ≫ x) ≫ (kernelι (vectorProjection R c b)).hom.hom)).scalar =
    a.left.appTop (pointsEquiv R c T (x ≫ (kernelι (vectorProjection R c b)).hom.hom)).scalar
  rw [Category.assoc, pointsEquiv_naturality]
  rfl

/-- An additive coordinate is a one-dimensional vector coordinate. -/
def scalarVectorEquiv (S : Type u) [AddCommGroup S] :
    Multiplicative S ≃* Multiplicative (Fin 1 → S) where
  toFun x := Multiplicative.ofAdd (fun _ => x.toAdd)
  invFun y := Multiplicative.ofAdd (y.toAdd 0)
  left_inv _ := rfl
  right_inv y := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg y.toAdd (Subsingleton.elim 0 i)
  map_mul' _ _ := rfl

variable (k : Type u) [Field k] {I : Type u} [Fintype I]
  (c : I → I → k) {n : ℕ} (b : Fin n ≃ I)

theorem vectorProjectionKernel_isVectorGroup :
    RelativeRoot.IsVectorGroupOfDimension
      (kernel (vectorProjection (CommRingCat.of k) c b)) 1 := by
  refine ⟨fun T => (vectorProjectionKernelCoordinates (CommRingCat.of k) c b T).trans
    (scalarVectorEquiv _), ?_⟩
  intro T T' a x
  funext i
  change (vectorProjectionKernelCoordinates (CommRingCat.of k) c b T' (a ≫ x)).toAdd =
    a.left.appTop (vectorProjectionKernelCoordinates (CommRingCat.of k) c b T x).toAdd
  exact vectorProjectionKernelCoordinates_naturality (CommRingCat.of k) c b a x

/-- Every finite-dimensional bilinear coordinate group over a field is unipotent. -/
theorem isUnipotent : IsUnipotent (groupScheme (CommRingCat.of k) c) := by
  let b := (Fintype.equivFin I).symm
  let : IsAffineHom (groupScheme (CommRingCat.of k) c).X.hom :=
    BilinearCoordinate.isAffineHom (CommRingCat.of k) c
  let q := vectorProjection (CommRingCat.of k) c b
  let : IsAffineHom q.hom.hom.left := isAffineHom_vectorProjection (CommRingCat.of k) c b
  let : Flat q.hom.hom.left := flat_vectorProjection (CommRingCat.of k) c b
  let : Surjective q.hom.hom.left := surjective_vectorProjection (CommRingCat.of k) c b
  let : IsAffineHom (kernel q).X.hom :=
    (vectorProjectionKernel_isVectorGroup k c b).isAffineHom
  exact isUnipotent_of_kernel_of_quotient q
    (vectorProjectionKernel_isVectorGroup k c b).isUnipotent
    (VectorGroup.isUnipotent k _)

end Langlands.GroupScheme.BilinearCoordinate
