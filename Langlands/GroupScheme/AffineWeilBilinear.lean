import Langlands.GroupScheme.AffineWeilVector
import Langlands.GroupScheme.BilinearCoordinateGroup
import Langlands.GroupScheme.Reductive.UnipotentExtension

/-! # Finite free restriction of bilinear coordinate groups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeilBilinear

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {I : Type u} [Fintype I] (c : I → I → B)
  {n : ℕ} (b : Module.Basis (Fin n) A B)

/-- The original group functor on tensor-extended test algebras. -/
abbrev functor :=
  AffineWeil.pointFunctor A B (BilinearCoordinate.groupScheme (CommRingCat.of B) c)

/-- Tensor-valued bilinear coordinates, with their original group law. -/
def affineCoordinates (T : CommAlgCat.{u} (CommRingCat.of A)) :
    (functor A B c).obj T ≃*
      BilinearCoordinate.Coordinates
        (BilinearCoordinate.algebraCoefficients (CommRingCat.of B) c
          (B ⊗[A] T)) :=
  Corepresented.affinePointsEquiv (BilinearCoordinate.functor (CommRingCat.of B) c)
    (BilinearCoordinate.corepresentableBy (CommRingCat.of B) c)
    ((AffineWeil.tensorFunctor A B).obj T)

theorem affineCoordinates_naturality
    {T T' : CommAlgCat.{u} (CommRingCat.of A)} (f : T ⟶ T')
    (x : (functor A B c).obj T) :
    affineCoordinates A B c T' ((functor A B c).map f x) =
      BilinearCoordinate.Coordinates.map
        (Algebra.TensorProduct.lTensor (S := B) B f.hom).toRingHom
        (fun i j => (Algebra.TensorProduct.lTensor (S := B) B f.hom).commutes (c i j))
        (affineCoordinates A B c T x) := by
  change Corepresented.affinePointsEquiv
    (BilinearCoordinate.functor (CommRingCat.of B) c)
    (BilinearCoordinate.corepresentableBy (CommRingCat.of B) c)
    ((AffineWeil.tensorFunctor A B).obj T')
    ((algSpec (CommRingCat.of B)).map ((AffineWeil.tensorFunctor A B).map f).op ≫ x) = _
  exact Corepresented.affinePointsEquiv_naturality _ _ _ _

/-- The variables are the basis components of the vector and central entries. -/
abbrev Variables := (I × Fin n) ⊕ Fin n

/-- Basis components give set coordinates without altering the group law. -/
def basisCoordinateEquiv (T : CommAlgCat.{u} (CommRingCat.of A)) :
    (Variables (I := I) (n := n) → T) ≃
      BilinearCoordinate.Coordinates
        (BilinearCoordinate.algebraCoefficients (CommRingCat.of B) c (B ⊗[A] T)) where
  toFun x := ⟨fun i => AffineWeil.tensorCoordinateEquiv b T (fun j => x (.inl (i, j))),
    AffineWeil.tensorCoordinateEquiv b T (fun j => x (.inr j))⟩
  invFun x := Sum.elim
    (fun ij => (AffineWeil.tensorCoordinateEquiv b T).symm (x.vec ij.1) ij.2)
    (fun j => (AffineWeil.tensorCoordinateEquiv b T).symm x.scalar j)
  left_inv x := by
    funext v
    cases v <;> simp
  right_inv x := by
    apply BilinearCoordinate.Coordinates.ext <;> simp

theorem basisCoordinateEquiv_naturality
    {T T' : CommAlgCat.{u} (CommRingCat.of A)} (f : T ⟶ T')
    (x : Variables (I := I) (n := n) → T) :
    basisCoordinateEquiv A B c b T' (fun v => f.hom (x v)) =
      BilinearCoordinate.Coordinates.map
        (Algebra.TensorProduct.lTensor (S := B) B f.hom).toRingHom
        (fun i j => (Algebra.TensorProduct.lTensor (S := B) B f.hom).commutes (c i j))
        (basisCoordinateEquiv A B c b T x) := by
  apply BilinearCoordinate.Coordinates.ext
  · funext i
    exact (AffineWeil.lTensor_tensorCoordinateEquiv b f.hom _).symm
  · exact (AffineWeil.lTensor_tensorCoordinateEquiv b f.hom _).symm

/-- An explicit polynomial algebra for the same actual restriction functor. -/
abbrev polynomialAlgebra : CommAlgCat.{u} (CommRingCat.of A) :=
  CommAlgCat.of (CommRingCat.of A) (MvPolynomial (Variables (I := I) (n := n)) A)

/-- A polynomial algebra map is determined by its values on the variables. -/
def polynomialHomEquiv (T : CommAlgCat.{u} (CommRingCat.of A)) :
    (polynomialAlgebra A (I := I) (n := n) ⟶ T) ≃
      (Variables (I := I) (n := n) → T) where
  toFun f v := f.hom (X v)
  invFun x := CommAlgCat.ofHom (aeval x)
  left_inv _ := CommAlgCat.hom_ext (algHom_ext fun v => aeval_X _ v)
  right_inv _ := funext fun v => aeval_X _ v

/-- The explicit polynomial algebra corepresents the original tensor-valued point groups. -/
def corepresentableBy :
    (functor A B c ⋙ forget GrpCat).CorepresentableBy
      (polynomialAlgebra A (I := I) (n := n)) where
  homEquiv := fun {T} => (polynomialHomEquiv A T).trans
    ((basisCoordinateEquiv A B c b T).trans (affineCoordinates A B c T).toEquiv.symm)
  homEquiv_comp := by
    intro T T' f g
    apply (affineCoordinates A B c T').injective
    change affineCoordinates A B c T'
      ((affineCoordinates A B c T').symm
        (basisCoordinateEquiv A B c b T' (fun v => (g ≫ f).hom (X v)))) =
      affineCoordinates A B c T' ((functor A B c).map f
        ((affineCoordinates A B c T).symm
          (basisCoordinateEquiv A B c b T (fun v => g.hom (X v)))))
    rw [MulEquiv.apply_symm_apply, affineCoordinates_naturality,
      MulEquiv.apply_symm_apply]
    exact basisCoordinateEquiv_naturality A B c b f _

theorem homEquiv_symm_X {T : CommAlgCat.{u} (CommRingCat.of A)}
    (x : (functor A B c).obj T) (v : Variables (I := I) (n := n)) :
    ((corepresentableBy A B c b).homEquiv.symm x).hom (X v) =
      (basisCoordinateEquiv A B c b T).symm (affineCoordinates A B c T x) v := by
  change aeval ((basisCoordinateEquiv A B c b T).symm
    (affineCoordinates A B c T x)) (X v) = _
  exact aeval_X _ v

/-- The polynomial corepresentation carries exactly the original group laws. -/
abbrev polynomialGroupScheme : GroupScheme (Spec (CommRingCat.of A)) :=
  Corepresented.groupScheme (functor A B c) (corepresentableBy A B c b)

instance polynomial_isAffineHom :
    IsAffineHom (polynomialGroupScheme A B c b).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom
    (algebraMap A (MvPolynomial (Variables (I := I) (n := n)) A))))
  infer_instance

instance polynomial_smooth : Smooth (polynomialGroupScheme A B c b).X.hom := by
  rw [Corepresented.smooth_groupScheme_iff]
  infer_instance

instance polynomial_geometricallyConnected :
    GeometricallyConnected (polynomialGroupScheme A B c b).X.hom :=
  BilinearCoordinate.geometricallyConnected_spec_mvPolynomial
    (CommRingCat.of A) (Variables (I := I) (n := n))

/-- The natural base algebra on the global functions of a relative scheme. -/
abbrev sectionsAlgebra (T : Over (Spec (CommRingCat.of A))) :
    CommAlgCat.{u} (CommRingCat.of A) :=
  ((algΓ (CommRingCat.of A)).obj T).unop

instance polynomial_isAffine : IsAffine (polynomialGroupScheme A B c b).X.left := by
  change IsAffine (Spec (CommRingCat.of
    (MvPolynomial (Variables (I := I) (n := n)) A)))
  infer_instance

/-- Tensor-valued coordinates on every scheme test of the polynomial model. -/
def coordinates (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (polynomialGroupScheme A B c b).X) ≃*
      BilinearCoordinate.Coordinates
        (BilinearCoordinate.algebraCoefficients (CommRingCat.of B) c
          (B ⊗[A] sectionsAlgebra A T)) :=
  (Corepresented.pointsEquiv (functor A B c) (corepresentableBy A B c b) T).trans
    (affineCoordinates A B c (((algΓ (CommRingCat.of A)).obj T).unop))

theorem coordinates_naturality {T T' : Over (Spec (CommRingCat.of A))}
    (a : T' ⟶ T) (x : T ⟶ (polynomialGroupScheme A B c b).X) :
    coordinates A B c b T' (a ≫ x) =
      BilinearCoordinate.Coordinates.map
        (Algebra.TensorProduct.lTensor (S := B) B
          (((algΓ (CommRingCat.of A)).map a).unop.hom)).toRingHom
        (fun i j => (Algebra.TensorProduct.lTensor (S := B) B
          (((algΓ (CommRingCat.of A)).map a).unop.hom)).commutes (c i j))
        (coordinates A B c b T x) := by
  dsimp only [coordinates, MulEquiv.trans_apply]
  rw [Corepresented.pointsEquiv_naturality]
  exact affineCoordinates_naturality A B c _ _

variable {m : ℕ} (v : Fin m ≃ I × Fin n)

local instance vector_isAffine : IsAffine (VectorGroup.groupScheme (CommRingCat.of A) m).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin m) A)))
  infer_instance

/-- Every vector basis component is primitive in the original bilinear group law. -/
theorem vectorPrimitive :
    VectorGroup.IsPrimitiveFamily (corepresentableBy A B c b)
      (fun i => (X (.inl (v i)) :
        MvPolynomial (Variables (I := I) (n := n)) A)) := by
  intro T x y i
  rw [homEquiv_symm_X, homEquiv_symm_X, homEquiv_symm_X]
  change (AffineWeil.tensorCoordinateEquiv b T).symm
    ((affineCoordinates A B c T (x * y)).vec (v i).1) (v i).2 = _
  rw [map_mul, BilinearCoordinate.Coordinates.vec_mul, Pi.add_apply, map_add]
  rfl

/-- Projection to all basis components of the vector entries. -/
def vectorProjection :
    polynomialGroupScheme A B c b ⟶ VectorGroup.groupScheme (CommRingCat.of A) m :=
  VectorGroup.quotientMap (vectorPrimitive A B c b v)

theorem coordinates_vectorProjection {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ (polynomialGroupScheme A B c b).X) (i : Fin m) :
    (VectorGroup.coordinates (CommRingCat.of A) m T
      (x ≫ (vectorProjection A B c b v).hom.hom)).toAdd i =
      (AffineWeil.tensorCoordinateEquiv b (sectionsAlgebra A T)).symm
        ((coordinates A B c b T x).vec (v i).1) (v i).2 := by
  rw [vectorProjection, VectorGroup.coordinates_quotientMap, homEquiv_symm_X]
  rfl

/-- Vector and central variables together exhaust the polynomial variables. -/
def vectorScalarVariableEquiv : Fin m ⊕ ULift.{u} (Fin n) ≃
    Variables (I := I) (n := n) :=
  Equiv.sumCongr v Equiv.ulift

omit [Fintype I] in
theorem vectorScalarGenerators :
    Function.Bijective
      (aeval (Sum.elim (fun i => X (.inl (v i)))
        (fun j : ULift.{u} (Fin n) => X (.inr j.down))) :
        MvPolynomial (Fin m ⊕ ULift.{u} (Fin n)) A →ₐ[A]
          MvPolynomial (Variables (I := I) (n := n)) A) := by
  have he :
      (aeval (Sum.elim (fun i => X (.inl (v i)))
        (fun j : ULift.{u} (Fin n) => X (.inr j.down))) :
        MvPolynomial (Fin m ⊕ ULift.{u} (Fin n)) A →ₐ[A]
          MvPolynomial (Variables (I := I) (n := n)) A) =
      (renameEquiv A (vectorScalarVariableEquiv v)).toAlgHom := by
    apply algHom_ext
    intro z
    cases z <;> simp [vectorScalarVariableEquiv]
  rw [he]
  exact (renameEquiv A (vectorScalarVariableEquiv v)).bijective

theorem isAffineHom_vectorProjection :
    IsAffineHom (vectorProjection A B c b v).hom.hom.left := by
  rw [vectorProjection, VectorGroup.quotientMap_left]
  exact isAffineHom_of_isAffine _

theorem flat_vectorProjection :
    Flat (vectorProjection A B c b v).hom.hom.left :=
  VectorGroup.flat_quotientMap (vectorPrimitive A B c b v) (vectorScalarGenerators A v)

theorem surjective_vectorProjection :
    Surjective (vectorProjection A B c b v).hom.hom.left :=
  VectorGroup.surjective_quotientMap (vectorPrimitive A B c b v) (vectorScalarGenerators A v)

theorem vectorProjection_eq_one_iff {T : Over (Spec (CommRingCat.of A))}
    (x : T ⟶ (polynomialGroupScheme A B c b).X) :
    x ≫ (vectorProjection A B c b v).hom.hom = 1 ↔
      (coordinates A B c b T x).vec = 0 := by
  constructor
  · intro hx
    funext j
    apply (AffineWeil.tensorCoordinateEquiv b (sectionsAlgebra A T)).symm.injective
    funext k
    obtain ⟨i, hi⟩ := v.surjective (j, k)
    have h := coordinates_vectorProjection A B c b v x i
    rw [hx, map_one, hi] at h
    simpa using h.symm
  · intro hx
    apply VectorGroup.points_ext
    intro i
    rw [coordinates_vectorProjection, hx, map_one]
    simp

/-- The pointwise projection kernel has just the central tensor coordinate. -/
def vectorProjectionKernelPointEquiv (T : Over (Spec (CommRingCat.of A))) :
    (((yonedaGrp.map (vectorProjection A B c b v)).app (op T)).hom.ker) ≃*
      Multiplicative (B ⊗[A] sectionsAlgebra A T) where
  toFun x := Multiplicative.ofAdd (coordinates A B c b T x.val).scalar
  invFun y := ⟨(coordinates A B c b T).symm ⟨0, y.toAdd⟩, by
    change (coordinates A B c b T).symm _ ≫ (vectorProjection A B c b v).hom.hom = 1
    rw [vectorProjection_eq_one_iff, MulEquiv.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply (coordinates A B c b T).injective
    rw [MulEquiv.apply_symm_apply]
    apply BilinearCoordinate.Coordinates.ext
    · exact ((vectorProjection_eq_one_iff A B c b v x.val).mp x.property).symm
    · rfl
  right_inv y := by
    change Multiplicative.ofAdd
      (coordinates A B c b T ((coordinates A B c b T).symm _)).scalar = y
    rw [MulEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (coordinates A B c b T (x.val * y.val)).scalar = _
    rw [map_mul]
    change Multiplicative.ofAdd
      ((coordinates A B c b T x.val).scalar + (coordinates A B c b T y.val).scalar +
        BilinearCoordinate.form _ (coordinates A B c b T x.val).vec
          (coordinates A B c b T y.val).vec) = _
    rw [(vectorProjection_eq_one_iff A B c b v x.val).mp x.property,
      BilinearCoordinate.form_zero_left, add_zero]
    rfl

/-- Basis components of the central tensor entry are actual kernel coordinates. -/
def vectorProjectionKernelCoordinates (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (kernel (vectorProjection A B c b v)).X) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)) :=
  ((kernelPointsEquiv (vectorProjection A B c b v) T).trans
    (vectorProjectionKernelPointEquiv A B c b v T)).trans
      (AffineWeil.tensorCoordinateEquiv b (sectionsAlgebra A T)).symm.toMultiplicative

set_option maxRecDepth 2048 in
theorem vectorProjectionKernelCoordinates_naturality
    {T T' : Over (Spec (CommRingCat.of A))} (a : T' ⟶ T)
    (x : T ⟶ (kernel (vectorProjection A B c b v)).X) :
    (vectorProjectionKernelCoordinates A B c b v T' (a ≫ x)).toAdd =
      fun j => a.left.appTop
        ((vectorProjectionKernelCoordinates A B c b v T x).toAdd j) := by
  change (AffineWeil.tensorCoordinateEquiv b (sectionsAlgebra A T')).symm
    (coordinates A B c b T'
      ((a ≫ x) ≫ (kernelι (vectorProjection A B c b v)).hom.hom)).scalar = _
  rw [Category.assoc, coordinates_naturality]
  exact AffineWeil.tensorCoordinateEquiv_symm_lTensor b
    (((algΓ (CommRingCat.of A)).map a).unop.hom) _

theorem vectorProjectionKernel_isVectorGroup :
    RelativeRoot.IsVectorGroupOfDimension
      (kernel (vectorProjection A B c b v)) n :=
  ⟨vectorProjectionKernelCoordinates A B c b v,
    fun _ _ a x => vectorProjectionKernelCoordinates_naturality A B c b v a x⟩

section ActualRestriction

variable [Module.Finite A B] [Module.Projective A B]

local instance bilinear_isAffine :
    IsAffine (BilinearCoordinate.groupScheme (CommRingCat.of B) c).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Option I) B)))
  infer_instance

local instance bilinear_locallyOfFiniteType :
    LocallyOfFiniteType (BilinearCoordinate.groupScheme (CommRingCat.of B) c).X.hom := by
  have : Smooth (BilinearCoordinate.groupScheme (CommRingCat.of B) c).X.hom :=
    BilinearCoordinate.smooth (CommRingCat.of B) c
  infer_instance

/-- The polynomial model is isomorphic to the existing actual affine Weil restriction. -/
def restrictionIso :
    AffineWeil.groupScheme A B (BilinearCoordinate.groupScheme (CommRingCat.of B) c) ≅
      polynomialGroupScheme A B c b :=
  isoOfPoints
    (fun T => (Corepresented.pointsEquiv (functor A B c)
      (AffineWeil.corepresentableBy A B
        (BilinearCoordinate.groupScheme (CommRingCat.of B) c)) T).trans
      (Corepresented.pointsEquiv (functor A B c) (corepresentableBy A B c b) T).symm)
    (by
      intro T T' a x
      apply (Corepresented.pointsEquiv (functor A B c) (corepresentableBy A B c b) T').injective
      dsimp only [MulEquiv.trans_apply]
      rw [MulEquiv.apply_symm_apply, Corepresented.pointsEquiv_naturality,
        Corepresented.pointsEquiv_naturality, MulEquiv.apply_symm_apply])

end ActualRestriction

end Langlands.GroupScheme.AffineWeilBilinear

namespace Langlands.GroupScheme.AffineWeilBilinear

variable (k B : Type u) [Field k] [CommRing B] [Algebra k B]
  {I : Type u} [Fintype I] (c : I → I → B)
  {n : ℕ} (b : Module.Basis (Fin n) k B)

/-- Restriction of a bilinear group is an extension of two vector groups. -/
theorem polynomial_isUnipotent :
    IsUnipotent (polynomialGroupScheme k B c b) := by
  let v := (Fintype.equivFin (I × Fin n)).symm
  let q := vectorProjection k B c b v
  let : IsAffineHom q.hom.hom.left := isAffineHom_vectorProjection k B c b v
  let : Flat q.hom.hom.left := flat_vectorProjection k B c b v
  let : Surjective q.hom.hom.left := surjective_vectorProjection k B c b v
  let : IsAffineHom (kernel q).X.hom :=
    (vectorProjectionKernel_isVectorGroup k B c b v).isAffineHom
  exact isUnipotent_of_kernel_of_quotient q
    (vectorProjectionKernel_isVectorGroup k B c b v).isUnipotent
    (VectorGroup.isUnipotent k _)

/-- The polynomial model has the three required geometric properties over a field. -/
theorem polynomial_properties :
    Smooth (polynomialGroupScheme k B c b).X.hom ∧
      ConnectedSpace (polynomialGroupScheme k B c b).X.left ∧
        IsUnipotent (polynomialGroupScheme k B c b) := by
  refine ⟨inferInstance, ?_, polynomial_isUnipotent k B c b⟩
  change ConnectedSpace (Spec (CommRingCat.of
    (MvPolynomial (Variables (I := I) (n := n)) k)))
  infer_instance

variable [Module.Finite k B] [Module.Projective k B]

attribute [local instance] bilinear_isAffine bilinear_locallyOfFiniteType

include b in
/-- The actual affine Weil restriction is smooth, connected and unipotent.
No separability or reducedness hypothesis on the finite algebra is imposed. -/
theorem properties :
    Smooth (AffineWeil.groupScheme k B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.hom ∧
      ConnectedSpace (AffineWeil.groupScheme k B
        (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.left ∧
        IsUnipotent (AffineWeil.groupScheme k B
          (BilinearCoordinate.groupScheme (CommRingCat.of B) c)) :=
  smooth_connected_unipotent_of_groupIso (restrictionIso k B c b)
    (polynomial_properties k B c b)

end Langlands.GroupScheme.AffineWeilBilinear
