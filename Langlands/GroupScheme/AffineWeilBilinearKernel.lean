import Langlands.GroupScheme.AffineWeilBilinear
import Langlands.GroupScheme.PolynomialLinearKernel

/-! # Linear kernels in finite free restrictions of bilinear groups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.AffineWeil

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} (b : Module.Basis (Fin n) A B)

/-- Multiplication by a coefficient, in the chosen basis of the finite algebra. -/
def multiplicationMatrix (z : B) : Matrix (Fin n) (Fin n) A :=
  fun j l => b.repr (z * b l) j

theorem tensorCoordinateEquiv_mul
    (T : Type u) [CommRing T] [Algebra A T] (z : B) (x : Fin n → T) :
    tensorCoordinateEquiv b T
        ((multiplicationMatrix b z).map (algebraMap A T) *ᵥ x) =
      algebraMap B (B ⊗[A] T) z * tensorCoordinateEquiv b T x := by
  classical
  rw [tensorCoordinateEquiv_apply, tensorCoordinateEquiv_apply,
    Finset.mul_sum]
  change (∑ j, b j ⊗ₜ[A]
      (∑ l, algebraMap A T (b.repr (z * b l) j) * x l)) =
    ∑ l, (z ⊗ₜ[A] (1 : T)) * (b l ⊗ₜ[A] x l)
  simp only [TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  conv_rhs => rw [← b.sum_repr (z * b l), TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro j _
  rw [TensorProduct.smul_tmul, Algebra.smul_def]

theorem tensorCoordinateEquiv_symm_mul
    (T : Type u) [CommRing T] [Algebra A T] (z : B) (x : B ⊗[A] T) :
    (tensorCoordinateEquiv b T).symm (algebraMap B (B ⊗[A] T) z * x) =
      (multiplicationMatrix b z).map (algebraMap A T) *ᵥ
        (tensorCoordinateEquiv b T).symm x := by
  apply (tensorCoordinateEquiv b T).injective
  rw [AddEquiv.apply_symm_apply, tensorCoordinateEquiv_mul,
    AddEquiv.apply_symm_apply]

end Langlands.GroupScheme.AffineWeil

namespace Langlands.GroupScheme.AffineWeilBilinear

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {I J : Type u} [Fintype I] [Fintype J]
  (c : I → I → B) (d : J → J → B)
  {n : ℕ} (b : Module.Basis (Fin n) A B)

attribute [local instance] bilinear_isAffine bilinear_locallyOfFiniteType

/-- Tensor coordinates on every test scheme of the actual affine restriction. -/
def restrictionCoordinates (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X) ≃*
      BilinearCoordinate.Coordinates
        (BilinearCoordinate.algebraCoefficients (CommRingCat.of B) c
          (B ⊗[A] sectionsAlgebra A T)) :=
  (Corepresented.pointsEquiv (functor A B c)
    (AffineWeil.corepresentableBy A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)) T).trans
    (affineCoordinates A B c (sectionsAlgebra A T))

theorem restrictionCoordinates_naturality
    {T T' : Over (Spec (CommRingCat.of A))} (a : T' ⟶ T)
    (x : T ⟶ (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X) :
    restrictionCoordinates A B c T' (a ≫ x) =
      BilinearCoordinate.Coordinates.map
        (Algebra.TensorProduct.lTensor (S := B) B
          (((algΓ (CommRingCat.of A)).map a).unop.hom)).toRingHom
        (fun i j => (Algebra.TensorProduct.lTensor (S := B) B
          (((algΓ (CommRingCat.of A)).map a).unop.hom)).commutes (c i j))
        (restrictionCoordinates A B c T x) := by
  dsimp only [restrictionCoordinates, MulEquiv.trans_apply]
  rw [Corepresented.pointsEquiv_naturality]
  exact affineCoordinates_naturality A B c _ _

/-- Finite set coordinates retain all basis components, including the central entry. -/
def restrictionBasisCoordinates (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X) ≃
      (Variables (I := I) (n := n) → Γ(T.left, ⊤)) :=
  (restrictionCoordinates A B c T).toEquiv.trans
    (basisCoordinateEquiv A B c b (sectionsAlgebra A T)).symm

theorem restrictionBasisCoordinates_naturality
    {T T' : Over (Spec (CommRingCat.of A))} (a : T' ⟶ T)
    (x : T ⟶ (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X) :
    restrictionBasisCoordinates A B c b T' (a ≫ x) =
      fun v => a.left.appTop (restrictionBasisCoordinates A B c b T x v) := by
  change (basisCoordinateEquiv A B c b (sectionsAlgebra A T')).symm
    (restrictionCoordinates A B c T' (a ≫ x)) = _
  rw [restrictionCoordinates_naturality]
  funext v
  cases v with
  | inl ij =>
      exact congrFun (AffineWeil.tensorCoordinateEquiv_symm_lTensor b
        (((algΓ (CommRingCat.of A)).map a).unop.hom)
        ((restrictionCoordinates A B c T x).vec ij.1)) ij.2
  | inr j =>
      exact congrFun (AffineWeil.tensorCoordinateEquiv_symm_lTensor b
        (((algΓ (CommRingCat.of A)).map a).unop.hom)
        (restrictionCoordinates A B c T x).scalar) j

theorem restrictionBasisCoordinates_one (T : Over (Spec (CommRingCat.of A))) :
    restrictionBasisCoordinates A B c b T 1 = 0 := by
  change (basisCoordinateEquiv A B c b (sectionsAlgebra A T)).symm
    (restrictionCoordinates A B c T 1) = 0
  rw [map_one]
  apply (basisCoordinateEquiv A B c b (sectionsAlgebra A T)).injective
  rw [Equiv.apply_symm_apply]
  apply BilinearCoordinate.Coordinates.ext
  · funext i
    exact (map_zero (AffineWeil.tensorCoordinateEquiv b (sectionsAlgebra A T))).symm
  · exact (map_zero (AffineWeil.tensorCoordinateEquiv b (sectionsAlgebra A T))).symm

variable {c d} (M : I → J → B) (t : B) (h : BilinearCoordinate.IsCompatible c d M t)

/-- The original linear homomorphism, expressed in all basis components over the base. -/
def linearMatrix :
    Matrix (Variables (I := J) (n := n)) (Variables (I := I) (n := n)) A :=
  fun w v => match w, v with
    | .inl (j, r), .inl (i, s) => AffineWeil.multiplicationMatrix b (M i j) r s
    | .inr r, .inr s => AffineWeil.multiplicationMatrix b t r s
    | _, _ => 0

omit [Module.Finite A B] [Module.Projective A B] in
theorem basisCoordinateEquiv_linearMap (T : CommAlgCat.{u} (CommRingCat.of A))
    (x : Variables (I := I) (n := n) → T) :
    (basisCoordinateEquiv A B d b T).symm
        (BilinearCoordinate.Coordinates.linearMap
          (fun i j => algebraMap B (B ⊗[A] T) (M i j))
          (algebraMap B (B ⊗[A] T) t) (h.map (algebraMap B (B ⊗[A] T)))
          (basisCoordinateEquiv A B c b T x)) =
      (linearMatrix A B b M t).map (algebraMap A T) *ᵥ x := by
  classical
  funext w
  cases w with
  | inl jr =>
      change (AffineWeil.tensorCoordinateEquiv b T).symm
        (∑ i, AffineWeil.tensorCoordinateEquiv b T (fun s => x (.inl (i, s))) *
          algebraMap B (B ⊗[A] T) (M i jr.1)) jr.2 = _
      simp_rw [mul_comm (AffineWeil.tensorCoordinateEquiv b T _),
        map_sum, Finset.sum_apply, AffineWeil.tensorCoordinateEquiv_symm_mul,
        AddEquiv.symm_apply_apply]
      simp [linearMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  | inr r =>
      change (AffineWeil.tensorCoordinateEquiv b T).symm
        (algebraMap B (B ⊗[A] T) t *
          AffineWeil.tensorCoordinateEquiv b T (fun s => x (.inr s))) r = _
      rw [AffineWeil.tensorCoordinateEquiv_symm_mul, AddEquiv.symm_apply_apply]
      simp [linearMatrix, Matrix.mulVec, dotProduct]

theorem restrictionCoordinates_linearHom
    (T : Over (Spec (CommRingCat.of A)))
    (x : T ⟶ (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X) :
    restrictionCoordinates A B d T
        (x ≫ (AffineWeil.map A B
          (BilinearCoordinate.linearHom (CommRingCat.of B) M t h)).hom.hom) =
      BilinearCoordinate.Coordinates.linearMap
        (fun i j => algebraMap B (B ⊗[A] sectionsAlgebra A T) (M i j))
        (algebraMap B (B ⊗[A] sectionsAlgebra A T) t)
        (h.map (algebraMap B (B ⊗[A] sectionsAlgebra A T)))
        (restrictionCoordinates A B c T x) := by
  dsimp only [restrictionCoordinates, MulEquiv.trans_apply, AffineWeil.map]
  rw [Corepresented.groupSchemeMap_points]
  exact Corepresented.groupSchemeMap_affinePoints
    (BilinearCoordinate.corepresentableBy (CommRingCat.of B) c)
    (BilinearCoordinate.corepresentableBy (CommRingCat.of B) d)
    (BilinearCoordinate.linearNatTrans (CommRingCat.of B) M t h) _

theorem restrictionBasisCoordinates_linearHom
    (T : Over (Spec (CommRingCat.of A)))
    (x : T ⟶ (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X) :
    restrictionBasisCoordinates A B d b T
        (x ≫ (AffineWeil.map A B
          (BilinearCoordinate.linearHom (CommRingCat.of B) M t h)).hom.hom) =
      (linearMatrix A B b M t).map (scalarMap T) *ᵥ
        restrictionBasisCoordinates A B c b T x := by
  change (basisCoordinateEquiv A B d b (sectionsAlgebra A T)).symm
    (restrictionCoordinates A B d T _) =
      (linearMatrix A B b M t).map (algebraMap A (sectionsAlgebra A T)) *ᵥ
        (basisCoordinateEquiv A B c b (sectionsAlgebra A T)).symm
          (restrictionCoordinates A B c T x)
  rw [restrictionCoordinates_linearHom]
  have hf := basisCoordinateEquiv_linearMap A B b M t h (sectionsAlgebra A T)
    ((basisCoordinateEquiv A B c b (sectionsAlgebra A T)).symm
      (restrictionCoordinates A B c T x))
  simpa only [Equiv.apply_symm_apply] using hf

end Langlands.GroupScheme.AffineWeilBilinear

namespace Langlands.GroupScheme.AffineWeilBilinear

variable (k B : Type u) [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B] [Module.Projective k B]
  {I J : Type u} [Fintype I] [Fintype J]
  {c : I → I → B} {d : J → J → B}
  {n : ℕ} (b : Module.Basis (Fin n) k B)
  (M : I → J → B) (t : B) (h : BilinearCoordinate.IsCompatible c d M t)

attribute [local instance] bilinear_isAffine bilinear_locallyOfFiniteType

include b in
/-- The kernel of the actual restricted linear map is smooth, connected and
unipotent over the field, even when the finite coefficient algebra is nonreduced. -/
theorem linearKernel_properties :
    Smooth (kernel (AffineWeil.map k B
      (BilinearCoordinate.linearHom (CommRingCat.of B) M t h))).X.hom ∧
      ConnectedSpace (kernel (AffineWeil.map k B
        (BilinearCoordinate.linearHom (CommRingCat.of B) M t h))).X.left ∧
        IsUnipotent (kernel (AffineWeil.map k B
          (BilinearCoordinate.linearHom (CommRingCat.of B) M t h))) := by
  have hG := properties k B c b
  let : Smooth (AffineWeil.groupScheme k B
    (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.hom := hG.1
  let : ConnectedSpace (AffineWeil.groupScheme k B
    (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.left := hG.2.1
  let : IsAffineHom (AffineWeil.groupScheme k B
    (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.hom :=
      isAffineHom_of_isAffine _
  let : IsAffineHom (AffineWeil.groupScheme k B
    (BilinearCoordinate.groupScheme (CommRingCat.of B) d)).X.hom :=
      isAffineHom_of_isAffine _
  exact PolynomialLinearKernel.properties
    (restrictionBasisCoordinates k B c b)
    (fun {_ _} a x => restrictionBasisCoordinates_naturality k B c b a x)
    (restrictionBasisCoordinates k B d b)
    (restrictionBasisCoordinates_one k B d b)
    (AffineWeil.map k B (BilinearCoordinate.linearHom (CommRingCat.of B) M t h))
    (linearMatrix k B b M t)
    (restrictionBasisCoordinates_linearHom k B b M t h) hG.2.2

end Langlands.GroupScheme.AffineWeilBilinear
