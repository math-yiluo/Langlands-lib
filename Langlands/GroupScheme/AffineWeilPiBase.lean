import Langlands.GroupScheme.AffineWeilEmbeddingProductComparison
import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.ProductProperties

/-! # Weil restriction from a finite product of copies of the base ring -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineWeil.PiBase

variable (A : Type u) [CommRing A] (I : Type u) [Finite I]

/-- Evaluation at a component of the product algebra. -/
def evaluation (i : I) : (I → A) →ₐ[A] A :=
  Pi.evalAlgHom A (fun _ : I => A) i

/-- The original test ring, with product-base action through one evaluation. -/
abbrev coefficientAlgebra (R : CommAlgCat.{u} (CommRingCat.of A)) (i : I) :
    CommAlgCat.{u} (CommRingCat.of (I → A)) :=
  embeddingCoefficientAlgebra A (I → A) A R (evaluation A I i)

/-- The corresponding actual base-change factor of a group over the product base. -/
abbrev factor (H : GroupScheme (Spec (CommRingCat.of (I → A)))) (i : I) :
    GroupScheme (Spec (CommRingCat.of A)) :=
  (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (evaluation A I i).toRingHom))).obj H

/-- The tensor-product splitting, with the original product-base action retained. -/
def tensorAlgEquiv (R : CommAlgCat.{u} (CommRingCat.of A)) :
    (I → A) ⊗[A] R ≃ₐ[I → A] (∀ i, coefficientAlgebra A I R i) where
  __ := (WeilGm.piTensorEquiv (CommRingCat.of A) I R).toRingEquiv
  commutes' b := by
    funext i
    change b i • (1 : R) = algebraMap A R (b i)
    rw [Algebra.smul_def, mul_one]

/-- Each tensor coordinate is an actual homomorphism of product-base algebras. -/
def evaluationMap (R : CommAlgCat.{u} (CommRingCat.of A)) (i : I) :
    CommAlgCat.of (I → A) ((I → A) ⊗[A] R) ⟶ coefficientAlgebra A I R i :=
  CommAlgCat.ofHom (Y := coefficientAlgebra A I R i)
    ((Pi.evalAlgHom (I → A) (fun i => coefficientAlgebra A I R i) i).comp
      (tensorAlgEquiv A I R).toAlgHom)

/-- Tensor evaluation commutes with every change of coefficient algebra. -/
theorem evaluationMap_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of A)} (a : R ⟶ R') (i : I) :
    CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := I → A) (I → A) a.hom) ≫
        evaluationMap A I R' i =
      evaluationMap A I R i ≫
        embeddingCoefficientMap A (I → A) A a (evaluation A I i) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact congrFun (WeilGm.piTensorEquiv_natural (CommRingCat.of A) I a.hom x) i

variable (H : GroupScheme (Spec (CommRingCat.of (I → A)))) [IsAffine H.X.left]

instance (i : I) : IsAffine (factor A I H i).X.left :=
  inferInstanceAs (IsAffine (pullback H.X.hom
    (Spec.map (CommRingCat.ofHom (evaluation A I i).toRingHom))))

/-- Actual tensor-valued points are families of points with their component scalar actions. -/
def tensorPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of A)) :
    H.affinePoints (CommAlgCat.of (I → A) ((I → A) ⊗[A] R)) ≃*
      (∀ i, H.affinePoints (coefficientAlgebra A I R i)) :=
  (H.affinePointFunctor.mapIso (CommAlgCat.isoMk (tensorAlgEquiv A I R))).groupIsoToMulEquiv.trans
    (H.affinePointsPiEquiv (coefficientAlgebra A I R))

/-- Each coordinate is precisely the original tensor point pulled back along evaluation. -/
theorem tensorPointsEquiv_apply (R : CommAlgCat.{u} (CommRingCat.of A))
    (x : H.affinePoints (CommAlgCat.of (I → A) ((I → A) ⊗[A] R))) (i : I) :
    tensorPointsEquiv A I H R x i = H.affinePointMap (evaluationMap A I R i) x := by
  change H.affinePointMap _ (H.affinePointMap _ x) = _
  rw [← MonoidHom.comp_apply, ← affinePointMap_comp]
  rfl

/-- Naturality of the multiplicative tensor decomposition. -/
theorem tensorPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of A)} (a : R ⟶ R')
    (x : H.affinePoints (CommAlgCat.of (I → A) ((I → A) ⊗[A] R))) (i : I) :
    tensorPointsEquiv A I H R'
        (H.affinePointMap (CommAlgCat.ofHom
          (Algebra.TensorProduct.lTensor (S := I → A) (I → A) a.hom)) x) i =
      H.affinePointMap (embeddingCoefficientMap A (I → A) A a (evaluation A I i))
        (tensorPointsEquiv A I H R x i) := by
  rw [tensorPointsEquiv_apply, tensorPointsEquiv_apply,
    ← MonoidHom.comp_apply, ← affinePointMap_comp,
    evaluationMap_naturality, affinePointMap_comp]
  rfl

/-- The original factor point is the tensor-coordinate point with its actual scalar action. -/
abbrev factorPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of A)) (i : I) :
    (factor A I H i).affinePoints R ≃* H.affinePoints (coefficientAlgebra A I R i) :=
  embeddingFactorPointsEquiv A (I → A) A H R (evaluation A I i)

omit [Finite I] [IsAffine H.X.left] in
/-- The factor-point comparison respects every coefficient homomorphism. -/
theorem factorPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of A)} (a : R ⟶ R') (i : I)
    (x : (factor A I H i).affinePoints R) :
    factorPointsEquiv A I H R' i ((factor A I H i).affinePointMap a x) =
      H.affinePointMap (embeddingCoefficientMap A (I → A) A a (evaluation A I i))
        (factorPointsEquiv A I H R i x) :=
  embeddingFactorPointsEquiv_naturality A (I → A) A H a (evaluation A I i) x

variable [LocallyOfFiniteType H.X.hom]

instance : IsAffine (GroupScheme.pi (factor A I H)).X.left := by
  have : IsAffineHom (GroupScheme.pi (factor A I H)).X.hom :=
    prop_pi_hom @IsAffineHom (factor A I H) (fun _ => inferInstance)
  exact isAffine_of_isAffineHom (GroupScheme.pi (factor A I H)).X.hom

/-- Multiplicative splitting of the actual Weil restriction on every affine test. -/
def pointsEquiv (R : CommAlgCat.{u} (CommRingCat.of A)) :
    (AffineWeil.groupScheme A (I → A) H).affinePoints R ≃*
      (GroupScheme.pi (factor A I H)).affinePoints R :=
  (AffineWeil.pointsEquiv A (I → A) H R).trans <|
    (tensorPointsEquiv A I H R).trans <|
      (MulEquiv.piCongrRight (fun i => (factorPointsEquiv A I H R i).symm)).trans
        (piPointsEquiv (factor A I H) ((algSpec (CommRingCat.of A)).obj (op R))).symm

/-- Projection to each factor is the actual tensor-point evaluation. -/
theorem pointsEquiv_component (R : CommAlgCat.{u} (CommRingCat.of A))
    (x : (AffineWeil.groupScheme A (I → A) H).affinePoints R) (i : I) :
    factorPointsEquiv A I H R i
        (piPointsEquiv (factor A I H) ((algSpec (CommRingCat.of A)).obj (op R))
          (pointsEquiv A I H R x) i) =
      tensorPointsEquiv A I H R (AffineWeil.pointsEquiv A (I → A) H R x) i := by
  simp only [pointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    MulEquiv.piCongrRight_apply]
  rfl

/-- The splitting is natural in every coefficient-algebra homomorphism. -/
theorem pointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of A)} (a : R ⟶ R')
    (x : (AffineWeil.groupScheme A (I → A) H).affinePoints R) :
    pointsEquiv A I H R'
        ((AffineWeil.groupScheme A (I → A) H).affinePointMap a x) =
      (GroupScheme.pi (factor A I H)).affinePointMap a (pointsEquiv A I H R x) := by
  apply (piPointsEquiv (factor A I H) ((algSpec (CommRingCat.of A)).obj (op R'))).injective
  funext i
  apply (factorPointsEquiv A I H R' i).injective
  rw [pointsEquiv_component]
  have ht := congrFun (piPointsEquiv_naturality (factor A I H)
    ((algSpec (CommRingCat.of A)).map a.op) (pointsEquiv A I H R x)) i
  change piPointsEquiv (factor A I H) ((algSpec (CommRingCat.of A)).obj (op R'))
      ((GroupScheme.pi (factor A I H)).affinePointMap a (pointsEquiv A I H R x)) i =
    (factor A I H i).affinePointMap a
      (piPointsEquiv (factor A I H) ((algSpec (CommRingCat.of A)).obj (op R))
        (pointsEquiv A I H R x) i) at ht
  rw [ht]
  rw [factorPointsEquiv_naturality, pointsEquiv_component]
  have hw := AffineWeil.pointsEquiv_naturality A (I → A) H a.hom x
  simp only [CommAlgCat.ofHom_hom] at hw
  rw [hw, tensorPointsEquiv_naturality]

/-- The original affine group-valued point functors are naturally isomorphic. -/
def affinePointIso :
    (AffineWeil.groupScheme A (I → A) H).affinePointFunctor ≅
      (GroupScheme.pi (factor A I H)).affinePointFunctor :=
  NatIso.ofComponents (fun R => (pointsEquiv A I H R).toGrpIso) (by
    intro R R' a
    ext x
    exact pointsEquiv_naturality A I H a x)

/-- Actual Weil restriction from a finite split product base is the product of
the actual evaluation pullbacks. -/
def iso : AffineWeil.groupScheme A (I → A) H ≅ GroupScheme.pi (factor A I H) :=
  AffinePointComparison.iso (affinePointIso A I H)

end Langlands.GroupScheme.AffineWeil.PiBase
