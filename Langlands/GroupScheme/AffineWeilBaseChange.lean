import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.AffineWeilEmbeddingProductComparison
import Langlands.GroupScheme.AffineWeilKernel
import Langlands.GroupScheme.KernelSquareTransport

/-! # Base change of actual affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil.BaseChange

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private theorem inversePoints_target
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H)
    (p : ((GroupScheme.baseChange (Spec.algebraMap R S)).obj G).affinePoints
      (CommAlgCat.of S T)) :
    (affinePointsBaseChangeMulEquiv R S T H).symm
        (p ≫ ((GroupScheme.baseChange (Spec.algebraMap R S)).map f).hom.hom) =
      (affinePointsBaseChangeMulEquiv R S T G).symm p ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  change (p.left ≫ ((Over.pullback (Spec.algebraMap R S)).map f.hom.hom).left) ≫
    pullback.fst H.X.hom (Spec.algebraMap R S) = _
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  change p.left ≫ pullback.fst G.X.hom (Spec.algebraMap R S) ≫ f.hom.hom.left =
    ((affinePointsBaseChangeMulEquiv R S T G).symm p).left ≫ f.hom.hom.left
  rw [affinePointsBaseChangeMulEquiv_symm_left, Category.assoc]

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance testBaseAlgebra (R : CommAlgCat.{u} (CommRingCat.of C)) :
    Algebra A R := Algebra.compHom R (algebraMap A C)

local instance testScalarTower (R : CommAlgCat.{u} (CommRingCat.of C)) :
    IsScalarTower A C R := IsScalarTower.of_algebraMap_eq' rfl

local instance tensorTestTower (R : CommAlgCat.{u} (CommRingCat.of C)) :
    IsScalarTower B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) := by
  infer_instance

/-- Tensor cancellation retains the original B-action, including a nonreduced
base-changed coefficient algebra. -/
def tensorEquiv (R : CommAlgCat.{u} (CommRingCat.of C)) :
    ((C ⊗[A] B) ⊗[C] R) ≃ₐ[B] B ⊗[A] R where
  __ := ((Algebra.TensorProduct.comm C (C ⊗[A] B) R).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange A C R R B).toRingEquiv).trans
      (Algebra.TensorProduct.comm A R B).toRingEquiv
  commutes' b := by
    change
      Algebra.TensorProduct.comm A R B
        (Algebra.TensorProduct.cancelBaseChange A C R R B
          (Algebra.TensorProduct.comm C (C ⊗[A] B) R
            ((1 ⊗ₜ[A] b) ⊗ₜ[C] 1))) = b ⊗ₜ[A] 1
    simp

@[simp] theorem tensorEquiv_tmul (R : CommAlgCat.{u} (CommRingCat.of C))
    (c : C) (b : B) (r : R) :
    tensorEquiv A B C R ((c ⊗ₜ[A] b) ⊗ₜ[C] r) =
      b ⊗ₜ[A] (algebraMap C R c * r) := by
  change
    Algebra.TensorProduct.comm A R B
      (Algebra.TensorProduct.cancelBaseChange A C R R B
        (Algebra.TensorProduct.comm C (C ⊗[A] B) R
          ((c ⊗ₜ[A] b) ⊗ₜ[C] r))) = _
  simp [Algebra.smul_def]

/-- Cancellation commutes with every map of test algebras. -/
theorem tensorEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of C)} (a : R ⟶ R') :
    (tensorEquiv A B C R').toAlgHom.comp
        ((Algebra.TensorProduct.lTensor (S := C ⊗[A] B) (C ⊗[A] B) a.hom).restrictScalars B) =
      (Algebra.TensorProduct.lTensor (S := B) B (a.hom.restrictScalars A)).comp
        (tensorEquiv A B C R).toAlgHom := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all
  | tmul d r =>
    induction d using TensorProduct.inductionOn with
    | tmul c b => simp [a.hom.commutes]
    | add x y hx hy => simp_all [TensorProduct.add_tmul]

variable (G : GroupScheme (Spec (CommRingCat.of B)))

/-- The original group over the base-changed coefficient algebra. -/
abbrev factor : GroupScheme (Spec (CommRingCat.of (C ⊗[A] B))) :=
  (GroupScheme.baseChange (Spec.algebraMap B (C ⊗[A] B))).obj G

instance factor_isAffine [IsAffine G.X.left] : IsAffine (factor A B C G).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap B (C ⊗[A] B)))
  infer_instance

instance factor_locallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (factor A B C G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (Spec.algebraMap B (C ⊗[A] B)))
  infer_instance

/-- Points of the coefficient base change, followed by tensor cancellation. -/
def factorTensorPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of C)) :
    (factor A B C G).affinePoints (CommAlgCat.of (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R)) ≃*
      G.affinePoints (CommAlgCat.of B (B ⊗[A] R)) :=
  (affinePointsBaseChangeMulEquiv B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) G).symm.trans
    (G.affinePointFunctor.mapIso
      (CommAlgCat.isoMk (tensorEquiv A B C R))).groupIsoToMulEquiv

/-- The comparison is the original pullback projection preceded by tensor cancellation. -/
theorem factorTensorPointsEquiv_left (R : CommAlgCat.{u} (CommRingCat.of C))
    (p : (factor A B C G).affinePoints
      (CommAlgCat.of (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R))) :
    (factorTensorPointsEquiv A B C G R p).left =
      Spec.map (CommRingCat.ofHom (tensorEquiv A B C R).toRingHom) ≫
        p.left ≫ pullback.fst G.X.hom (Spec.algebraMap B (C ⊗[A] B)) := by
  change Spec.map (CommRingCat.ofHom (tensorEquiv A B C R).toRingHom) ≫
    ((affinePointsBaseChangeMulEquiv B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) G).symm p).left = _
  rw [affinePointsBaseChangeMulEquiv_symm_left]

/-- The coefficient-factor comparison commutes with every test-algebra map. -/
theorem factorTensorPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of C)} (a : R ⟶ R')
    (p : (factor A B C G).affinePoints
      (CommAlgCat.of (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R))) :
    factorTensorPointsEquiv A B C G R'
        ((factor A B C G).affinePointMap
          (CommAlgCat.ofHom
            (Algebra.TensorProduct.lTensor (S := C ⊗[A] B) (C ⊗[A] B) a.hom)) p) =
      G.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := B) B (a.hom.restrictScalars A)))
          (factorTensorPointsEquiv A B C G R p) := by
  apply Over.OverMorphism.ext
  rw [factorTensorPointsEquiv_left]
  change Spec.map (CommRingCat.ofHom (tensorEquiv A B C R').toRingHom) ≫
      ((Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lTensor (S := C ⊗[A] B) (C ⊗[A] B) a.hom).toRingHom) ≫
          p.left) ≫ pullback.fst G.X.hom (Spec.algebraMap B (C ⊗[A] B))) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lTensor (S := B) B (a.hom.restrictScalars A)).toRingHom) ≫
        (factorTensorPointsEquiv A B C G R p).left
  rw [factorTensorPointsEquiv_left]
  have hspec :
      Spec.map (CommRingCat.ofHom (tensorEquiv A B C R').toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lTensor (S := C ⊗[A] B) (C ⊗[A] B) a.hom).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lTensor (S := B) B (a.hom.restrictScalars A)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (tensorEquiv A B C R).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
      (tensorEquiv_naturality A B C a)
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ p.left ≫ pullback.fst G.X.hom (Spec.algebraMap B (C ⊗[A] B))) hspec

variable [Module.Finite A B] [Module.Projective A B]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Base change of the actual original restriction. -/
abbrev source : GroupScheme (Spec (CommRingCat.of C)) :=
  (GroupScheme.baseChange (Spec.algebraMap A C)).obj (groupScheme A B G)

instance source_isAffine : IsAffine (source A B C G).X.left := by
  change IsAffine (pullback (groupScheme A B G).X.hom (Spec.algebraMap A C))
  infer_instance

/-- Restriction over the base-changed coefficient algebra. -/
abbrev target : GroupScheme (Spec (CommRingCat.of C)) :=
  groupScheme C (C ⊗[A] B) (factor A B C G)

/-- The right-hand restriction recovers the same original tensor-valued points. -/
def targetPointsEquiv (R : CommAlgCat.{u} (CommRingCat.of C)) :
    (target A B C G).affinePoints R ≃*
      G.affinePoints (CommAlgCat.of B (B ⊗[A] R)) :=
  (pointsEquiv C (C ⊗[A] B) (factor A B C G) R).trans <|
    factorTensorPointsEquiv A B C G R

/-- Naturality of the tensor-valued points of the right-hand restriction. -/
theorem targetPointsEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of C)} (a : R ⟶ R')
    (p : (target A B C G).affinePoints R) :
    targetPointsEquiv A B C G R' ((target A B C G).affinePointMap a p) =
      G.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.lTensor (S := B) B (a.hom.restrictScalars A)))
          (targetPointsEquiv A B C G R p) := by
  dsimp only [targetPointsEquiv, MulEquiv.trans_apply]
  have hn := pointsEquiv_naturality C (C ⊗[A] B) (factor A B C G) a.hom p
  change pointsEquiv C (C ⊗[A] B) (factor A B C G) R'
    ((target A B C G).affinePointMap a p) = _ at hn
  exact (congrArg (factorTensorPointsEquiv A B C G R') hn).trans
    (factorTensorPointsEquiv_naturality A B C G a _)

/-- The two actual affine point groups agree through their common tensor-valued points. -/
def pointEquiv (R : CommAlgCat.{u} (CommRingCat.of C)) :
    (source A B C G).affinePoints R ≃* (target A B C G).affinePoints R :=
  (baseChangeTensorPointsEquiv A B C G R).trans (targetPointsEquiv A B C G R).symm

/-- The comparison is natural in the actual affine test algebra. -/
theorem pointEquiv_naturality
    {R R' : CommAlgCat.{u} (CommRingCat.of C)} (a : R ⟶ R')
    (p : (source A B C G).affinePoints R) :
    pointEquiv A B C G R' ((source A B C G).affinePointMap a p) =
      (target A B C G).affinePointMap a (pointEquiv A B C G R p) := by
  apply (targetPointsEquiv A B C G R').injective
  have hn := targetPointsEquiv_naturality A B C G a (pointEquiv A B C G R p)
  dsimp only [pointEquiv, MulEquiv.trans_apply] at hn ⊢
  simp only [MulEquiv.apply_symm_apply] at hn ⊢
  exact (baseChangeTensorPointsEquiv_naturality A B C G a p).trans hn.symm

/-- The actual group-valued affine point functors are naturally isomorphic. -/
def affinePointIso :
    (source A B C G).affinePointFunctor ≅ (target A B C G).affinePointFunctor :=
  NatIso.ofComponents (fun R => (pointEquiv A B C G R).toGrpIso) (by
    intro R R' a
    ext p
    exact pointEquiv_naturality A B C G a p)

/-- Arbitrary base change commutes with actual finite-projective affine Weil restriction. -/
def iso : source A B C G ≅ target A B C G :=
  AffinePointComparison.iso (affinePointIso A B C G)

/-- The reconstructed isomorphism has precisely the constructed affine-point formula. -/
theorem iso_hom_points (R : CommAlgCat.{u} (CommRingCat.of C))
    (p : (source A B C G).affinePoints R) :
    p ≫ (iso A B C G).hom.hom.hom = pointEquiv A B C G R p :=
  AffinePointComparison.iso_hom_points (affinePointIso A B C G) R p

variable {H : GroupScheme (Spec (CommRingCat.of B))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] (f : G ⟶ H)

/-- Base change of the restricted homomorphism. -/
abbrev sourceMap : source A B C G ⟶ source A B C H :=
  (GroupScheme.baseChange (Spec.algebraMap A C)).map (map A B f)

/-- Base change of the original homomorphism to the coefficient algebra. -/
abbrev factorMap : factor A B C G ⟶ factor A B C H :=
  (GroupScheme.baseChange (Spec.algebraMap B (C ⊗[A] B))).map f

/-- Restriction of the homomorphism over the base-changed coefficient algebra. -/
abbrev targetMap : target A B C G ⟶ target A B C H :=
  map C (C ⊗[A] B) (factorMap A B C G f)

/-- The left-hand tensor points retain the original group homomorphism. -/
theorem sourcePointsEquiv_target (R : CommAlgCat.{u} (CommRingCat.of C))
    (p : (source A B C G).affinePoints R) :
    baseChangeTensorPointsEquiv A B C H R (p ≫ (sourceMap A B C G f).hom.hom) =
      baseChangeTensorPointsEquiv A B C G R p ≫ f.hom.hom := by
  dsimp only [baseChangeTensorPointsEquiv, MulEquiv.trans_apply]
  exact (congrArg (pointsEquiv A B H R)
    (inversePoints_target A C R (map A B f) p)).trans
      (map_affinePoints A B f R _)

omit [Module.Finite A B] [Module.Projective A B]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
/-- The coefficient-factor point comparison retains the original homomorphism. -/
theorem factorTensorPointsEquiv_target (R : CommAlgCat.{u} (CommRingCat.of C))
    (p : (factor A B C G).affinePoints
      (CommAlgCat.of (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R))) :
    factorTensorPointsEquiv A B C H R
        (p ≫ ((GroupScheme.baseChange (Spec.algebraMap B (C ⊗[A] B))).map f).hom.hom) =
      factorTensorPointsEquiv A B C G R p ≫ f.hom.hom := by
  dsimp only [factorTensorPointsEquiv, MulEquiv.trans_apply]
  change H.affinePointMap (CommAlgCat.ofHom (tensorEquiv A B C R).toAlgHom)
      ((affinePointsBaseChangeMulEquiv B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) H).symm
        (p ≫ ((GroupScheme.baseChange (Spec.algebraMap B (C ⊗[A] B))).map f).hom.hom)) = _
  calc
    _ = H.affinePointMap (CommAlgCat.ofHom (tensorEquiv A B C R).toAlgHom)
        ((affinePointsBaseChangeMulEquiv B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) G).symm p ≫
          f.hom.hom) :=
      congrArg (H.affinePointMap (CommAlgCat.ofHom (tensorEquiv A B C R).toAlgHom))
        (inversePoints_target B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) f p)
    _ = _ := by
      change
        (algSpec (CommRingCat.of B)).map
            (CommAlgCat.ofHom (tensorEquiv A B C R).toAlgHom).op ≫
          ((affinePointsBaseChangeMulEquiv B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) G).symm p ≫
            f.hom.hom) =
        ((algSpec (CommRingCat.of B)).map
            (CommAlgCat.ofHom (tensorEquiv A B C R).toAlgHom).op ≫
          (affinePointsBaseChangeMulEquiv B (C ⊗[A] B) ((C ⊗[A] B) ⊗[C] R) G).symm p) ≫
            f.hom.hom
      exact (Category.assoc _ _ _).symm

/-- The tensor points of the right-hand restriction retain the original homomorphism. -/
theorem targetPointsEquiv_target (R : CommAlgCat.{u} (CommRingCat.of C))
    (p : (target A B C G).affinePoints R) :
    targetPointsEquiv A B C H R (p ≫ (targetMap A B C G f).hom.hom) =
      targetPointsEquiv A B C G R p ≫ f.hom.hom := by
  dsimp only [targetPointsEquiv, MulEquiv.trans_apply]
  exact (congrArg (factorTensorPointsEquiv A B C H R)
    (map_affinePoints C (C ⊗[A] B)
      ((GroupScheme.baseChange (Spec.algebraMap B (C ⊗[A] B))).map f) R p)).trans
        (factorTensorPointsEquiv_target A B C G f R _)

/-- The affine-point comparison commutes with both actual group homomorphisms. -/
theorem pointEquiv_target (R : CommAlgCat.{u} (CommRingCat.of C))
    (p : (source A B C G).affinePoints R) :
    pointEquiv A B C H R (p ≫ (sourceMap A B C G f).hom.hom) =
      pointEquiv A B C G R p ≫ (targetMap A B C G f).hom.hom := by
  apply (targetPointsEquiv A B C H R).injective
  have ht := targetPointsEquiv_target A B C G f R (pointEquiv A B C G R p)
  dsimp only [pointEquiv, MulEquiv.trans_apply] at ht ⊢
  simp only [MulEquiv.apply_symm_apply] at ht ⊢
  exact (sourcePointsEquiv_target A B C G f R p).trans ht.symm

/-- The group-scheme comparison is natural in the original homomorphism. -/
theorem iso_naturality :
    (iso A B C G).hom ≫ targetMap A B C G f =
      sourceMap A B C G f ≫ (iso A B C H).hom := by
  apply AffinePointComparison.hom_ext (source A B C G)
  intro R p
  change (p ≫ (iso A B C G).hom.hom.hom) ≫ (targetMap A B C G f).hom.hom =
    (p ≫ (sourceMap A B C G f).hom.hom) ≫ (iso A B C H).hom.hom.hom
  rw [iso_hom_points, iso_hom_points]
  exact (pointEquiv_target A B C G f R p).symm

local instance : IsAffine (kernel (factorMap A B C G f)).X.left := by
  let : IsAffineHom (factor A B C G).X.hom := inferInstance
  let : IsSeparated (factor A B C H).X.hom := inferInstance
  let : IsAffineHom (kernel (factorMap A B C G f)).X.hom := by
    rw [← (kernelι (factorMap A B C G f)).hom.hom.w]
    infer_instance
  exact isAffine_of_isAffineHom (kernel (factorMap A B C G f)).X.hom

local instance : LocallyOfFiniteType (kernel (factorMap A B C G f)).X.hom := by
  let : IsSeparated (factor A B C H).X.hom := inferInstance
  rw [← (kernelι (factorMap A B C G f)).hom.hom.w]
  infer_instance

/-- The actual kernel after arbitrary base change is restriction of the actual
kernel over the base-changed coefficient algebra. -/
def kernelIso :
    kernel (sourceMap A B C G f) ≅
      groupScheme C (C ⊗[A] B) (kernel (factorMap A B C G f)) :=
  kernelSquareIso (sourceMap A B C G f) (targetMap A B C G f)
      (iso A B C G) (iso A B C H) (iso_naturality A B C G f) ≪≫
    AffineWeil.kernelIso C (C ⊗[A] B) (factorMap A B C G f)

/-- The actual-kernel comparison respects inclusion into the source. -/
theorem kernelIso_hom_inclusion :
    (kernelIso A B C G f).hom ≫
        map C (C ⊗[A] B) (kernelι (factorMap A B C G f)) =
      kernelι (sourceMap A B C G f) ≫ (iso A B C G).hom := by
  dsimp only [kernelIso, Iso.trans_hom]
  rw [Category.assoc, AffineWeil.kernelIso_hom_inclusion]
  exact kernelSquareIso_hom_ι _ _ _ _ _

end Langlands.GroupScheme.AffineWeil.BaseChange
