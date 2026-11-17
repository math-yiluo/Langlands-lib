import Langlands.GroupScheme.Torus.DiagonalizableSourceCoordinates
import Langlands.GroupScheme.HopfMorphismBaseChange
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Scalar extension of actual diagonalizable-source coordinate maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- An isomorphism on an actual affine-spectrum base change makes its tensor
coordinate map bijective. -/
theorem tensorMap_bijective_of_baseChange_isIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B)
    [IsIso
      (((Over.pullback (Spec.algebraMap R S)).map
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).left)] :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  let φ : CommRingCat.of (S ⊗[R] A) ⟶ CommRingCat.of (S ⊗[R] B) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
  have he : Spec.map φ =
      (HopfMorphismBaseChange.tensorSpecIso R S B).inv ≫
        (((Over.pullback (Spec.algebraMap R S)).map
          ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).left) ≫
        (HopfMorphismBaseChange.tensorSpecIso R S A).hom := by
    rw [HopfMorphismBaseChange.tensorSpecIso_naturality]
    simp [φ]
  have : IsIso (Spec.map φ) := by
    rw [he]
    infer_instance
  have : IsIso (Scheme.Spec.map φ.op) := by
    rw [Scheme.Spec_map]
    exact ‹IsIso (Spec.map φ)›
  have : IsIso φ.op := isIso_of_reflects_iso φ.op Scheme.Spec
  have : IsIso φ := isIso_of_op φ
  exact ConcreteCategory.bijective_of_isIso φ

variable {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]

/-- Scalar extension of the standard diagonalizable-source coordinate map,
expressed in the group algebra over the new coefficient ring. -/
def diagonalSourceScalarMap (S : Type u) [CommRing S] [Algebra R S]
    (f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶ G) :
    S ⊗[R] AffineCoordinates.hopfAlgebra G →ₐ[S] AddMonoidAlgebra S M :=
  Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension
    (diagonalSourceCoordinateMap f).hom.toAlgHom S

/-- An isomorphism of actual scalar-extended group morphisms makes the
standard scalar-extended coordinate map bijective. -/
theorem diagonalSourceScalarMap_bijective
    (f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶ G)
    [IsIso ((GroupScheme.baseChange (Spec.algebraMap R S)).map f)] :
    Function.Bijective (diagonalSourceScalarMap S f) := by
  let π := diagonalSourceCoordinateMap f
  have hm : IsIso
      ((GroupScheme.baseChange (Spec.algebraMap R S)).map
        ((hopfSpec (CommRingCat.of R)).map π.op)) := by
    rw [show (hopfSpec (CommRingCat.of R)).map π.op =
      (Diagonalizable.hopfSpecIso (CommRingCat.of R) M).hom ≫ f ≫
        (AffineCoordinates.hopfSpecIso G).inv from diagonalSourceCoordinateMap_spec f,
      Functor.map_comp, Functor.map_comp]
    infer_instance
  have hraw : IsIso
      (((Over.pullback (Spec.algebraMap R S)).map
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom π.hom.toAlgHom).op)).left) :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso
      ((GroupScheme.baseChange (Spec.algebraMap R S)).map
        ((hopfSpec (CommRingCat.of R)).map π.op))
  have hbij := tensorMap_bijective_of_baseChange_isIso (S := S) π.hom.toAlgHom
  change Function.Bijective
    (Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension π.hom.toAlgHom S)
  rw [HopfMorphismBaseChange.scalarExtension_eq]
  exact (AddMonoidAlgebra.scalarTensorEquiv R S (M := M)).bijective.comp hbij

/-- Injectivity on actual quotient fibres detects ideal-multiple membership in
the original coordinates. -/
theorem diagonalSourceCoordinates_mem_smul_of_baseChange_isIso
    (J : Ideal R)
    (f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶ G)
    [IsIso ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ J))).map f)]
    (a : AffineCoordinates.hopfAlgebra G)
    (ha : (diagonalSourceCoordinateMap f).hom a ∈
      J • (⊤ : Submodule R (AddMonoidAlgebra R M))) :
    a ∈ J • (⊤ : Submodule R (AffineCoordinates.hopfAlgebra G)) := by
  have hzero : (1 : R ⧸ J) ⊗ₜ[R] (diagonalSourceCoordinateMap f).hom a = 0 := by
    have hker : (diagonalSourceCoordinateMap f).hom a ∈
        LinearMap.ker (TensorProduct.mk R (R ⧸ J) (AddMonoidAlgebra R M) 1) := by
      rwa [LinearMap.ker_tensorProductMk]
    exact hker
  have hmap : diagonalSourceScalarMap (R ⧸ J) f ((1 : R ⧸ J) ⊗ₜ[R] a) = 0 := by
    rw [diagonalSourceScalarMap, HopfMorphismBaseChange.scalarExtension_eq]
    change (AddMonoidAlgebra.scalarTensorEquiv R (R ⧸ J) (M := M))
      ((1 : R ⧸ J) ⊗ₜ[R] (diagonalSourceCoordinateMap f).hom a) = 0
    rw [hzero, map_zero]
  have hred : (1 : R ⧸ J) ⊗ₜ[R] a = 0 :=
    (diagonalSourceScalarMap_bijective (S := R ⧸ J) f).injective
      (hmap.trans (map_zero (diagonalSourceScalarMap (R ⧸ J) f)).symm)
  have hker : a ∈ LinearMap.ker
      (TensorProduct.mk R (R ⧸ J) (AffineCoordinates.hopfAlgebra G) 1) := hred
  rwa [LinearMap.ker_tensorProductMk] at hker

/-- A special-fibre isomorphism gives a unit coefficient in each character
degree over a local base ring. -/
theorem diagonalSourceCoordinates_unit_coeff_of_special_isIso [IsLocalRing R]
    (f : (Diagonalizable.groupScheme (CommRingCat.of R) M).toGrp ⟶ G)
    [IsIso ((GroupScheme.baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)] (m : M) :
    ∃ a : AffineCoordinates.hopfAlgebra G,
      IsUnit (((diagonalSourceCoordinateMap f).hom a).coeff m) := by
  obtain ⟨a, ha⟩ :=
    Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus.exists_nonzero_coefficient
      (diagonalSourceCoordinateMap f).hom.toAlgHom (IsLocalRing.ResidueField R)
      (diagonalSourceScalarMap_bijective (S := IsLocalRing.ResidueField R) f).surjective m
  exact ⟨a, (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ha⟩

/-- Finite type over a noetherian base makes the actual coordinate Hopf
algebra noetherian. -/
theorem coordinate_isNoetherianRing [IsNoetherianRing R] [LocallyOfFiniteType G.X.hom] :
    IsNoetherianRing (AffineCoordinates.hopfAlgebra G) := by
  let : Algebra.FiniteType R (AffineCoordinates.hopfAlgebra G) :=
    AffineCoordinates.algebraFiniteType G
  exact Algebra.FiniteType.isNoetherianRing R (AffineCoordinates.hopfAlgebra G)

end Langlands.GroupScheme.CompleteLocalDeformation
