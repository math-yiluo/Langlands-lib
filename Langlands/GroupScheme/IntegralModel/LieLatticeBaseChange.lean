import Langlands.GroupScheme.IntegralModel.LieLatticeCoefficientExtension
import Langlands.GroupScheme.IntegralModel.BaseChange
import Langlands.GroupScheme.IntegralModel.LieLattice
import Langlands.GroupScheme.Lie.LinearBaseChangeNaturality
import Langlands.GroupScheme.Lie.ElementCentralizer

/-! # Coefficient extension of the generic Lie algebra and the integral Lie lattice -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable (R A : Type u) {K B : Type u} [CommRing R] [CommRing A] [Field K] [Field B]
  [Algebra R K] [Algebra A B] [Algebra R A] [Algebra K B] [Algebra R B]
  [IsScalarTower R A B] [IsScalarTower R K B]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]

local notation "G_B" => Functor.obj (GroupScheme.baseChange (Spec.algebraMap K B)) G

local instance : IsAffineHom (G_B).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (Spec.algebraMap K B))
  infer_instance

/-- Extend both coefficients of a generic dual-number tangent point and regard the
result as a tangent point of the actual scheme pullback. -/
def GenericLie.baseChange : GenericLie R G →ₛₗ[algebraMap R A] GenericLie A G_B where
  toFun X := (GenericLie.equiv A G_B).symm
    ((Lie.kernelBaseChangeLinearEquiv K B G B).symm
      (lieKernelMapLinear G (Algebra.ofId K B) (GenericLie.equiv R G X)))
  map_add' X Y := by simp only [LinearEquiv.map_add, LinearMap.map_add]
  map_smul' r X := by
    rw [GenericLie.smul_def, LinearEquiv.map_smul, LinearMap.map_smulₛₗ,
      LinearEquiv.map_smul, LinearEquiv.map_smul, GenericLie.smul_def]
    congr 1
    exact (IsScalarTower.algebraMap_apply R K B r).symm.trans
      (IsScalarTower.algebraMap_apply R A B r)

theorem GenericLie.baseChange_apply (X : GenericLie R G) :
    GenericLie.baseChange R A G X = (GenericLie.equiv A G_B).symm
      ((Lie.kernelBaseChangeLinearEquiv K B G B).symm
        (lieKernelMapLinear G (Algebra.ofId K B) (GenericLie.equiv R G X))) := rfl

namespace IntegralModel

variable {R A G} [IsDomain R] [IsDomain A] [IsFractionRing R K] [IsFractionRing A B]
  (M : IntegralModel R K G)

local notation "M_A" => M.baseChange A B
local notation "M_K" => M.genericFibre

local instance : IsAffineHom ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group).X.hom := by
  change IsAffineHom (pullback.snd M.group.X.hom (Spec.algebraMap R A))
  infer_instance

local instance : IsAffineHom ((GroupScheme.baseChange (Spec.algebraMap A B)).obj
    ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)).X.hom := by
  change IsAffineHom (pullback.snd
    ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group).X.hom (Spec.algebraMap A B))
  infer_instance

local notation "M_AB" => IntegralModel.genericFibre (M.baseChange A B)

/-- The pullback comparison sends the extended model's generic-fibre tangent
point to the same original-model point along both sides of the coefficient square. -/
private theorem lieKernel_coefficientSquare (Z : Additive (lieKernel M_AB B)) :
    Lie.kernelBaseChangeLinearEquiv R K M.group B
      (Lie.targetMapLinear M.genericIso.inv B
        (Lie.kernelBaseChangeLinearEquiv K B G B
          (Lie.targetMapLinear (M.baseChangeGenericIso A B).hom B Z))) =
    Lie.kernelBaseChangeLinearEquiv R A M.group B
      (Lie.kernelBaseChangeLinearEquiv A B (M_A).group B Z) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change (Lie.affineBaseChangeEquiv R K M.group (DualNumber B)
    (Lie.affineBaseChangeEquiv K B G (DualNumber B)
      (Z.toMul.val ≫ (M.baseChangeGenericIso A B).hom.hom.hom) ≫
      M.genericIso.inv.hom.hom)).left =
    (Lie.affineBaseChangeEquiv R A M.group (DualNumber B)
      (Lie.affineBaseChangeEquiv A B (M_A).group (DualNumber B) Z.toMul.val)).left
  simp only [Lie.affineBaseChangeEquiv_left, Over.comp_left, Category.assoc]
  rw [M.baseChangeGenericIso_hom_fst A B]
  rfl

/-- Tangent coefficient extension on the model followed by the inverse
pullback identification of the model's Lie module. -/
def lieModuleBaseChange (X : M.LieModule) : (M_A).LieModule :=
  (Lie.kernelBaseChangeLinearEquiv R A M.group A).symm
    (lieKernelMapLinear M.group (Algebra.ofId R A) X)

set_option maxHeartbeats 700000 in
/-- Extension of an integral tangent vector agrees with extension of its generic tangent point. -/
theorem lieMap_baseChange (X : M.LieModule) :
    (M_A).lieMap (M.lieModuleBaseChange (A := A) (B := B) X) =
      GenericLie.baseChange R A G (M.lieMap X) := by
  apply (GenericLie.equiv A G_B).injective
  apply (Lie.kernelBaseChangeLinearEquiv K B G B).injective
  apply (lieKernelLinearEquiv M.genericIso B).symm.injective
  apply (Lie.kernelBaseChangeLinearEquiv R K M.group B).injective
  simp only [lieMap_apply, GenericLie.baseChange_apply, genericLieEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change (Lie.kernelBaseChangeLinearEquiv R K M.group B)
      (Lie.targetMapLinear M.genericIso.inv B
        (Lie.kernelBaseChangeLinearEquiv K B G B
          (Lie.targetMapLinear (M.baseChangeGenericIso A B).hom B _))) = _
  rw [M.lieKernel_coefficientSquare]
  rw [LinearEquiv.apply_symm_apply]
  have hleft := Lie.kernelBaseChangeLinearEquiv_naturality R A M.group
    (Algebra.ofId A B) (M.lieModuleBaseChange (A := A) (B := B) X)
  rw [lieModuleBaseChange, LinearEquiv.apply_symm_apply] at hleft
  refine hleft.trans ?_
  let Z := (Lie.kernelBaseChangeLinearEquiv R K M.group K).symm
    (lieKernelMapLinear M.group (Algebra.ofId R K) X)
  change _ = Lie.kernelBaseChangeLinearEquiv R K M.group B
    ((lieKernelLinearEquiv M.genericIso B).symm
      (lieKernelMapLinear G (Algebra.ofId K B) (Lie.targetMapLinear M.genericIso.hom K Z)))
  rw [← lieKernelTargetLinear_map, show Lie.targetMapLinear M.genericIso.hom B =
    (lieKernelLinearEquiv M.genericIso B).toLinearMap from rfl, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  have hright := Lie.kernelBaseChangeLinearEquiv_naturality R K M.group (Algebra.ofId K B) Z
  change _ = Lie.kernelBaseChangeLinearEquiv R K M.group B _
  rw [hright]
  simp only [Z, LinearEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  simp only [lieKernelMapLinear_toMul, ← lieKernelMap_comp]
  have hcomp : ((Algebra.ofId A B).restrictScalars (CommRingCat.of R)).comp (Algebra.ofId R A) =
      ((Algebra.ofId K B).restrictScalars (CommRingCat.of R)).comp (Algebra.ofId R K) := by
    apply AlgHom.ext
    intro r
    exact (IsScalarTower.algebraMap_apply R A B r).symm.trans
      (IsScalarTower.algebraMap_apply R K B r)
  rw [hcomp]

/-- The generic tangent extension carries the original integral Lie lattice into the
Lie lattice of the actual base-changed model. -/
theorem baseChange_mem_lieLattice {Y : GenericLie R G} (hY : Y ∈ M.lieLattice) :
    GenericLie.baseChange R A G Y ∈ (M_A).lieLattice := by
  obtain ⟨X, rfl⟩ := hY
  exact ⟨M.lieModuleBaseChange X, M.lieMap_baseChange X⟩

end IntegralModel
end Langlands.GroupScheme
