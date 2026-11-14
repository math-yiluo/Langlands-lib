import Langlands.GroupScheme.Lie.LinearBaseChangeNaturality
import Langlands.GroupScheme.Rational.RootPointLieBaseChange
import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.GroupScheme.Rational.ScalarExtensionNaturality

/-! # Intrinsic root-point Lie comparison under field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G U : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "U_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) U

namespace GaloisPointComparison

/-- The affine pullback and rational-coefficient comparisons use the same
projection of the actual scheme pullback. -/
theorem affineBaseChangeEquiv_rationalCoeffEquiv
    (x : rationalPoints G_K) :
    Lie.affineBaseChangeEquiv k K G K (rationalCoeffEquiv K G_K x) =
      baseChangeCoeffEquiv k K G x := by
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left, rationalCoeffEquiv_left,
    baseChangeCoeffEquiv_left]

/-- The actual extension of a rational point becomes coefficient extension
after the affine pullback comparison. -/
theorem affineBaseChangeEquiv_rationalExtend
    (x : rationalPoints G) :
    Lie.affineBaseChangeEquiv k K G K
        (rationalCoeffEquiv K G_K (rationalExtend k K G x)) =
      Lie.affineMap G (Algebra.ofId k K) (rationalCoeffEquiv k G x) := by
  rw [affineBaseChangeEquiv_rationalCoeffEquiv, baseChangeCoeffEquiv_rationalExtend]
  rfl

end GaloisPointComparison

variable [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]

local instance {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b)
  infer_instance

namespace Lie

/-- Actual extension of a Lie vector commutes with the differential of a
group-scheme homomorphism. -/
theorem schemeScalarExtension_target
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType U.X.hom] (j : U ⟶ G)
    (X : Additive (lieKernel U k)) :
    schemeScalarExtension (K := K) G (1 ⊗ₜ[k] targetMapLinear j k X) =
      targetMapLinear ((GroupScheme.baseChange b).map j) K
        (schemeScalarExtension (K := K) U (1 ⊗ₜ[k] X)) := by
  apply (kernelBaseChangeLinearEquiv k K G K).injective
  rw [kernelBaseChangeLinearEquiv_target, schemeScalarExtension_tmul,
    schemeScalarExtension_tmul, one_smul, one_smul,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact (lieKernelTargetLinear_map j (Algebra.ofId k K) X).symm

end Lie

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" => characterLattice.baseChange b S a

local instance {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b)
  infer_instance

local instance : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Extend an actual root weight vector by tensor scalar extension into
the Lie algebra of the actual base-changed group. -/
def rootWeightSpaceFieldExtend :
    weightSpace i a →+ weightSpace (T := S_K) i_K a_K where
  toFun X := ⟨Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] X.val),
    weightSpace_baseChange_mem G i a X.property⟩
  map_zero' := by
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero, TensorProduct.tmul_zero, map_zero]
  map_add' X Y := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add, TensorProduct.tmul_add, map_add]

@[simp]
theorem rootWeightSpaceFieldExtend_val (X : weightSpace i a) :
    (rootWeightSpaceFieldExtend (K := K) i a X : Additive (lieKernel G_K K)) =
      Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] X.val) := rfl

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- Extension of the intrinsic root-group point agrees with extension through
any representative of that root functor. -/
theorem rootGroupPointsFieldExtend_represented
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : (subgroup i a).IsRepresentedBy j) (v : rationalPoints U) :
    rootGroupPointsFieldExtend (K := K) i a (hj.pointsEquiv _ v) =
      (rootSubgroup_isRepresentedBy_baseChange (K := K) i a hj).pointsEquiv _
        (rationalExtend k K U v) := by
  apply Subtype.ext
  exact rationalExtend_map k K j v

set_option maxHeartbeats 1000000 in
/-- The intrinsic root-point comparison intertwines the actual rational
field-extension map and the actual Lie scheme scalar-extension map. -/
theorem rootPointLieEquiv_fieldExtend
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    (v : rootGroupPoints i a) :
    rootPointLieEquiv (k := K) (S := S_K) (G := G_K) (a := a_K)
        (hS.baseChange b) i_K
        ((characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha)
        (HasNoHigherRoots.baseChange (k := k) (K := K)
          (S := S) (G := G) (a := a) hS i hhigh)
        (Additive.ofMul (rootGroupPointsFieldExtend (K := K) i a v)) =
      rootWeightSpaceFieldExtend (K := K) i a
        (rootPointLieEquiv hS i ha hhigh (Additive.ofMul v)) := by
  obtain ⟨U, hU, j, hj, hrep⟩ := rootPointLieEquiv_exists_representative hS i ha hhigh
  let : IsAffineHom U.X.hom := hU
  let hjK := rootSubgroup_isRepresentedBy_baseChange (K := K) i a hj
  let haK := (characterLattice.baseChangeEquiv b S hS).map_ne_zero_iff.mpr ha
  let hhK := hhigh.baseChange (K := K) hS i
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  let x := (hj.pointsEquiv _).symm v
  have hx : hj.pointsEquiv _ x = v := (hj.pointsEquiv _).apply_symm_apply _
  have hrepK := rootPointLieEquiv_eq_represented
    (k := K) (S := S_K) (G := G_K) (U := (GroupScheme.baseChange b).obj U)
    (a := a_K) (hS.baseChange b) i_K haK hhK hjK
  rw [hrepK, hrep, ← hx,
    rootGroupPointsFieldExtend_represented (K := K) i a hj x]
  apply Subtype.ext
  change (representedRootPointLieEquiv (k := K) (S := S_K) (G := G_K)
      (U := (GroupScheme.baseChange b).obj U) (a := a_K)
      (hS.baseChange b) i_K haK hhK hjK
      (Additive.ofMul (hjK.pointsEquiv _ (rationalExtend k K U x))) :
        Additive (lieKernel G_K K)) =
    Lie.schemeScalarExtension (K := K) G
      (1 ⊗ₜ[k] (representedRootPointLieEquiv hS i ha hhigh hj
        (Additive.ofMul (hj.pointsEquiv _ x)) : Additive (lieKernel G k)))
  rw [representedRootPointLieEquiv_apply, representedRootPointLieEquiv_apply]
  apply (Lie.kernelBaseChangeLinearEquiv k K G K).injective
  rw [Lie.kernelBaseChangeLinearEquiv_target,
    rootVectorPointLieEquiv_baseChange (K := K) hS i ha hhigh hj K,
    affineBaseChangeEquiv_rationalExtend, Lie.schemeScalarExtension_tmul,
    one_smul, LinearEquiv.apply_symm_apply]
  exact (congrArg (Lie.targetMapLinear j K)
    (vectorPointLieEquiv_naturality c.2.val c.2.property.1
      (CommAlgCat.ofHom (Algebra.ofId k K)) (rationalCoeffEquiv k U x))).trans
    (lieKernelTargetLinear_map j (Algebra.ofId k K)
      (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
        (Additive.ofMul (rationalCoeffEquiv k U x))))

end Langlands.Geometry.Building
