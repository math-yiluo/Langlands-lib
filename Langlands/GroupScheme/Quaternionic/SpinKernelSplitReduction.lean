import Langlands.GroupScheme.Quaternionic.SpinKernelComparison
import Langlands.AbelianScheme.KernelBaseChange

/-! # From split orthogonal coordinates to the original binary diagonal kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

section RootCoordinates

variable {K L : Type u} [Field K] [Field L]
  (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))

/-- Square-root parameters over the extension field in the original coefficient algebra. -/
def squareRootCoordinates (U : Over (Spec (CommRingCat.of L))) :
    {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1} ≃
      rootsOfUnity 2 (BinaryScheme.coefficients ((Over.map b).obj U)) where
  toFun z := ⟨Gm.pointsEquiv _ U z.val, (mem_rootsOfUnity 2 _).mpr (by
    simpa only [map_mul, map_one, pow_two] using
      congrArg (Gm.pointsEquiv (Spec (CommRingCat.of L)) U) z.2)⟩
  invFun z := ⟨(Gm.pointsEquiv _ U).symm z.val, by
    apply (Gm.pointsEquiv _ U).injective
    rw [map_mul, map_one, MulEquiv.apply_symm_apply]
    simpa only [pow_two] using (mem_rootsOfUnity 2 _).mp z.2⟩
  left_inv z := Subtype.ext ((Gm.pointsEquiv _ U).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((Gm.pointsEquiv _ U).apply_symm_apply z.val)

/-- The original binary `μ₂` points, with square-root parameters over the extension. -/
def binaryRootPointsEquiv (U : Over (Spec (CommRingCat.of L))) :
    {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1} ≃
      ((Over.map b).obj U ⟶ (BinaryKernel.muTwo (K := K)).X) :=
  (squareRootCoordinates b U).trans (BinaryKernel.rootsPointsEquiv _).symm.toEquiv

end RootCoordinates

section KernelComparison

variable {K L : Type u} [Field K] [Field L]
  (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (f : G ⟶ H) (d : BinaryKernel.muTwo (K := K) ⟶ kernel f)
  (a : (Gm (Spec (CommRingCat.of L))).toGrp ⟶ (GroupScheme.baseChange b).obj G)

/-- All-test square-root parameters identifying the original binary map with the
full kernel after base change make that original map an isomorphism after base change. -/
theorem isIso_baseChange_binaryKernelMap
    (hparam : ∀ (U : Over (Spec (CommRingCat.of L)))
      (x : U ⟶ ((GroupScheme.baseChange b).obj G).X),
      x ≫ ((GroupScheme.baseChange b).map f).hom.hom = 1 →
        ∃! z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1},
          z.val ≫ a.hom.hom = x)
    (hc : ∀ (U : Over (Spec (CommRingCat.of L)))
      (z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1}),
      baseChangePointsEquiv b G U (z.val ≫ a.hom.hom) =
        binaryRootPointsEquiv b U z ≫ (d ≫ kernelι f).hom.hom) :
    IsIso ((GroupScheme.baseChange b).map d) := by
  let F := GroupScheme.baseChange b
  let e (U : Over (Spec (CommRingCat.of L))) :=
    (binaryRootPointsEquiv b U).trans
      (baseChangePointsEquiv b (BinaryKernel.muTwo (K := K)) U).symm.toEquiv
  have he (U : Over (Spec (CommRingCat.of L)))
      (z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1}) :
      (e U z ≫ (F.map d).hom.hom) ≫ (F.map (kernelι f)).hom.hom =
        z.val ≫ a.hom.hom := by
    apply (baseChangePointsEquiv b G U).injective
    rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_comp, hc]
    simp only [e, Equiv.trans_apply, MulEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, MulEquiv.apply_symm_apply, Grp.comp_hom_hom, Category.assoc]
  have hx (U : Over (Spec (CommRingCat.of L)))
      (x : U ⟶ (F.obj (kernel f)).X) :
      (x ≫ (F.map (kernelι f)).hom.hom) ≫ (F.map f).hom.hom = 1 := by
    apply (baseChangePointsEquiv b H U).injective
    rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_comp, map_one]
    exact (kernelPointsEquiv f _ (baseChangePointsEquiv b (kernel f) U x)).property
  have : IsIso ((F.map d).hom.hom) := by
    apply isIso_of_yoneda_map_bijective
    intro U
    constructor
    · intro y y' hyy'
      change y ≫ (F.map d).hom.hom = y' ≫ (F.map d).hom.hom at hyy'
      apply (e U).symm.injective
      obtain ⟨z, hz, huniq⟩ := hparam U
        ((y ≫ (F.map d).hom.hom) ≫ (F.map (kernelι f)).hom.hom)
        (hx U (y ≫ (F.map d).hom.hom))
      have hy : ((e U).symm y).val ≫ a.hom.hom =
          (y ≫ (F.map d).hom.hom) ≫ (F.map (kernelι f)).hom.hom := by
        rw [← he, Equiv.apply_symm_apply]
      have hy' : ((e U).symm y').val ≫ a.hom.hom =
          (y ≫ (F.map d).hom.hom) ≫ (F.map (kernelι f)).hom.hom := by
        rw [← he, Equiv.apply_symm_apply, ← hyy']
      exact (huniq _ hy).trans (huniq _ hy').symm
    · intro x
      obtain ⟨z, hz, -⟩ := hparam U (x ≫ (F.map (kernelι f)).hom.hom) (hx U x)
      refine ⟨e U z, ?_⟩
      apply (cancel_mono (F.map (kernelι f)).hom.hom).mp
      rw [he, hz]
  have : IsIso ((Mon.forget _).map (F.map d).hom) := this
  have : IsIso (F.map d).hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map (F.map d)) := this
  exact isIso_of_reflects_iso (F.map d) (Grp.forget₂Mon _)

end KernelComparison

section SpinComparison

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Infinite K] [Field L]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})
  (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
  (a : (Gm (Spec (CommRingCat.of L))).toGrp ⟶ (GroupScheme.baseChange b).obj S)

/-- A split square-root calculation suffices when its map agrees with the
base change of the original binary spin diagonal on every test scheme. -/
theorem isIso_baseChange_diagonalKernel_of_squareRootParametrization
    (hparam : ∀ (U : Over (Spec (CommRingCat.of L)))
      (x : U ⟶ ((GroupScheme.baseChange b).obj S).X),
      x ≫ ((GroupScheme.baseChange b).map π).hom.hom = 1 →
        ∃! z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1},
          z.val ≫ a.hom.hom = x)
    (hc : ∀ (U : Over (Spec (CommRingCat.of L)))
      (z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1}),
      baseChangePointsEquiv b S U (z.val ≫ a.hom.hom) =
        binaryRootPointsEquiv b U z ≫
          (BinarySpinLift.diagonalSpin σ hdim hsym h hπ hsc).hom.hom) :
    IsIso ((GroupScheme.baseChange b).map
      (BinarySpinLift.diagonalKernel σ hdim hsym h hπ hsc)) := by
  apply isIso_baseChange_binaryKernelMap b π
    (BinarySpinLift.diagonalKernel σ hdim hsym h hπ hsc) a hparam
  simpa only [BinarySpinLift.diagonalKernel_comp] using hc

end SpinComparison

end Langlands.GroupScheme.Quaternionic.SpinKernel
