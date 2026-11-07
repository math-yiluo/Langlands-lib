import Langlands.Global.CurvePlaceProjectiveWeilAdeleEvaluation
import Langlands.Global.ProjectiveAffineChart
import Langlands.Global.AdelicTensorBaseChange

/-! # The canonical full function-field tensor comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.Global

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section General

variable (A B R D : Type u) [CommRing A] [CommRing B] [CommRing R] [CommRing D]
  [Algebra A B] [Algebra A R] [Algebra B D]
  [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]
  [IsSeparated Y.hom]

private def tensorWeilPointEquiv (hY : HasFiniteAffineNeighborhoods Y.left) :
    RingPoint A (affineChartWeilRestriction A B Y) R ≃
      RingPoint B Y (B ⊗[A] R) :=
  (affineChartWeilRestrictionTestEquiv A B Y hY (ringTest A R)).trans
    (ringBaseChangeSpectrumIso A B R).homFromEquiv

private theorem tensorWeilPointEquiv_evaluation
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (f : R →+* D)
    (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))
    (g : B ⊗[A] R →ₐ[B] D) (hg : ∀ r : R, g (1 ⊗ₜ[A] r) = f r)
    (p : RingPoint A (affineChartWeilRestriction A B Y) R) :
    (tensorWeilPointEquiv A B R Y hY p).changeRing g =
      weilRestrictionEvaluation A B R D f hf Y p := by
  have ht : ringTestMap B g ≫ (ringBaseChangeSpectrumIso A B R).inv =
      weilRestrictionEvaluationTest A B R D f hf := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change Spec.map _ ≫
          (ringBaseChangeSpectrumIso A B R).inv.left ≫
            pullback.fst (Spec.algebraMap A R) (Spec.algebraMap A B) =
        (weilRestrictionEvaluationTest A B R D f hf).left ≫
          pullback.fst (Spec.algebraMap A R) (Spec.algebraMap A B)
      rw [ringBaseChangeSpectrumIso_inv_fst, weilRestrictionEvaluationTest_fst,
        ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext hg
    · exact (Over.w (ringTestMap B g ≫ (ringBaseChangeSpectrumIso A B R).inv)).trans
        (Over.w (weilRestrictionEvaluationTest A B R D f hf)).symm
  change ringTestMap B g ≫ ((ringBaseChangeSpectrumIso A B R).inv ≫ _) =
    weilRestrictionEvaluationTest A B R D f hf ≫ _
  rw [← Category.assoc, ht]
  simp only [affineChartWeilRestrictionTestEquiv_apply]

private theorem affineLinePoint_changeRing
    [Algebra A D] (g : R →ₐ[A] D) (r : R) :
    ((affineLinePointEquiv A R).symm r).changeRing g =
      (affineLinePointEquiv A D).symm (g r) := by
  change ringTestMap A g ≫
    ringTestMap A (MvPolynomial.aeval (fun _ : Unit => r)) =
      ringTestMap A (MvPolynomial.aeval (fun _ : Unit => g r))
  rw [← ringTestMap_comp]
  apply congrArg (ringTestMap A)
  apply MvPolynomial.algHom_ext
  intro i
  cases i
  simp

private theorem affineLineTensorMap_bijective
    (hY : HasFiniteAffineNeighborhoods (ringTest B (MvPolynomial Unit B)).left)
    (f : R →+* D)
    (hf : f.comp (algebraMap A R) = (algebraMap B D).comp (algebraMap A B))
    (g : B ⊗[A] R →ₐ[B] D) (hg : ∀ r : R, g (1 ⊗ₜ[A] r) = f r)
    (hb : Function.Bijective
      (weilRestrictionEvaluation A B R D f hf (ringTest B (MvPolynomial Unit B)))) :
    Function.Bijective g := by
  let e := tensorWeilPointEquiv A B R (ringTest B (MvPolynomial Unit B)) hY
  let a := affineLinePointEquiv B (B ⊗[A] R)
  let d := affineLinePointEquiv B D
  let c := ((e.trans a).symm.trans (Equiv.ofBijective _ hb)).trans d
  have hc : ⇑c = ⇑g := by
    funext z
    change d (weilRestrictionEvaluation A B R D f hf
      (ringTest B (MvPolynomial Unit B)) (e.symm (a.symm z))) = g z
    rw [← tensorWeilPointEquiv_evaluation A B R D
      (ringTest B (MvPolynomial Unit B)) hY f hf g hg]
    change d ((e (e.symm (a.symm z))).changeRing g) = g z
    rw [Equiv.apply_symm_apply]
    change d (((affineLinePointEquiv B (B ⊗[A] R)).symm z).changeRing g) = g z
    rw [affineLinePoint_changeRing]
    exact d.apply_symm_apply _
  rw [← hc]
  exact c.bijective

end General

section FunctionField

open IntermediateField
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L]

set_option quotPrecheck false in
local notation "withUpper% " t:0 =>
  (letI : Algebra (RatFunc k) L :=
    ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
   letI : IsScalarTower (RatFunc k) K L :=
    .of_algebraMap_eq fun _ => rfl
   letI : IsScalarTower k (RatFunc k) L :=
    .of_algebraMap_eq fun a => by
      change algebraMap k L a =
        algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
      rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
        ← IsScalarTower.algebraMap_apply k K L]
   letI : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
   t)

private theorem curvePlaceAffineLineEvaluation_bijective :
    withUpper% Function.Bijective
      (weilRestrictionEvaluation K L (CurvePlaceAdeleRing k K) (CurvePlaceAdeleRing k L)
        (curvePlaceAdeleInclusion k K L)
        (CurvePlaceProjectiveWeilAdeleEvaluation.adeleInclusion_compatible k K L)
        (ringTest L (MvPolynomial Unit L))) := withUpper% by
  let Y := ringTest L (MvPolynomial Unit L)
  let j := (projectiveLineAffineInclusion L).left
  let s := algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)
  have : FiniteDimensional k⟮s⟯ K :=
    FunctionField.FiniteDimensional.adjoin_algebraMap_X
  let M := curvePlaceFunctionFieldProjectiveModel k K L ∅ ∅ Y.left 1 j
  let E := curvePlacePrincipalExceptional k K s (M.denominator : K)
  let := curvePlaceSpreadAdelePointTopology k K E
    (CurvePlaceProjectiveWeilAdeleHomeomorph.lowerModel k K L s ∅ ∅ Y.left 1 j M) _
    (CurvePlaceProjectiveWeilAdeleHomeomorph.lowerGenericFiberIso
      k K L s ∅ ∅ Y.left 1 j M)
  let := curvePlaceSpreadAdelePointTopology k L
    (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
    (CurvePlaceProjectiveWeilAdeleHomeomorph.upperGenericFiberIso
      k K L s ∅ ∅ Y.left 1 j M)
  let H := CurvePlaceProjectiveWeilAdeleHomeomorph.adelicPointHomeomorph
    k K L s ∅ ∅ Y.left 1 j M
  have h := H.toEquiv.bijective
  have he :
      (⇑H.toEquiv) =
      CurvePlaceProjectiveWeilAdeleEvaluation.adelicEvaluation k K L Y.left 1 j := by
    funext p
    exact CurvePlaceProjectiveWeilAdeleEvaluation.adelicPointHomeomorph_eq_evaluation
      k K L Y.left 1 j s ∅ ∅ M p
  rw [he] at h
  have hY : CurvePlaceProjectiveWeilAdeleHomeomorph.originalScheme L Y.left 1 j = Y := by
    change Over.mk (j ≫ projectiveSpaceToSpec L 1) = Over.mk Y.hom
    exact congrArg Over.mk (projectiveLineAffineInclusion L).w
  have : LocallyOfFiniteType
      (CurvePlaceProjectiveWeilAdeleHomeomorph.originalScheme L Y.left 1 j).hom := by
    rw [hY]
    infer_instance
  have : IsSeparated
      (CurvePlaceProjectiveWeilAdeleHomeomorph.originalScheme L Y.left 1 j).hom := by
    rw [hY]
    infer_instance
  change Function.Bijective
    (weilRestrictionEvaluation K L (CurvePlaceAdeleRing k K) (CurvePlaceAdeleRing k L)
      (curvePlaceAdeleInclusion k K L)
      (CurvePlaceProjectiveWeilAdeleEvaluation.adeleInclusion_compatible k K L)
      (CurvePlaceProjectiveWeilAdeleHomeomorph.originalScheme L Y.left 1 j)) at h
  have transport (Z : Over (Spec (CommRingCat.of L)))
      [LocallyOfFiniteType Z.hom] [IsSeparated Z.hom] (hZ : Z = Y)
      (hb : Function.Bijective
        (weilRestrictionEvaluation K L (CurvePlaceAdeleRing k K) (CurvePlaceAdeleRing k L)
          (curvePlaceAdeleInclusion k K L)
          (CurvePlaceProjectiveWeilAdeleEvaluation.adeleInclusion_compatible k K L) Z)) :
      Function.Bijective
        (weilRestrictionEvaluation K L (CurvePlaceAdeleRing k K) (CurvePlaceAdeleRing k L)
          (curvePlaceAdeleInclusion k K L)
          (CurvePlaceProjectiveWeilAdeleEvaluation.adeleInclusion_compatible k K L) Y) := by
    subst Z
    exact hb
  exact transport _ hY h

/-- The canonical tensor map for all curve-place adeles is bijective,
including for inseparable finite extensions. -/
theorem curvePlaceAdeleTensorMap_bijective :
    withUpper% Function.Bijective (curvePlaceAdeleTensorMap k K L) := withUpper% by
  exact affineLineTensorMap_bijective K L (CurvePlaceAdeleRing k K) (CurvePlaceAdeleRing k L)
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion L 1
      (projectiveLineAffineInclusion L).left)
    (curvePlaceAdeleInclusion k K L)
    (CurvePlaceProjectiveWeilAdeleEvaluation.adeleInclusion_compatible k K L)
    (curvePlaceAdeleTensorMap k K L) (curvePlaceAdeleTensorMap_one_tmul)
    (curvePlaceAffineLineEvaluation_bijective k K L)

/-- The original full curve-place adelic tensor map as an `L`-algebra equivalence. -/
def curvePlaceAdeleTensorEquiv :
    withUpper% L ⊗[K] CurvePlaceAdeleRing k K ≃ₐ[L] CurvePlaceAdeleRing k L := withUpper%
  AlgEquiv.ofBijective (curvePlaceAdeleTensorMap k K L)
    (curvePlaceAdeleTensorMap_bijective k K L)

/-- The equivalence has exactly the original canonical algebra homomorphism. -/
@[simp] theorem curvePlaceAdeleTensorEquiv_toAlgHom :
    withUpper% (curvePlaceAdeleTensorEquiv k K L).toAlgHom =
      curvePlaceAdeleTensorMap k K L := withUpper% rfl

/-- Pure tensors evaluate by the principal scalar and the original adelic inclusion. -/
@[simp] theorem curvePlaceAdeleTensorEquiv_tmul (a : L) (x : CurvePlaceAdeleRing k K) :
    withUpper% curvePlaceAdeleTensorEquiv k K L (a ⊗ₜ[K] x) =
      algebraMap L (CurvePlaceAdeleRing k L) a * curvePlaceAdeleInclusion k K L x :=
  withUpper% rfl

end FunctionField

end Langlands.Global
