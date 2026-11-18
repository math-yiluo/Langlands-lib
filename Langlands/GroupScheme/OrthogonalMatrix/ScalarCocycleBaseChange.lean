import Langlands.GroupScheme.OrthogonalMatrix.ScalarCocycle
import Langlands.LinearAlgebra.OrthogonalCocycleScalarExtension

/-! # Scalar orthogonal cocycles on the pullback cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.OrthogonalMatrix

open Quaternionic
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LinearAlgebra.OrthogonalCocycleDescent

variable {F K L : Type u} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
  {n : ℕ} (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "Gq" => FirstKindInvolution.isometryGroup (FirstKindInvolution.scalar F) q
local notation "R" => K ⊗[F] L
local notation "bFK" => Spec.algebraMap F K
local notation "U" => GaloisCocycle.cover F L
local notation "V" => Functor.obj (Over.pullback bFK) U
local notation "T" => ringTest K R
local notation "T₀" => ringTest F R
local notation "Ralg" => CommAlgCat.of (CommRingCat.of F) R
local notation "Kalg" => CommAlgCat.of (CommRingCat.of K) R
local notation "j" => (Algebra.TensorProduct.includeRight : L →ₐ[F] R)

/-- The polar matrix chart on points of the actual base-changed orthogonal group over `K ⊗[F] L`. -/
def scalarTensorMatrixPoint : ((baseChange bFK).obj Gq).affinePoints Kalg →* GL (Fin n) R :=
  (scalarMatrixPoint q Ralg).comp (affinePointsBaseChangeMulEquiv F K R Gq).symm.toMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- A cochain on the actual pullback cover yields a matrix twist on the coefficient tensor ring. -/
theorem exists_tensor_matrix_twist [CharZero F] (ξ ζ : Cocycle Gq U)
    (h : let r := (Over.mapPullbackAdj bFK).counit.app U
      (ξ.baseChange bFK V r).Cohomologous (ζ.baseChange bFK V r)) :
    ∃ a : GL (Fin n) R,
      gramTransform a ((FirstKindInvolution.polar (FirstKindInvolution.scalar F) q).map
          (algebraMap F R)) =
        (FirstKindInvolution.polar (FirstKindInvolution.scalar F) q).map (algebraMap F R) ∧
      ∀ σ : L ≃ₐ[F] L,
        Matrix.GeneralLinearGroup.map (j).toRingHom ((scalarMatrixCocycle q ζ).toFun σ) =
          a⁻¹ * Matrix.GeneralLinearGroup.map (j).toRingHom ((scalarMatrixCocycle q ξ).toFun σ) *
            Matrix.GeneralLinearGroup.map (tensorGaloisMap K σ).toRingHom a := by
  obtain ⟨f, hf⟩ := h
  let r := (Over.mapPullbackAdj bFK).counit.app U
  let e := ringTestRestrictScalarsIso F K R
  let E := ringPointBaseChangeEquiv F K R U
  let d : T₀ ⟶ U := ringTestMap F j
  let x : T ⟶ V := E d
  let ρ := (affinePointsBaseChangeMulEquiv F K R Gq).symm
  let s (σ : L ≃ₐ[F] L) : T ⟶ T := ringTestMap K (tensorGaloisMap K σ)
  let t (σ : L ≃ₐ[F] L) : T₀ ⟶ T₀ :=
    ringTestMap F ((tensorGaloisMap K σ).restrictScalars F)
  have hproj (z : T ⟶ V) : e.inv ≫ ((Over.map bFK).map z ≫ r) = E.symm z := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rfl
  have hbase (ν : Cocycle Gq U) (z w : T ⟶ V) :
      ρ ((ν.baseChange bFK V r).toFun z w) = ν.toFun (E.symm z) (E.symm w) := by
    have hp := congrArg (fun p => p.left) (ν.baseChange_toFun bFK V r z w)
    rw [baseChangePointsEquiv_left] at hp
    have hn := ν.naturality e.inv ((Over.map bFK).map z ≫ r) ((Over.map bFK).map w ≫ r)
    rw [hproj, hproj] at hn
    apply Over.OverMorphism.ext
    rw [affinePointsBaseChangeMulEquiv_symm_left, hp, hn, Over.comp_left,
      ringTestRestrictScalarsIso_inv_left]
    exact (Category.id_comp _).symm
  have hcomp (σ : L ≃ₐ[F] L) : t σ ≫ d = d ≫ GaloisCocycle.arrow F L σ := by
    have hσ : ringTestMap F σ.toAlgHom = GaloisCocycle.arrow F L σ := by
      apply Over.OverMorphism.ext
      rfl
    rw [← hσ]
    dsimp only [t, d]
    rw [← ringTestMap_comp, ← ringTestMap_comp, tensorGaloisMap_comp_includeRight]
  have hsecond (σ : L ≃ₐ[F] L) : E.symm (s σ ≫ x) = d ≫ GaloisCocycle.arrow F L σ := by
    rw [← hcomp σ]
    apply Over.OverMorphism.ext
    change ((ringPointBaseChangeEquiv F K R U).symm (s σ ≫ E d)).left = _
    simp only [E, ringPointBaseChangeEquiv_symm_left, Over.comp_left, Category.assoc,
      ringPointBaseChangeEquiv_left_fst]
    rfl
  have hval (ν : Cocycle Gq U) (σ : L ≃ₐ[F] L) :
      ρ ((ν.baseChange bFK V r).toFun x (s σ ≫ x)) =
        affinePointMap Gq (CommAlgCat.ofHom j) (GaloisCocycle.value ν σ) := by
    rw [hbase, hsecond, show E.symm x = d from E.symm_apply_apply d]
    calc
      _ = d ≫ GaloisCocycle.value ν σ := by
        simpa only [Category.comp_id, GaloisCocycle.value] using
          ν.naturality d (𝟙 U) (GaloisCocycle.arrow F L σ)
      _ = _ := by
        apply Over.OverMorphism.ext
        rfl
  let p := ρ (x ≫ f)
  have hcochain (σ : L ≃ₐ[F] L) : ρ ((s σ ≫ x) ≫ f) =
      affinePointMap Gq (CommAlgCat.ofHom ((tensorGaloisMap K σ).restrictScalars F)) p := by
    apply Over.OverMorphism.ext
    simp only [ρ, affinePointsBaseChangeMulEquiv_symm_left, affinePointMap_apply,
      Over.comp_left, Category.assoc, p]
    rfl
  let a := scalarTensorMatrixPoint q (x ≫ f)
  refine ⟨a, scalarMatrixPoint_preserves q Ralg p, fun σ => ?_⟩
  have key := congrArg (fun w => scalarMatrixPoint q Ralg (ρ w)) (hf x (s σ ≫ x))
  simp only [Cocycle.twist, map_mul, map_inv, hcochain] at key
  change scalarMatrixPoint q Ralg (ρ ((ζ.baseChange bFK V r).toFun x (s σ ≫ x))) =
    (scalarMatrixPoint q Ralg p)⁻¹ *
      scalarMatrixPoint q Ralg (ρ ((ξ.baseChange bFK V r).toFun x (s σ ≫ x))) *
      scalarMatrixPoint q Ralg
        (affinePointMap Gq (CommAlgCat.ofHom ((tensorGaloisMap K σ).restrictScalars F)) p) at key
  rw [hval ζ σ, hval ξ σ,
    scalarMatrixPoint_naturality q (CommAlgCat.ofHom j) (GaloisCocycle.value ζ σ),
    scalarMatrixPoint_naturality q (CommAlgCat.ofHom j) (GaloisCocycle.value ξ σ),
    scalarMatrixPoint_naturality q (CommAlgCat.ofHom ((tensorGaloisMap K σ).restrictScalars F)) p]
    at key
  exact key

end Langlands.GroupScheme.OrthogonalMatrix
