import Langlands.Geometry.Building.KPCharacterValuationExtension
import Langlands.Geometry.Building.KPSplitUnitKernel
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.Torus.WeilRestrictionSeparable

/-! # Unit coordinates in finite-separable Weil restrictions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Plancherel.TorusNormKernel
open Langlands.Algebra.SeparableTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace Langlands.Geometry.Building

/-- A split-torus point is in the character kernel exactly when all its
coordinates have unit valuation. -/
theorem mem_split_characterValuationKernel
    (k : Type u) [Field k] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation k Γ) (I : Type u) [Fintype I]
    (x : rationalPoints (splitTorus (Spec (CommRingCat.of k)) I)) :
    x ∈ characterValuationKernel v (splitTorus (Spec (CommRingCat.of k)) I) ↔
      ∀ i, v (splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of k))) x i : k) = 1 := by
  constructor
  · intro hx i
    exact (mem_gm_characterValuationKernel k v _).mp
      (map_characterValuationKernel_le v
        (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i))
        ⟨x, hx, rfl⟩)
  · intro hx
    rw [splitPoint_decomposition k I x]
    apply Subgroup.prod_mem
    intro i _
    have hi : rationalPoints.map
        (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i)) x ∈
          characterValuationKernel v (Gm (Spec (CommRingCat.of k))).toGrp :=
      (mem_gm_characterValuationKernel k v _).mpr (hx i)
    exact map_characterValuationKernel_le v
      (CommGroupScheme.groupHom (splitTorus.single (Spec (CommRingCat.of k)) I i))
      ⟨_, hi, rfl⟩

end Langlands.Geometry.Building

namespace Langlands.GroupScheme.WeilGm

open Langlands.Geometry.Building

variable (k E L : Type u) [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra k L] [FiniteDimensional k E] [Algebra.IsSeparable k E]
  (hsplit : ∀ z : E, ((minpoly k z).map (algebraMap k L)).Splits)

local notation "W" => groupScheme (CommRingCat.of k) E
local notation "W_L" =>
  CommGroupScheme.toGrp (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k L))
    (commGroupScheme (CommRingCat.of k) E))

/-- On rational points, the canonical splitting has the direct tensor-evaluation
coordinates. -/
theorem embedding_rational_coordinate
    (x : rationalPoints W_L) (τ : E →ₐ[k] L) :
    splitTorus.affinePointsEquiv (E →ₐ[k] L) (𝟙 (Spec (CommRingCat.of L)))
        (rationalPoints.map
          (CommGroupScheme.groupHom (embeddingCommIso k E L (embeddingEvaluationStatement k E L hsplit)).hom) x) τ =
      Units.map (tensorCoordinate (AlgHom.id k L) τ).toMonoidHom
        (extensionUnitsEquiv k L E x) := by
  let T := (algSpec (CommRingCat.of L)).obj (op (CommAlgCat.of L L))
  let y := rationalCoeffEquiv L W_L x
  let c := (Corepresented.affineSectionsIso (R := CommRingCat.of L)
    (CommAlgCat.of L L)).hom.hom
  have c_eq (s) : c s = (Scheme.ΓSpecIso (CommRingCat.of L)).hom s :=
    DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom
      (R := CommRingCat.of L) (CommAlgCat.of L L)) s
  have hp :
      GroupScheme.baseChangePointsEquiv (GaloisPointComparison.baseMap k L) W T y =
        (specRestrictIso k L L).hom ≫ baseChangeCoeffEquiv k L W x := by
    have he : y = pointE k L L W (baseChangeCoeffEquiv k L W x) :=
      (pointE_baseChangeCoeffEquiv (F := k) (E := L) (T := W) x).symm
    exact (congrArg (GroupScheme.baseChangePointsEquiv
      (GaloisPointComparison.baseMap k L) W T) he).trans
        (baseChangePointsEquiv_pointE k L L W _)
  have hsplitPoint := congrFun
    (embeddingCommIso_hom_points k E L
      (embeddingEvaluationStatement k E L hsplit) T y) τ
  rw [embeddingPointsEquiv_apply, hp, pointsEquiv_naturality] at hsplitPoint
  have hc := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor (CommRingCat.of k) E) (corepresentableBy (CommRingCat.of k) E)
    (CommAlgCat.of k L) (baseChangeCoeffEquiv k L W x)
  change Units.map (Algebra.TensorProduct.lTensor (S := E) E
      (Corepresented.affineSectionsIso (R := CommRingCat.of k)
        (CommAlgCat.of k L)).hom.hom).toMonoidHom _ =
    extensionUnitsEquiv k L E x at hc
  have hleft :
      splitTorus.affinePointsEquiv (E →ₐ[k] L) (𝟙 (Spec (CommRingCat.of L)))
          (rationalPoints.map
            (CommGroupScheme.groupHom (embeddingCommIso k E L (embeddingEvaluationStatement k E L hsplit)).hom) x) τ =
        Units.map c.toMonoidHom
          (splitTorus.pointsEquiv (E →ₐ[k] L) T
            (y ≫ (CommGroupScheme.groupHom
              (embeddingCommIso k E L (embeddingEvaluationStatement k E L hsplit)).hom).hom.hom) τ) := by
    change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))
      ((x ≫ (CommGroupScheme.groupHom (embeddingCommIso k E L (embeddingEvaluationStatement k E L hsplit)).hom).hom.hom) ≫
        (CategoryTheory.Limits.Pi.π (fun _ : E →ₐ[k] L =>
          (Gm (Spec (CommRingCat.of L))).toGrp) τ).hom.hom) = _
    rw [← GaloisPoint.gm_units_rationalCoeffEquiv L]
    rw [rationalCoeffEquiv_comp, rationalCoeffEquiv_comp, splitTorus.pointsEquiv_apply]
    apply Units.ext
    change (Scheme.ΓSpecIso (CommRingCat.of L)).hom _ = c _
    exact (c_eq _).symm
  rw [hleft, hsplitPoint, ← hc]
  apply Units.ext
  change c (tensorCoordinate (embeddingCoefficientMap k L T) τ
      (Algebra.TensorProduct.lTensor (S := E) E
        ((algΓ (CommRingCat.of k)).map (specRestrictIso k L L).hom).unop.hom _)) =
    tensorCoordinate (AlgHom.id k L) τ
      (Algebra.TensorProduct.lTensor (S := E) E
        (Corepresented.affineSectionsIso (R := CommRingCat.of k)
          (CommAlgCat.of k L)).hom.hom _)
  suffices hall : ∀ z,
      c (tensorCoordinate (embeddingCoefficientMap k L T) τ
        (Algebra.TensorProduct.lTensor (S := E) E
          ((algΓ (CommRingCat.of k)).map (specRestrictIso k L L).hom).unop.hom z)) =
      tensorCoordinate (AlgHom.id k L) τ
        (Algebra.TensorProduct.lTensor (S := E) E
          (Corepresented.affineSectionsIso (R := CommRingCat.of k)
            (CommAlgCat.of k L)).hom.hom z) by
    exact hall _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, tensorCoordinate_tmul, map_mul]
      congr 1
      · exact c.commutes (τ a)
      · rw [c_eq]
        exact (DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom
          (R := CommRingCat.of k) (CommAlgCat.of k L)) b).symm
  | add a b ha hb => simp only [map_add, ha, hb]

include hsplit in
/-- Boundedness after a splitting extension is exactly unit valuation in each
canonical embedding coordinate of the direct tensor unit. -/
theorem mem_extension_characterValuationKernel
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
    (x : rationalPoints W_L) :
    x ∈ characterValuationKernel v W_L ↔
      ∀ τ : E →ₐ[k] L,
        v (Units.map (tensorCoordinate (AlgHom.id k L) τ).toMonoidHom
          (extensionUnitsEquiv k L E x) : L) = 1 := by
  classical
  let e := embeddingCommIso k E L (embeddingEvaluationStatement k E L hsplit)
  constructor
  · intro hx τ
    have hmap := map_characterValuationKernel_le v (CommGroupScheme.groupHom e.hom)
      ⟨x, hx, rfl⟩
    have hcoord := (mem_split_characterValuationKernel L v (E →ₐ[k] L) _).mp hmap τ
    rw [embedding_rational_coordinate k E L hsplit x τ] at hcoord
    exact hcoord
  · intro hx
    have hmap : rationalPoints.map (CommGroupScheme.groupHom e.hom) x ∈
        characterValuationKernel v (splitTorus (Spec (CommRingCat.of L)) (E →ₐ[k] L)) := by
      rw [mem_split_characterValuationKernel]
      intro τ
      rw [embedding_rational_coordinate k E L hsplit x τ]
      exact hx τ
    have hback := map_characterValuationKernel_le v (CommGroupScheme.groupHom e.inv)
      ⟨_, hmap, rfl⟩
    have he : rationalPoints.map (CommGroupScheme.groupHom e.inv)
        (rationalPoints.map (CommGroupScheme.groupHom e.hom) x) = x := by
      change (x ≫ (CommGroupScheme.groupHom e.hom).hom.hom) ≫
        (CommGroupScheme.groupHom e.inv).hom.hom = x
      rw [← comp_groupHom_comp, e.hom_inv_id]
      rfl
    rwa [he] at hback

section TensorKernel

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)

/-- Tensor units with valuation one in each embedding coordinate. -/
def tensorEmbeddingUnitKernel : Subgroup (E ⊗[k] L)ˣ :=
  ⨅ τ : E →ₐ[k] L,
    ((Units.map v.toMonoidHom).comp
      (Units.map (tensorCoordinate (AlgHom.id k L) τ).toMonoidHom)).ker

omit [FiniteDimensional k E] [Algebra.IsSeparable k E] in
theorem mem_tensorEmbeddingUnitKernel (z : (E ⊗[k] L)ˣ) :
    z ∈ tensorEmbeddingUnitKernel k E L v ↔
      ∀ τ : E →ₐ[k] L,
        v (Units.map (tensorCoordinate (AlgHom.id k L) τ).toMonoidHom z : L) = 1 := by
  simp only [tensorEmbeddingUnitKernel, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.comp_apply, Units.ext_iff, Units.coe_map, Units.val_one]
  rfl

/-- The actual character kernel in the direct embedding-unit coordinate model. -/
def extensionCharacterKernelEquiv :
    characterValuationKernel v W_L ≃* tensorEmbeddingUnitKernel k E L v where
  toFun x := ⟨extensionUnitsEquiv k L E x.val,
    (mem_tensorEmbeddingUnitKernel k E L v _).mpr
      ((mem_extension_characterValuationKernel k E L hsplit v x.val).mp x.property)⟩
  invFun z := ⟨(extensionUnitsEquiv k L E).symm z.val,
    (mem_extension_characterValuationKernel k E L hsplit v _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact (mem_tensorEmbeddingUnitKernel k E L v z.val).mp z.property)⟩
  left_inv x := Subtype.ext ((extensionUnitsEquiv k L E).symm_apply_apply x.val)
  right_inv z := Subtype.ext ((extensionUnitsEquiv k L E).apply_symm_apply z.val)
  map_mul' x y := Subtype.ext ((extensionUnitsEquiv k L E).map_mul x.val y.val)

end TensorKernel

end Langlands.GroupScheme.WeilGm
