import Langlands.Geometry.Building.KPWeilRestrictionUnitKernel
import Langlands.GroupScheme.Torus.WeilRestrictionNormCoordinates

/-! # Character kernels for products of Weil restrictions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Plancherel.TorusNormKernel Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.WeilGm

section Decomposition

variable (k L B : Type u) [Field k] [Field L] [Algebra k L]
  [CommRing B] [Algebra k B] [Module.Finite k B] [Module.Projective k B]
  (J : Type u) [Fintype J] (e : L ⊗[k] B ≃ₐ[L] (J → L))

local notation "W" => groupScheme (CommRingCat.of k) B
local notation "W_L" =>
  CommGroupScheme.toGrp (Functor.obj
    (CommGroupScheme.baseChange (GaloisPointComparison.baseMap k L))
      (commGroupScheme (CommRingCat.of k) B))

/-- A splitting of the coefficient algebra gives the same direct tensor-unit
coordinates on actual rational points. -/
theorem decomposition_rational_coordinate
    (x : rationalPoints W_L) (j : J) :
    splitTorus.affinePointsEquiv J (𝟙 (Spec (CommRingCat.of L)))
        (rationalPoints.map (CommGroupScheme.groupHom
          (commDecompositionIso (CommRingCat.of k) (CommRingCat.of L) B J e).hom) x) j =
      MulEquiv.piUnits
        (Units.map ((Algebra.TensorProduct.comm k B L).toRingEquiv.trans e.toRingEquiv).toMonoidHom
          (extensionUnitsEquiv k L B x)) j := by
  let T := (algSpec (CommRingCat.of L)).obj (op (CommAlgCat.of L L))
  let _ := restrictedSectionsAlgebra (CommRingCat.of k) (CommRingCat.of L) T
  let _ := restrictedSectionsScalarTower (CommRingCat.of k) (CommRingCat.of L) T
  let y := rationalCoeffEquiv L W_L x
  let c := (Corepresented.affineSectionsIso (R := CommRingCat.of L)
    (CommAlgCat.of L L)).hom.hom
  have c_eq (s) : c s = (Scheme.ΓSpecIso (CommRingCat.of L)).hom s :=
    DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom
      (R := CommRingCat.of L) (CommAlgCat.of L L)) s
  have hp : GroupScheme.baseChangePointsEquiv
      (GaloisPointComparison.baseMap k L) W T y =
        (specRestrictIso k L L).hom ≫ baseChangeCoeffEquiv k L W x := by
    have he : y = pointE k L L W (baseChangeCoeffEquiv k L W x) :=
      (pointE_baseChangeCoeffEquiv (F := k) (E := L) (T := W) x).symm
    exact (congrArg (GroupScheme.baseChangePointsEquiv
      (GaloisPointComparison.baseMap k L) W T) he).trans
        (baseChangePointsEquiv_pointE k L L W _)
  have hsplitPoint := congrFun
    (commDecompositionIso_hom_points (CommRingCat.of k) (CommRingCat.of L)
      B J e T y) j
  have hc := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor (CommRingCat.of k) B) (corepresentableBy (CommRingCat.of k) B)
    (CommAlgCat.of k L) (baseChangeCoeffEquiv k L W x)
  change Units.map (Algebra.TensorProduct.lTensor (S := B) B
      (Corepresented.affineSectionsIso (R := CommRingCat.of k)
        (CommAlgCat.of k L)).hom.hom).toMonoidHom _ =
    extensionUnitsEquiv k L B x at hc
  have hleft :
      splitTorus.affinePointsEquiv J (𝟙 (Spec (CommRingCat.of L)))
          (rationalPoints.map (CommGroupScheme.groupHom
            (commDecompositionIso (CommRingCat.of k) (CommRingCat.of L) B J e).hom) x) j =
        Units.map c.toMonoidHom
          (splitTorus.pointsEquiv J T
            (y ≫ (CommGroupScheme.groupHom
              (commDecompositionIso (CommRingCat.of k)
                (CommRingCat.of L) B J e).hom).hom.hom) j) := by
    change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))
      ((x ≫ (CommGroupScheme.groupHom
        (commDecompositionIso (CommRingCat.of k) (CommRingCat.of L) B J e).hom).hom.hom) ≫
        (CategoryTheory.Limits.Pi.π (fun _ : J =>
          (Gm (Spec (CommRingCat.of L))).toGrp) j).hom.hom) = _
    rw [← GaloisPoint.gm_units_rationalCoeffEquiv L]
    rw [rationalCoeffEquiv_comp, rationalCoeffEquiv_comp, splitTorus.pointsEquiv_apply]
    apply Units.ext
    change (Scheme.ΓSpecIso (CommRingCat.of L)).hom _ = c _
    exact (c_eq _).symm
  rw [hleft, hsplitPoint, ← hc]
  apply Units.ext
  change c (decompositionTensorEquiv k L B
    (restrictedSections (CommRingCat.of k) (CommRingCat.of L) T) J e
      ((pointsEquiv (CommRingCat.of k) B
        ((Over.map (GaloisPointComparison.baseMap k L)).obj T))
          (GroupScheme.baseChangePointsEquiv
            (GaloisPointComparison.baseMap k L) W T y)) j) = _
  rw [hp, pointsEquiv_naturality]
  suffices hall : ∀ z,
      c (decompositionTensorEquiv k L B
          (restrictedSections (CommRingCat.of k) (CommRingCat.of L) T) J e
        (Algebra.TensorProduct.lTensor (S := B) B
          ((algΓ (CommRingCat.of k)).map (specRestrictIso k L L).hom).unop.hom z) j) =
      ((Algebra.TensorProduct.comm k B L).toRingEquiv.trans e.toRingEquiv)
        (Algebra.TensorProduct.lTensor (S := B) B
          (Corepresented.affineSectionsIso (R := CommRingCat.of k)
            (CommAlgCat.of k L)).hom.hom z) j by
    exact hall _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, decompositionTensorEquiv_tmul, RingEquiv.trans_apply]
      have hb : c (((algΓ (CommRingCat.of k)).map
          (specRestrictIso k L L).hom).unop.hom b) =
        (Corepresented.affineSectionsIso (R := CommRingCat.of k)
          (CommAlgCat.of k L)).hom.hom b := by
        rw [c_eq]
        exact (DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom
          (R := CommRingCat.of k) (CommAlgCat.of k L)) b).symm
      rw [map_smul, hb]
      change e (1 ⊗ₜ a) j *
        (Corepresented.affineSectionsIso (R := CommRingCat.of k)
          (CommAlgCat.of k L)).hom.hom b =
        e ((Corepresented.affineSectionsIso (R := CommRingCat.of k)
          (CommAlgCat.of k L)).hom.hom b ⊗ₜ a) j
      have ht (l : L) : l ⊗ₜ[k] a = l • ((1 : L) ⊗ₜ[k] a) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht ((Corepresented.affineSectionsIso (R := CommRingCat.of k)
        (CommAlgCat.of k L)).hom.hom b), map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_comm (e ((1 : L) ⊗ₜ[k] a) j)
        ((Corepresented.affineSectionsIso (R := CommRingCat.of k)
          (CommAlgCat.of k L)).hom.hom b)
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

include e in
/-- Character-kernel membership for any split coefficient algebra is
coordinatewise unit valuation in the direct tensor model. -/
theorem mem_decomposition_characterValuationKernel
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
    (x : rationalPoints W_L) :
    x ∈ characterValuationKernel v W_L ↔
      ∀ j, v (MulEquiv.piUnits
        (Units.map ((Algebra.TensorProduct.comm k B L).toRingEquiv.trans e.toRingEquiv).toMonoidHom
          (extensionUnitsEquiv k L B x)) j : L) = 1 := by
  let d := commDecompositionIso (CommRingCat.of k) (CommRingCat.of L) B J e
  constructor
  · intro hx j
    have hmap := map_characterValuationKernel_le v (CommGroupScheme.groupHom d.hom)
      ⟨x, hx, rfl⟩
    have hcoord := (mem_split_characterValuationKernel L v J _).mp hmap j
    rw [decomposition_rational_coordinate k L B J e x j] at hcoord
    exact hcoord
  · intro hx
    have hmap : rationalPoints.map (CommGroupScheme.groupHom d.hom) x ∈
        characterValuationKernel v (splitTorus (Spec (CommRingCat.of L)) J) := by
      rw [mem_split_characterValuationKernel]
      intro j
      rw [decomposition_rational_coordinate k L B J e x j]
      exact hx j
    have hback := map_characterValuationKernel_le v (CommGroupScheme.groupHom d.inv)
      ⟨_, hmap, rfl⟩
    have hd : rationalPoints.map (CommGroupScheme.groupHom d.inv)
        (rationalPoints.map (CommGroupScheme.groupHom d.hom) x) = x := by
      change (x ≫ (CommGroupScheme.groupHom d.hom).hom.hom) ≫
        (CommGroupScheme.groupHom d.inv).hom.hom = x
      rw [← comp_groupHom_comp, d.hom_inv_id]
      rfl
    rwa [hd] at hback

end Decomposition

section Product

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {I : Type u} [Fintype I] [DecidableEq I] (E : I → IntermediateField k L)

/-- Uncurrying a family of coefficient functions as an algebra equivalence. -/
def productEmbeddingUncurry :
    (∀ i, (E i →ₐ[k] L) → L) ≃ₐ[L] ((Σ i, E i →ₐ[k] L) → L) where
  __ := (Equiv.piCurry fun i (_ : E i →ₐ[k] L) => L).symm
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The product tensor decomposition, with its two indices combined into one. -/
def productEmbeddingDecomposition :
    L ⊗[k] (∀ i, E i) ≃ₐ[L] ((Σ i, E i →ₐ[k] L) → L) :=
  ((Algebra.TensorProduct.piRight k L L (fun i => E i)).trans
    (AlgEquiv.piCongrRight fun i => separableEmbeddingDecomposition k (E i) L
      (intermediate_minpoly_splits k L (E i)))).trans
    (productEmbeddingUncurry k L E)

/-- The generic decomposition coordinates are precisely the shared product
tensor-embedding coordinates. -/
theorem productEmbeddingDecomposition_units
    (z : ((∀ i, E i) ⊗[k] L)ˣ) (i : I) (τ : E i →ₐ[k] L) :
    MulEquiv.piUnits
        (Units.map ((Algebra.TensorProduct.comm k (∀ i, E i) L).toRingEquiv.trans
          (productEmbeddingDecomposition k L E).toRingEquiv).toMonoidHom z) ⟨i, τ⟩ =
      productTensorEmbeddingUnitsEquiv k L E z i τ := rfl

/-- The character kernel of the base-changed product Weil restriction is
coordinatewise unit valuation in the shared tensor model. -/
theorem mem_product_extension_characterValuationKernel
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
    (x : rationalPoints (baseChanged k L
      (groupScheme (CommRingCat.of k) (∀ i, E i)))) :
    x ∈ characterValuationKernel v (baseChanged k L
      (groupScheme (CommRingCat.of k) (∀ i, E i))) ↔
      ∀ (i : I) (τ : E i →ₐ[k] L),
        v (productTensorEmbeddingUnitsEquiv k L E
          (extensionUnitsEquiv k L (∀ i, E i) x) i τ : L) = 1 := by
  have hd := mem_decomposition_characterValuationKernel k L (∀ i, E i)
    (Σ i, E i →ₐ[k] L) (productEmbeddingDecomposition k L E) v x
  constructor
  · intro h i τ
    exact hd.mp h ⟨i, τ⟩
  · intro h
    apply hd.mpr
    intro j
    exact h j.1 j.2

/-- Extending a product-algebra unit gives its embedding values in the shared
product coordinates. -/
theorem productTensorEmbeddingUnitsEquiv_includeLeft
    (z : (∀ i, E i)ˣ) (i : I) (τ : E i →ₐ[k] L) :
    productTensorEmbeddingUnitsEquiv k L E
        (Units.map (Algebra.TensorProduct.includeLeft :
          (∀ i, E i) →ₐ[k] (∀ i, E i) ⊗[k] L).toMonoidHom z) i τ =
      Units.map τ.toMonoidHom (MulEquiv.piUnits z i) := by
  apply Units.ext
  change productTensorEmbeddingEquiv k L E ((z : ∀ i, E i) ⊗ₜ[k] (1 : L)) i τ =
    τ ((z : ∀ i, E i) i)
  simp

/-- A bounded ground-field point has unit valuation in each intermediate-field
coordinate, as viewed in the common Galois extension. -/
theorem product_coordinate_valuation_eq_one_of_mem
    {Γk ΓL : Type*} [LinearOrderedCommGroupWithZero Γk]
    [LinearOrderedCommGroupWithZero ΓL]
    (vk : Valuation k Γk) (vL : Valuation L ΓL) [vk.HasExtension vL]
    (hinv : ∀ (σ : L ≃ₐ[k] L) (z : L), vL (σ z) = vL z)
    (x : rationalPoints (groupScheme (CommRingCat.of k) (∀ i, E i)))
    (hx : x ∈ characterValuationKernel vk (groupScheme (CommRingCat.of k) (∀ i, E i)))
    (i : I) :
    vL (algebraMap (E i) L
      (MulEquiv.piUnits (rationalUnitsEquiv k (∀ i, E i) x) i : E i)) = 1 := by
  let _ : IsAffine (groupScheme (CommRingCat.of k) (∀ i, E i)).X.left := by
    change IsAffine (Spec _)
    infer_instance
  have hext := characterValuationKernel_le_comap vk vL hinv
    (groupScheme (CommRingCat.of k) (∀ i, E i)) hx
  have hcoord := (mem_product_extension_characterValuationKernel k L E vL _).mp
    hext i (E i).val
  rw [extensionUnitsEquiv_extend, productTensorEmbeddingUnitsEquiv_includeLeft] at hcoord
  exact hcoord

end Product

end Langlands.GroupScheme.WeilGm
