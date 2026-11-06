import Langlands.Geometry.Building.KPIntermediateUnitNorm
import Langlands.Geometry.Building.KPWeilProductUnitKernel
import Langlands.GroupScheme.Torus.WeilRestrictionSupportedNorm

/-! # Bounded norm lifts for finite products of Weil restrictions over `K` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 2

namespace Langlands.GroupScheme.WeilGm

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {I : Type u} [Fintype I] [DecidableEq I] (E : I → IntermediateField k L)
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)

/-- A point supported at inclusion embeddings is bounded when its supported units are. -/
theorem inclusionSupportedPoint_mem_characterValuationKernel
    (b : I → Lˣ) (hb : ∀ i, v (b i : L) = 1) :
    inclusionSupportedPoint k L E b ∈
      Langlands.Geometry.Building.characterValuationKernel v
        (baseChanged k L (groupScheme (CommRingCat.of k) (∀ i, E i))) := by
  classical
  apply (mem_product_extension_characterValuationKernel k L E v _).mpr
  intro i τ
  simp only [inclusionSupportedPoint, MulEquiv.apply_symm_apply,
    inclusionSupportedTensorUnit_coordinate]
  by_cases h : (E i).val = τ
  · subst τ
    simpa only [Pi.mulSingle_eq_same] using hb i
  · simp [Pi.mulSingle_eq_of_ne (Ne.symm h)]

end Langlands.GroupScheme.WeilGm

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
  {I : Type u} [Fintype I] [DecidableEq I]
  (E : I → IntermediateField (UnramifiedClosure F) L)

local instance : ∀ i, Algebra (UnramifiedClosure F) (E i) :=
  fun i => (E i).toSubalgebra.algebra

local instance : ∀ i, Module (UnramifiedClosure F) (E i) :=
  fun i => @Algebra.toModule _ _ _ _ (E i).toSubalgebra.algebra

local instance : ∀ i, SMul (UnramifiedClosure F) (E i) :=
  fun i => (E i).toSubalgebra.algebra.toSMul

local instance : ∀ i, FiniteDimensional (UnramifiedClosure F) (E i) :=
  fun i => IntermediateField.finiteDimensional_left (E i)

local instance : FiniteDimensional (UnramifiedClosure F) (∀ i, E i) :=
  Module.Finite.pi

local instance : Module.Projective (UnramifiedClosure F) (∀ i, E i) :=
  Module.Projective.of_basis (Module.Basis.ofVectorSpace (UnramifiedClosure F) (∀ i, E i))

set_option quotPrecheck false

local notation "K" => UnramifiedClosure F
local notation "W" => WeilGm.commGroupScheme (CommRingCat.of K) (∀ i, E i)

local instance : IsAffine (W).X.left := by
  change IsAffine (Spec _)
  infer_instance

/-- Coordinatewise bounded relative norm preimages of a bounded ground-field point. -/
def weilProductUnitNormLifts
    (x : characterValuationKernel (fixedFieldValuation F) (W).toGrp) (i : I) : Lˣ :=
  intermediateUnitNormLift F L (E i)
    (MulEquiv.piUnits (WeilGm.rationalUnitsEquiv K (∀ i, E i) x.val) i)
    (WeilGm.product_coordinate_valuation_eq_one_of_mem K L E
      (fixedFieldValuation F) (intermediateValuation F L)
      (intermediateValuation_conjugate F L) x.val x.property i)

theorem weilProductUnitNormLifts_valuation
    (x : characterValuationKernel (fixedFieldValuation F) (W).toGrp) (i : I) :
    intermediateValuation F L (weilProductUnitNormLifts F L E x i : L) = 1 :=
  intermediateUnitNormLift_valuation F L (E i) _ _

theorem weilProductUnitNormLifts_norm
    (x : characterValuationKernel (fixedFieldValuation F) (W).toGrp) (i : I) :
    Units.map (Algebra.norm (E i)) (weilProductUnitNormLifts F L E x i) =
      MulEquiv.piUnits (WeilGm.rationalUnitsEquiv K (∀ i, E i) x.val) i :=
  intermediateUnitNormLift_norm F L (E i) _ _

/-- A bounded rational point whose norm is the given bounded ground-field Weil point. -/
def weilProductBoundedNormLift
    (x : characterValuationKernel (fixedFieldValuation F) (W).toGrp) :
    characterValuationKernel (intermediateValuation F L)
      (baseChanged K L (W).toGrp) :=
  ⟨WeilGm.inclusionSupportedPoint K L E (weilProductUnitNormLifts F L E x),
    WeilGm.inclusionSupportedPoint_mem_characterValuationKernel K L E
      (intermediateValuation F L) _ (weilProductUnitNormLifts_valuation F L E x)⟩

/-- The constructed bounded point has the prescribed actual rational norm. -/
theorem rationalNorm_weilProductBoundedNormLift
    (x : characterValuationKernel (fixedFieldValuation F) (W).toGrp) :
    rationalNorm K L W (weilProductBoundedNormLift F L E x).val = x.val := by
  apply (WeilGm.rationalUnitsEquiv K (∀ i, E i)).injective
  apply MulEquiv.piUnits.injective
  funext i
  change MulEquiv.piUnits (WeilGm.rationalUnitsEquiv K (∀ i, E i)
    (rationalNorm K L W (WeilGm.inclusionSupportedPoint K L E
      (weilProductUnitNormLifts F L E x)))) i = _
  rw [WeilGm.rationalNorm_inclusionSupportedPoint]
  exact weilProductUnitNormLifts_norm F L E x i

/-- Every bounded point of the product Weil restriction is a norm of a bounded point. -/
theorem weilProductBoundedRationalNorm_surjective :
    Function.Surjective (boundedRationalNorm K L (fixedFieldValuation F)
      (intermediateValuation F L) (intermediateValuation_conjugate F L) W) := by
  intro x
  exact ⟨weilProductBoundedNormLift F L E x,
    Subtype.ext (rationalNorm_weilProductBoundedNormLift F L E x)⟩

/-- For the product Weil restriction over `K`, the norm Iwahori is the bounded subgroup. -/
theorem weilProduct_torusNormIwahori_eq_characterValuationKernel :
    torusNormIwahori K L (intermediateValuation F L) W =
      characterValuationKernel (fixedFieldValuation F) (W).toGrp := by
  apply le_antisymm (torusNormIwahori_le_characterValuationKernel
    (fixedFieldValuation F) (intermediateValuation F L)
    (intermediateValuation_conjugate F L) W)
  intro x hx
  exact (mem_torusNormIwahori K L).mpr
    ⟨(weilProductBoundedNormLift F L E ⟨x, hx⟩).val,
      (weilProductBoundedNormLift F L E ⟨x, hx⟩).property,
      rationalNorm_weilProductBoundedNormLift F L E ⟨x, hx⟩⟩

end Langlands.Geometry.Building
