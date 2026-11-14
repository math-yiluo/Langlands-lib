import Langlands.Geometry.Building.Kottwitz.TorusKottwitzLaw
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Independence of the torus norm square from the splitting field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

-- Between intermediate fields `L ⊆ M`, the module and scalar structures come from the given
-- algebra; searching other paths first times out.
attribute [local instance high] Algebra.toModule Algebra.toSMul

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPoint
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.TorusPointsTensorGalois

section Transfer

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- The order of a norm equals the order of the unit, when the normalized valuations are
compatible with the norm. -/
theorem orderUnits_norm
    (L M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [FiniteDimensional (UnramifiedClosure F) M]
    [Algebra L M] [FiniteDimensional L M]
    (hv : ∀ x : M, normalizedIntermediateValuation F L (Algebra.norm L x) =
      normalizedIntermediateValuation F M x)
    (w : Mˣ) :
    (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
        (Units.map (Algebra.norm L : M →* L) w)).toAdd =
      (IntegerValuation.orderUnits (normalizedIntermediateValuation F M) w).toAdd := by
  rw [IntegerValuation.orderUnits_toAdd, IntegerValuation.orderUnits_toAdd, Units.coe_map]
  exact congrArg (fun z => -WithZero.log z) (hv (w : M))

/-- The norm square values agree on a pure evaluation in the larger field. -/
theorem normLawValue_relativeNorm_tmul
    (L M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [FiniteDimensional (UnramifiedClosure F) M]
    [Algebra L M] [IsScalarTower k L M] [IsScalarTower L M (SeparableClosure F)]
    [FiniteDimensional L M] [IsGalois L M]
    (hL : IsSplitTorus (baseChanged k L T).toGrp) (hM : IsSplitTorus (baseChanged k M T).toGrp)
    (hv : ∀ x : M, normalizedIntermediateValuation F L (Algebra.norm L x) =
      normalizedIntermediateValuation F M x)
    (w : Additive Mˣ) (ν' : cocharacterLattice (baseChanged k M T)) :
    normLawValue F k T L hL (Additive.ofMul (relativeNorm k L M T
        (coefficientEvaluation k M T (w ⊗ₜ[ULift.{u} ℤ] ν')).toMul)) =
      normLawValue F k T M hM (coefficientEvaluation k M T (w ⊗ₜ[ULift.{u} ℤ] ν')) := by
  obtain ⟨ν, rfl⟩ := (extendGeometricCocharacters_bijective k L M T hL).2 ν'
  obtain ⟨u₀, hu₀⟩ := exists_not_isOfFinOrder F L
  have hE : IsSplitTorus (baseChanged k (SeparableClosure F) T).toGrp :=
    hL.baseChange_fieldTower k L (SeparableClosure F) T.toGrp
  rw [relativeNorm_coefficientEvaluation_tmul k L M T hM hu₀ w ν, ofMul_toMul]
  refine (normLawValue_tmul F k T L hL _ ν).trans ?_
  refine Eq.trans ?_ (normLawValue_tmul F k T M hM w _).symm
  have h1 := orderUnits_norm F L M hv w.toMul
  have h2 := extendGeometricCocharacters_extend k L M (SeparableClosure F) T hE hu₀ ν
  -- Avoid `rw` on the large goal: the motive check times out.
  have h3 := (map_zsmul (extendGeometricCocharacters k M (SeparableClosure F) T) _
      (extendGeometricCocharacters k L M T ν)).trans
    ((congrArg (fun z => (IntegerValuation.orderUnits (normalizedIntermediateValuation F M)
      w.toMul).toAdd • z) h2).trans
      (map_zsmul (extendGeometricCocharacters k L (SeparableClosure F) T) _ ν).symm)
  have h4 := congrArg (fun n : ℤ => extendGeometricCocharacters k L (SeparableClosure F) T
    (n • ν)) h1
  exact congrArg (inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
    (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)) (h4.trans h3.symm)

/-- KP 11.1.1, independence step: for finite extensions `L ⊆ M` splitting `T` with `M / L`
Galois, the norm square value at `L` of a relative norm from `M` is the norm square value at `M`.
-/
theorem normLawValue_relativeNorm
    (L M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [FiniteDimensional (UnramifiedClosure F) M]
    [Algebra L M] [IsScalarTower k L M] [IsScalarTower L M (SeparableClosure F)]
    [FiniteDimensional L M] [IsGalois L M]
    (hL : IsSplitTorus (baseChanged k L T).toGrp) (hM : IsSplitTorus (baseChanged k M T).toGrp)
    (hv : ∀ x : M, normalizedIntermediateValuation F L (Algebra.norm L x) =
      normalizedIntermediateValuation F M x)
    (x : affinePoints T.toGrp (CommAlgCat.of k M)) :
    normLawValue F k T L hL (Additive.ofMul (relativeNorm k L M T x)) =
      normLawValue F k T M hM (Additive.ofMul x) := by
  have key := additive_ext_coefficientEvaluation k M T hM
    (φ := (normLawValue F k T L hL).comp (relativeNorm k L M T).toAdditive)
    (φ' := normLawValue F k T M hM)
    (fun w ν' => normLawValue_relativeNorm_tmul F k T L M hL hM hv w ν')
  exact DFunLike.congr_fun key (Additive.ofMul x)

/-- KP 11.1.1, independence of the splitting field: a homomorphism satisfying the norm square
for one finite Galois splitting field `L₀ / K` satisfies it for every finite Galois splitting
field `L / K`. The comparison runs through the compositum `L ⊔ L₀`. -/
theorem torusNormLawAt_of_torusNormLawAt
    (L₀ L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L₀] [IsGalois (UnramifiedClosure F) L₀]
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL₀ : IsSplitTorus (baseChanged k L₀ T).toGrp) (hL : IsSplitTorus (baseChanged k L T).toGrp)
    {κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T)}
    (h : TorusNormLawAt F k T L₀ hL₀ κ) : TorusNormLawAt F k T L hL κ := by
  let K := UnramifiedClosure F
  let M : IntermediateField K (SeparableClosure F) := L ⊔ L₀
  -- The tower `K ⊆ L₀ ⊆ M`.
  let : Algebra L₀ M := (IntermediateField.inclusion (le_sup_right : L₀ ≤ M)).toAlgebra
  let : Module L₀ M := Algebra.toModule
  have : IsScalarTower k L₀ M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K L₀ M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower L₀ M (SeparableClosure F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional L₀ M := FiniteDimensional.right K L₀ M
  have : IsGalois L₀ M := IsGalois.tower_top_of_isGalois K L₀ M
  -- The tower `K ⊆ L ⊆ M`.
  let : Algebra L M := (IntermediateField.inclusion (le_sup_left : L ≤ M)).toAlgebra
  let : Module L M := Algebra.toModule
  have : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower L M (SeparableClosure F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional L M := FiniteDimensional.right K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  -- `T` splits over `M`.
  have hM : IsSplitTorus (baseChanged k M T).toGrp :=
    (IsSplitTorus.baseChange_fieldTower_iff k L₀ M T.toGrp).2
      (hL₀.baseChange (baseMap L₀ M))
  -- Norm compatibility of the normalized valuations.
  have hv₀ : ∀ x : M, normalizedIntermediateValuation F L₀ (Algebra.norm L₀ x) =
      normalizedIntermediateValuation F M x :=
    normalizedIntermediateValuation_norm F L₀ M le_sup_right
  have hv : ∀ x : M, normalizedIntermediateValuation F L (Algebra.norm L x) =
      normalizedIntermediateValuation F M x :=
    normalizedIntermediateValuation_norm F L M le_sup_left
  -- The norm square at `M`.
  have hlawM : ∀ x : affinePoints T.toGrp (CommAlgCat.of k M),
      κ (relativeNorm k K M T x) =
        Multiplicative.ofAdd (normLawValue F k T M hM (Additive.ofMul x)) := by
    intro x
    exact (congrArg κ (relativeNorm_relativeNorm k K L₀ M T x).symm).trans
      (((torusNormLawAt_iff F k T L₀ hL₀ κ).1 h _).trans
        (congrArg Multiplicative.ofAdd (normLawValue_relativeNorm F k T L₀ M hL₀ hM hv₀ x)))
  -- Descend to `L` using surjectivity of the norm from `M` to `L`.
  have hLdim : Langlands.FieldTheory.HasDimensionLEOne L :=
    (unramifiedClosure_hasDimensionLEOne F).finite_separable_extension
  refine (torusNormLawAt_iff F k T L hL κ).2 fun y => ?_
  obtain ⟨x, rfl⟩ := relativeNorm_surjective k L M T hLdim hM y
  exact (congrArg κ (relativeNorm_relativeNorm k K L M T x)).trans
    ((hlawM x).trans
      (congrArg Multiplicative.ofAdd (normLawValue_relativeNorm F k T L M hL hM hv x).symm))

end Transfer

end Langlands.Geometry.Building.Kottwitz
