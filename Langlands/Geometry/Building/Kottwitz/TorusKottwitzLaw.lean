import Langlands.Geometry.Building.Kottwitz.TorusMapStatement
import Langlands.Geometry.Building.Kottwitz.TorusCocharacterTower
import Langlands.Geometry.Building.Kottwitz.TorusNormValuation
import Langlands.FieldTheory.DimensionLEOneArithmetic
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Mathlib.FieldTheory.Galois.GaloisClosure

/-! # The norm squares of the torus Kottwitz homomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPoint
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.TorusPointsTensorGalois

section Order

/-- A unit of nonzero order has infinite multiplicative order. -/
theorem not_isOfFinOrder_of_orderUnits {L : Type u} [Field L]
    {v : Valuation L (WithZero (Multiplicative ℤ))} {a : Lˣ}
    (h : (IntegerValuation.orderUnits v a).toAdd ≠ 0) : ¬IsOfFinOrder a := by
  intro ha
  obtain ⟨n, hn, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp ((IntegerValuation.orderUnits v).isOfFinOrder ha)
  have h' := congrArg Multiplicative.toAdd hpow
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul] at h'
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact hn.ne' (by exact_mod_cast h'')
  · exact h h''

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L]

/-- The integer normalization has a unit of order one. -/
theorem exists_orderUnits_eq_one :
    ∃ a : Lˣ, (IntegerValuation.orderUnits (normalizedIntermediateValuation F L) a).toAdd = 1 := by
  obtain ⟨y, hy⟩ := (normalizedIntermediateValuation_spec' F L).2 (WithZero.exp (-1))
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  rw [IntegerValuation.orderUnits_toAdd, Units.val_mk0, hy, WithZero.log_exp, neg_neg]

/-- The integer normalization has a unit of infinite order. -/
theorem exists_not_isOfFinOrder : ∃ a : Lˣ, ¬IsOfFinOrder a := by
  obtain ⟨a, ha⟩ := exists_orderUnits_eq_one F L
  exact ⟨a, not_isOfFinOrder_of_orderUnits (v := normalizedIntermediateValuation F L)
    (by rw [ha]; exact one_ne_zero)⟩

/-- The integer normalization is constant on `Gal(L/K)`-orbits of units. -/
theorem orderUnits_algEquiv (σ : L ≃ₐ[UnramifiedClosure F] L) (a : Lˣ) :
    IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
        (Units.map σ.toMonoidHom a) =
      IntegerValuation.orderUnits (normalizedIntermediateValuation F L) a := by
  apply Multiplicative.toAdd.injective
  rw [IntegerValuation.orderUnits_toAdd, IntegerValuation.orderUnits_toAdd]
  exact congrArg (fun z => -WithZero.log z)
    (normalizedIntermediateValuation_algEquiv F L σ (a : L))

end Order

section Law

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- The right-hand side of the norm square at `L`, as an additive map on coefficient points. -/
def normLawValue (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (hL : IsSplitTorus (baseChanged k L T).toGrp) :
    Additive (affinePoints T.toGrp (CommAlgCat.of k L)) →+ TorusTarget F k T where
  toFun x := inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
    (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)
    (extendGeometricCocharacters k L (SeparableClosure F) T
      (splitValuation (baseChanged k L T) hL (normalizedIntermediateValuation F L)
        ((baseChangeCoeffEquiv k L T.toGrp).symm x.toMul)).toAdd)
  map_zero' := by simp
  map_add' x y := by simp [toMul_add, map_mul, toAdd_mul, map_add]

omit [IsAffine T.X.left] in
/-- `normLawValue` on a point coming from the base change. -/
theorem normLawValue_ofMul_symm (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (hL : IsSplitTorus (baseChanged k L T).toGrp)
    (y : rationalPoints (baseChanged k L T).toGrp) :
    normLawValue F k T L hL (Additive.ofMul (baseChangeCoeffEquiv k L T.toGrp y)) =
      inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)
        (extendGeometricCocharacters k L (SeparableClosure F) T
          (splitValuation (baseChanged k L T) hL (normalizedIntermediateValuation F L) y).toAdd) := by
  simp only [normLawValue, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul,
    MulEquiv.symm_apply_apply]

/-- The norm square at `L` in terms of `normLawValue`. -/
theorem torusNormLawAt_iff (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus (baseChanged k L T).toGrp)
    (κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T)) :
    TorusNormLawAt F k T L hL κ ↔ ∀ x, κ (relativeNorm k (UnramifiedClosure F) L T x) =
      Multiplicative.ofAdd (normLawValue F k T L hL (Additive.ofMul x)) := by
  constructor
  · intro h x
    have hx := h ((baseChangeCoeffEquiv k L T.toGrp).symm x)
    rw [MulEquiv.apply_symm_apply] at hx
    exact hx
  · intro h t
    rw [h, normLawValue_ofMul_symm]

omit [IsAffine T.X.left] in
/-- The value of the norm square on a pure cocharacter evaluation. -/
theorem normLawValue_tmul (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (hL : IsSplitTorus (baseChanged k L T).toGrp) (w : Additive Lˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    normLawValue F k T L hL (coefficientEvaluation k L T (w ⊗ₜ[ULift.{u} ℤ] ν)) =
      inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)
        (extendGeometricCocharacters k L (SeparableClosure F) T
          ((IntegerValuation.orderUnits (normalizedIntermediateValuation F L) w.toMul).toAdd •
            ν)) := by
  have h : coefficientEvaluation k L T (w ⊗ₜ[ULift.{u} ℤ] ν) =
      Additive.ofMul (baseChangeCoeffEquiv k L T.toGrp
        (CocharacterUniformizer.cocharacterPoints L (baseChanged k L T) ν w.toMul)) := rfl
  rw [h, normLawValue_ofMul_symm, splitValuation_cocharacterPoints, toAdd_ofAdd]

/-- The extension of an automorphism of `L/K` to the separable closure lies in the inertia
subgroup. -/
theorem liftNormal_mem_relativeInertia
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (σ : L ≃ₐ[UnramifiedClosure F] L) :
    (σ.liftNormal (SeparableClosure F)).restrictScalars k ∈
      relativeInertia k (UnramifiedClosure F) (SeparableClosure F) := by
  rw [relativeInertia, MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro a
  apply (algebraMap (UnramifiedClosure F) (SeparableClosure F)).injective
  change algebraMap (UnramifiedClosure F) (SeparableClosure F)
      (((σ.liftNormal (SeparableClosure F)).restrictScalars k).restrictNormal
        (UnramifiedClosure F) a) = algebraMap (UnramifiedClosure F) (SeparableClosure F) a
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]

omit [IsAffine T.X.left] in
/-- Inertia coinvariants do not see the extension of a relative automorphism. -/
theorem inertiaProjection_liftNormal
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (σ : L ≃ₐ[UnramifiedClosure F] L) (v : cocharacterLattice (baseChanged k (SeparableClosure F) T)) :
    inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)
        (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T
          ((σ.liftNormal (SeparableClosure F)).restrictScalars k) v) =
      inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T) v :=
  Representation.Coinvariants.mk_self_apply _
    (⟨_, liftNormal_mem_relativeInertia F k L σ⟩ :
      relativeInertia k (UnramifiedClosure F) (SeparableClosure F)) v

omit [Normal k (UnramifiedClosure F)] in
/-- Extending cocharacters from `L` intertwines a relative automorphism with its extension. -/
theorem extendGeometricCocharacters_liftNormal
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L]
    (hE : IsSplitTorus (baseChanged k (SeparableClosure F) T).toGrp)
    (σ : L ≃ₐ[UnramifiedClosure F] L) (ν : cocharacterLattice (baseChanged k L T)) :
    extendGeometricCocharacters k L (SeparableClosure F) T
        (cocharacterLattice.galoisRepresentation k L T (σ.restrictScalars k) ν) =
      cocharacterLattice.galoisRepresentation k (SeparableClosure F) T
        ((σ.liftNormal (SeparableClosure F)).restrictScalars k)
        (extendGeometricCocharacters k L (SeparableClosure F) T ν) := by
  obtain ⟨a₀, ha₀⟩ := exists_not_isOfFinOrder F L
  exact extendGeometricCocharacters_galois k L (SeparableClosure F) T hE ha₀
    (σ.restrictScalars k) _ (fun a => AlgEquiv.liftNormal_commutes σ (SeparableClosure F) a) ν

/-- The norm square value of a conjugated pure evaluation. -/
theorem normLawValue_conjugate_tmul
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L]
    (hL : IsSplitTorus (baseChanged k L T).toGrp)
    (hE : IsSplitTorus (baseChanged k (SeparableClosure F) T).toGrp)
    (σ : L ≃ₐ[UnramifiedClosure F] L) (w : Additive Lˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    normLawValue F k T L hL (Additive.ofMul (conjugate k L T.toGrp (σ.restrictScalars k)
      (coefficientEvaluation k L T (w ⊗ₜ[ULift.{u} ℤ] ν)).toMul)) =
    normLawValue F k T L hL (coefficientEvaluation k L T (w ⊗ₜ[ULift.{u} ℤ] ν)) := by
  have hord : IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
      (Units.map (σ.restrictScalars k).toMonoidHom w.toMul) =
      IntegerValuation.orderUnits (normalizedIntermediateValuation F L) w.toMul :=
    orderUnits_algEquiv F L σ w.toMul
  rw [← coefficientEvaluation_galois_tmul, normLawValue_tmul, normLawValue_tmul, toMul_ofMul,
    hord, ← map_zsmul, extendGeometricCocharacters_liftNormal F k T L hE σ,
    inertiaProjection_liftNormal F k T L σ]

/-- The norm square value is invariant under `Gal(L/K)`. -/
theorem normLawValue_relativeConjugate
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L]
    (hL : IsSplitTorus (baseChanged k L T).toGrp)
    (hE : IsSplitTorus (baseChanged k (SeparableClosure F) T).toGrp)
    (σ : L ≃ₐ[UnramifiedClosure F] L) (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    normLawValue F k T L hL
        (Additive.ofMul (relativeConjugate k (UnramifiedClosure F) L T.toGrp σ x)) =
      normLawValue F k T L hL (Additive.ofMul x) := by
  have key := additive_ext_coefficientEvaluation k L T hL
    (φ := (normLawValue F k T L hL).comp
      (relativeConjugate k (UnramifiedClosure F) L T.toGrp σ).toAdditive)
    (φ' := normLawValue F k T L hL)
    (fun w ν => normLawValue_conjugate_tmul F k T L hL hE σ w ν)
  exact DFunLike.congr_fun key (Additive.ofMul x)

end Law

section Existence

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
  (hL : IsSplitTorus (baseChanged k L T).toGrp)

include hL in
omit [Normal k (UnramifiedClosure F)] in
/-- The norm `T(L) → T(K)` is onto for a finite Galois splitting field `L` of `K`. -/
theorem relativeNorm_unramifiedClosure_surjective :
    Function.Surjective (relativeNorm k (UnramifiedClosure F) L T) :=
  relativeNorm_surjective k (UnramifiedClosure F) L T (unramifiedClosure_hasDimensionLEOne F) hL

/-- The norm-square value at `L` kills the kernel of the norm. -/
theorem normLawValue_eq_zero_of_relativeNorm_eq_one
    (x : affinePoints T.toGrp (CommAlgCat.of k L))
    (hx : relativeNorm k (UnramifiedClosure F) L T x = 1) :
    normLawValue F k T L hL (Additive.ofMul x) = 0 :=
  invariant_eq_zero_of_relativeNorm_eq_one k (UnramifiedClosure F) L T
    (unramifiedClosure_hasDimensionLEOne F) hL (normLawValue F k T L hL)
    (fun σ y => normLawValue_relativeConjugate F k T L hL
      (IsSplitTorus.baseChange_fieldTower k L (SeparableClosure F) T.toGrp hL) σ y) x hx

/-- Existence of a homomorphism satisfying the norm square at one finite Galois splitting
field. -/
theorem exists_torusNormLawAt :
    ∃ κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T),
      TorusNormLawAt F k T L hL κ := by
  have hsurj := relativeNorm_unramifiedClosure_surjective F k T L hL
  let g : affinePoints T.toGrp (CommAlgCat.of k L) →* Multiplicative (TorusTarget F k T) :=
    AddMonoidHom.toMultiplicativeRight (normLawValue F k T L hL)
  have hker : (relativeNorm k (UnramifiedClosure F) L T).ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change Multiplicative.ofAdd (normLawValue F k T L hL (Additive.ofMul x)) = 1
    rw [normLawValue_eq_zero_of_relativeNorm_eq_one F k T L hL x hx, ofAdd_zero]
  refine ⟨(relativeNorm k (UnramifiedClosure F) L T).liftOfRightInverse
    (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨g, hker⟩, ?_⟩
  rw [torusNormLawAt_iff]
  intro x
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- Two homomorphisms satisfying the norm square at the same `L` are equal. -/
theorem eq_of_torusNormLawAt
    {κ κ' : torusKPoints F k T →* Multiplicative (TorusTarget F k T)}
    (h : TorusNormLawAt F k T L hL κ) (h' : TorusNormLawAt F k T L hL κ') : κ = κ' := by
  rw [torusNormLawAt_iff] at h h'
  apply MonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := relativeNorm_unramifiedClosure_surjective F k T L hL y
  rw [h, h']

/-- A homomorphism satisfying the norm square at `L` is onto. -/
theorem surjective_of_torusNormLawAt
    {κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T)}
    (h : TorusNormLawAt F k T L hL κ) : Function.Surjective κ := by
  rw [torusNormLawAt_iff] at h
  intro m
  obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective
    ((cocharacterLattice.galoisRepresentation k (SeparableClosure F) T).comp
      (relativeInertia k (UnramifiedClosure F) (SeparableClosure F)).subtype) m.toAdd
  obtain ⟨ν, rfl⟩ := (extendGeometricCocharacters_bijective k L (SeparableClosure F) T hL).2 v
  obtain ⟨a, ha⟩ := exists_orderUnits_eq_one F L
  refine ⟨relativeNorm k (UnramifiedClosure F) L T
    (coefficientEvaluation k L T (Additive.ofMul a ⊗ₜ[ULift.{u} ℤ] ν)).toMul, ?_⟩
  rw [h, ofMul_toMul, normLawValue_tmul, toMul_ofMul, ha, one_smul]
  exact hv

end Existence

end Langlands.Geometry.Building.Kottwitz
