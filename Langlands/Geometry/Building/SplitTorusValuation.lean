import Langlands.Geometry.Building.SplitRealTorusSpace
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-!
# The actual valuation of a split torus in its cocharacter lattice and real space

For the actual split torus `𝕋` over a nonarchimedean local field `F`, `valuation F I` sends a
rational point `t` to the cocharacter `ν(t)` whose coordinates are the positive orders of the
coordinates of `t`, and `realValuation F I` sends `t` to `ω(t) = 1 ⊗ ν(t)` in the real
cocharacter space. This is the positive valuation of Kaletha–Prasad §2.5(b), as corrected by
the authors, for split tori.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RealTorusSpace

variable {k : Type u} [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The integral cocharacter lattice inside the real cocharacter space, `c ↦ 1 ⊗ c`. -/
def latticeEmbedding : cocharacterLattice T →+ V T :=
  (TensorProduct.mk ℤ ℝ (cocharacterLattice T) 1).toAddMonoidHom

@[simp] theorem latticeEmbedding_apply (c : cocharacterLattice T) :
    latticeEmbedding T c = (1 : ℝ) ⊗ₜ[ℤ] c := rfl

/-- Integer multiples of a cocharacter become real multiples of its pure tensor. -/
theorem latticeEmbedding_zsmul (n : ℤ) (c : cocharacterLattice T) :
    latticeEmbedding T (n • c) = (n : ℝ) ⊗ₜ[ℤ] c := by
  rw [latticeEmbedding_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    zsmul_eq_mul, mul_one]

/-- Evaluation of a character on an embedded cocharacter is the integer pairing. -/
theorem eval_latticeEmbedding (χ : characterLattice T) (c : cocharacterLattice T) :
    eval T χ (latticeEmbedding T c) = (latticePairing T χ c : ℝ) := by
  rw [latticeEmbedding_apply, eval_tmul, one_mul]

variable (k) (I : Type u) [Finite I]

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I

/-- The real coordinates of an embedded split cocharacter are its integer coordinates. -/
theorem splitCocharacterCoordinates_latticeEmbedding (c : cocharacterLattice 𝕋) :
    splitCocharacterCoordinates k I (latticeEmbedding 𝕋 c) =
      fun j => (splitTorus.cocharacterLatticeEquiv k I c j : ℝ) := by
  rw [latticeEmbedding_apply, splitCocharacterCoordinates_tmul]
  funext j
  rw [one_mul]

/-- The integral embedding of the split cocharacter lattice is injective. -/
theorem latticeEmbedding_injective : Function.Injective (latticeEmbedding 𝕋) := by
  intro c c' h
  have hc := congrArg (splitCocharacterCoordinates k I) h
  rw [splitCocharacterCoordinates_latticeEmbedding,
    splitCocharacterCoordinates_latticeEmbedding] at hc
  apply (splitTorus.cocharacterLatticeEquiv k I).injective
  funext j
  exact_mod_cast congrFun hc j

end RealTorusSpace

namespace SplitTorusValuation

open Plancherel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (I : Type u) [Finite I]

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I

/-- The actual coordinates of a rational point of the split torus, in `I → Fˣ`. -/
local notation "coords" => splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of F)))

/-- The actual valuation of the rational points of the split torus, with values in the
cocharacter lattice: its coordinate at `i` is the positive order of the `i`-th coordinate. -/
def valuation : rationalPoints (𝕋).toGrp →* Multiplicative (cocharacterLattice 𝕋) where
  toFun t := Multiplicative.ofAdd ((splitTorus.cocharacterLatticeEquiv F I).symm
    fun i => (fieldOrderUnits F (coords t i)).toAdd)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    rw [AddEquiv.symm_apply_eq, map_zero]
    funext i
    rw [map_one, Pi.one_apply, map_one, toAdd_one, Pi.zero_apply]
  map_mul' s t := by
    rw [← ofAdd_add, ← map_add]
    apply congrArg (fun m => Multiplicative.ofAdd ((splitTorus.cocharacterLatticeEquiv F I).symm m))
    funext i
    rw [map_mul, Pi.mul_apply, map_mul, toAdd_mul, Pi.add_apply]

theorem valuation_toAdd (t : rationalPoints (𝕋).toGrp) :
    (valuation F I t).toAdd = (splitTorus.cocharacterLatticeEquiv F I).symm
      fun i => (fieldOrderUnits F (coords t i)).toAdd := rfl

/-- The coordinate defining law of the lattice valuation. -/
@[simp] theorem cocharacterLatticeEquiv_valuation (t : rationalPoints (𝕋).toGrp) (i : I) :
    splitTorus.cocharacterLatticeEquiv F I (valuation F I t).toAdd i =
      (fieldOrderUnits F (coords t i)).toAdd := by
  rw [valuation_toAdd, AddEquiv.apply_symm_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The actual character attached to the integer vector `m` evaluates on rational points as
the product of the coordinate powers `tᵢ ^ mᵢ`. -/
theorem rationalCharacterEval_characterLatticeEquiv_symm [Fintype I] (m : I → ℤ)
    (t : rationalPoints (𝕋).toGrp) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice 𝕋).symm
      ((splitTorus.characterLatticeEquiv F I).symm m)) t = ∏ i, coords t i ^ m i := by
  rw [rationalCharacterEval_apply]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom
    (Gm.pointsEquiv _ _ (t ≫ (CommGroupScheme.groupHom
      ((splitTorus.characterLatticeEquiv F I).symm m)).hom.hom)) = _
  rw [splitTorus.pointsEquiv_characterLatticeEquiv_symm, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow]
  rfl

/-- The intrinsic characterization: pairing with every actual character gives the existing
rational-character valuation at the corresponding rational character. -/
theorem latticePairing_valuation (χ : characterLattice 𝕋) (t : rationalPoints (𝕋).toGrp) :
    latticePairing 𝕋 χ (valuation F I t).toAdd =
      (rationalCharacterValuation (𝕋).toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice 𝕋).symm χ) := by
  let _ : Fintype I := Fintype.ofFinite I
  rw [rationalCharacterValuation_apply]
  conv_rhs => rw [← (splitTorus.characterLatticeEquiv F I).symm_apply_apply χ,
    rationalCharacterEval_characterLatticeEquiv_symm]
  rw [splitTorus.latticePairing_eq_sum, map_prod, toAdd_prod]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cocharacterLatticeEquiv_valuation, map_zpow, toAdd_zpow, smul_eq_mul, mul_comm]

/-- The pairing identity determines the lattice valuation uniquely. -/
theorem eq_valuation_iff (t : rationalPoints (𝕋).toGrp) (c : cocharacterLattice 𝕋) :
    c = (valuation F I t).toAdd ↔
      ∀ χ : characterLattice 𝕋, latticePairing 𝕋 χ c =
        (rationalCharacterValuation (𝕋).toGrp t).toAdd
          ((rationalCharacters.equivCharacterLattice 𝕋).symm χ) := by
  constructor
  · rintro rfl χ
    exact latticePairing_valuation F I χ t
  · intro h
    apply (LinearMap.IsPerfPair.bijective_right (latticePairing 𝕋)).injective
    refine LinearMap.ext fun χ => ?_
    rw [LinearMap.flip_apply, LinearMap.flip_apply, h, latticePairing_valuation]

/-- The real valuation `ω(t) = 1 ⊗ ν(t)` in the real cocharacter space. -/
def realValuation : rationalPoints (𝕋).toGrp →* Multiplicative (RealTorusSpace.V 𝕋) :=
  (AddMonoidHom.toMultiplicative (RealTorusSpace.latticeEmbedding 𝕋)).comp (valuation F I)

theorem realValuation_toAdd (t : rationalPoints (𝕋).toGrp) :
    (realValuation F I t).toAdd = RealTorusSpace.latticeEmbedding 𝕋 (valuation F I t).toAdd :=
  rfl

/-- The real coordinates of `ω(t)` are the integer orders of the coordinates, cast to `ℝ`. -/
theorem splitCocharacterCoordinates_realValuation (t : rationalPoints (𝕋).toGrp) :
    RealTorusSpace.splitCocharacterCoordinates F I (realValuation F I t).toAdd =
      fun i => ((fieldOrderUnits F (coords t i)).toAdd : ℝ) := by
  rw [realValuation_toAdd, RealTorusSpace.splitCocharacterCoordinates_latticeEmbedding]
  funext i
  rw [cocharacterLatticeEquiv_valuation]

/-- Evaluation of `ω(t)` by an actual character is the real cast of the existing
rational-character valuation. -/
theorem eval_realValuation (χ : characterLattice 𝕋) (t : rationalPoints (𝕋).toGrp) :
    RealTorusSpace.eval 𝕋 χ (realValuation F I t).toAdd =
      ((rationalCharacterValuation (𝕋).toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice 𝕋).symm χ) : ℝ) := by
  rw [realValuation_toAdd, RealTorusSpace.eval_latticeEmbedding, latticePairing_valuation]

/-- Evaluation of `ω(t)` by an actual character is the corresponding coordinate of the existing
rational norm logarithm. -/
theorem eval_realValuation_eq_rationalNormLogarithm (χ : characterLattice 𝕋)
    (t : rationalPoints (𝕋).toGrp) :
    RealTorusSpace.eval 𝕋 χ (realValuation F I t).toAdd =
      (rationalNormLogarithm (𝕋).toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice 𝕋).symm χ) := by
  rw [eval_realValuation, rationalNormLogarithm_eq_intValuation]

/-! ### Cocharacter evaluation -/

/-- The rational points `c(a)` of an actual cocharacter `c`, obtained by evaluating the
group-scheme homomorphism `c` at the rational point of `𝔾_m` with value `a`. -/
def cocharacterPoints (c : cocharacterLattice 𝕋) : Fˣ →* rationalPoints (𝕋).toGrp :=
  (rationalPoints.map (CommGroupScheme.groupHom c)).comp
    (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm.toMonoidHom

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem cocharacterPoints_apply (c : cocharacterLattice 𝕋) (a : Fˣ) :
    cocharacterPoints F I c a =
      rationalPoints.map (CommGroupScheme.groupHom c)
        ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm a) := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The coordinates of `c(a)` are the powers of `a` by the coordinates of `c`. -/
theorem coords_cocharacterPoints (c : cocharacterLattice 𝕋) (a : Fˣ) (i : I) :
    coords (cocharacterPoints F I c a) i = a ^ splitTorus.cocharacterLatticeEquiv F I c i := by
  have h := splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm F I
    (splitTorus.cocharacterLatticeEquiv F I c) (T := Over.mk (𝟙 (Spec (CommRingCat.of F))))
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm a)
  rw [AddEquiv.symm_apply_apply] at h
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom
    (splitTorus.pointsEquiv I _ (((Gm.affinePointsEquiv
      (𝟙 (Spec (CommRingCat.of F)))).symm a) ≫ (CommGroupScheme.groupHom c).hom.hom) i) = _
  rw [h, map_zpow]
  congr 1
  exact (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).apply_symm_apply a

/-- `ν(c(a)) = ord(a) • c`. -/
theorem valuation_cocharacterPoints (c : cocharacterLattice 𝕋) (a : Fˣ) :
    (valuation F I (cocharacterPoints F I c a)).toAdd = (fieldOrderUnits F a).toAdd • c := by
  apply (splitTorus.cocharacterLatticeEquiv F I).injective
  funext i
  rw [cocharacterLatticeEquiv_valuation, coords_cocharacterPoints, map_zsmul, Pi.smul_apply,
    map_zpow, toAdd_zpow, smul_eq_mul, smul_eq_mul, mul_comm]

/-- `ω(c(a)) = ord(a) ⊗ c`. -/
theorem realValuation_cocharacterPoints (c : cocharacterLattice 𝕋) (a : Fˣ) :
    (realValuation F I (cocharacterPoints F I c a)).toAdd =
      ((fieldOrderUnits F a).toAdd : ℝ) ⊗ₜ[ℤ] c := by
  rw [realValuation_toAdd, valuation_cocharacterPoints, RealTorusSpace.latticeEmbedding_zsmul]

/-- The existing order-one uniformizer, regarded as a field unit. -/
def uniformizerUnit : Fˣ :=
  Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)

@[simp] theorem uniformizerUnit_val : (uniformizerUnit F : F) = LocalField.uniformizer F := rfl

/-- The uniformizer unit has order one. -/
@[simp] theorem fieldOrderUnits_uniformizerUnit :
    (fieldOrderUnits F (uniformizerUnit F)).toAdd = 1 := by
  have h := fieldOrderUnits_ord F (uniformizerUnit F)
  rw [uniformizerUnit_val, LocalField.ord_uniformizer] at h
  exact_mod_cast h.symm

/-- `ν(c(π)) = c`. -/
theorem valuation_cocharacterPoints_uniformizer (c : cocharacterLattice 𝕋) :
    (valuation F I (cocharacterPoints F I c (uniformizerUnit F))).toAdd = c := by
  rw [valuation_cocharacterPoints, fieldOrderUnits_uniformizerUnit, one_smul]

/-- `ω(c(π)) = 1 ⊗ c`. -/
theorem realValuation_cocharacterPoints_uniformizer (c : cocharacterLattice 𝕋) :
    (realValuation F I (cocharacterPoints F I c (uniformizerUnit F))).toAdd =
      (1 : ℝ) ⊗ₜ[ℤ] c := by
  rw [realValuation_cocharacterPoints, fieldOrderUnits_uniformizerUnit, Int.cast_one]

/-! ### Image and kernel -/

/-- The lattice valuation is onto the full actual cocharacter lattice. -/
theorem valuation_surjective : Function.Surjective (valuation F I) := fun x =>
  ⟨cocharacterPoints F I x.toAdd (uniformizerUnit F),
    congrArg Multiplicative.ofAdd (valuation_cocharacterPoints_uniformizer F I x.toAdd)⟩

theorem valuation_range : (valuation F I).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (valuation_surjective F I)

/-- The image of the real valuation is exactly the image of the integral embedding. -/
theorem mem_realValuation_range (x : Multiplicative (RealTorusSpace.V 𝕋)) :
    x ∈ (realValuation F I).range ↔ x.toAdd ∈ (RealTorusSpace.latticeEmbedding 𝕋).range := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(valuation F I t).toAdd, rfl⟩
  · rintro ⟨c, hc⟩
    obtain ⟨t, ht⟩ := valuation_surjective F I (Multiplicative.ofAdd c)
    refine ⟨t, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [realValuation_toAdd, ht, toAdd_ofAdd, hc]

theorem realValuation_range :
    (realValuation F I).range = (RealTorusSpace.latticeEmbedding 𝕋).range.toSubgroup := by
  ext x
  rw [mem_realValuation_range]
  rfl

/-- The pullback, under the actual coordinates, of the product of the integral unit groups. -/
def integralUnitKernel : Subgroup (rationalPoints (𝕋).toGrp) :=
  (Subgroup.pi Set.univ fun _ : I => FML.unitGroup F).comap (coords).toMonoidHom

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_integralUnitKernel (t : rationalPoints (𝕋).toGrp) :
    t ∈ integralUnitKernel F I ↔ ∀ i, coords t i ∈ FML.unitGroup F := by
  simp [integralUnitKernel, Subgroup.mem_pi]

theorem mem_valuation_ker (t : rationalPoints (𝕋).toGrp) :
    t ∈ (valuation F I).ker ↔ ∀ i, coords t i ∈ FML.unitGroup F := by
  rw [MonoidHom.mem_ker, ← toAdd_eq_zero,
    ← (splitTorus.cocharacterLatticeEquiv F I).map_eq_zero_iff, funext_iff]
  refine forall_congr' fun i => ?_
  rw [cocharacterLatticeEquiv_valuation, Pi.zero_apply, ← fieldOrderUnits_ker F,
    MonoidHom.mem_ker, toAdd_eq_zero]

theorem valuation_ker : (valuation F I).ker = integralUnitKernel F I := by
  ext t
  rw [mem_valuation_ker, mem_integralUnitKernel]

theorem realValuation_ker : (realValuation F I).ker = integralUnitKernel F I := by
  rw [← valuation_ker]
  ext t
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← toAdd_eq_zero, ← toAdd_eq_zero, realValuation_toAdd,
    (RealTorusSpace.latticeEmbedding_injective F I).eq_iff' (map_zero _)]

theorem mem_realValuation_ker (t : rationalPoints (𝕋).toGrp) :
    t ∈ (realValuation F I).ker ↔ ∀ i, coords t i ∈ FML.unitGroup F := by
  rw [realValuation_ker, mem_integralUnitKernel]

/-- The integral-unit kernel is the existing common kernel of the actual normalized
rational-character norms. -/
theorem integralUnitKernel_eq_rationalCommonNormKernel :
    integralUnitKernel F I = rationalCommonNormKernel (𝕋).toGrp := by
  rw [← valuation_ker]
  ext t
  rw [MonoidHom.mem_ker, mem_rationalCommonNormKernel_iff_valuation, ← toAdd_eq_zero, eq_comm,
    eq_valuation_iff]
  simp only [map_zero]
  constructor
  · intro h ψ
    have hψ := h (rationalCharacters.equivCharacterLattice 𝕋 ψ)
    rw [AddEquiv.symm_apply_apply] at hψ
    exact hψ.symm
  · intro h χ
    exact (h _).symm

/-! ### Regression specializations -/

section OneCoordinate

local notation "𝕋₁" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) PUnit

/-- The rational point of the one-coordinate split torus with coordinate the uniformizer. -/
abbrev uniformizerPoint : rationalPoints (𝕋₁).toGrp :=
  (splitTorus.affinePointsEquiv PUnit (𝟙 (Spec (CommRingCat.of F)))).symm
    fun _ => uniformizerUnit F

/-- On the one-coordinate split torus the uniformizer has valuation `+1`. -/
theorem cocharacterLatticeEquiv_valuation_uniformizerPoint :
    splitTorus.cocharacterLatticeEquiv F PUnit (valuation F PUnit (uniformizerPoint F)).toAdd =
      fun _ => 1 := by
  funext i
  rw [cocharacterLatticeEquiv_valuation, MulEquiv.apply_symm_apply,
    fieldOrderUnits_uniformizerUnit]

/-- On the one-coordinate split torus the inverse uniformizer has valuation `-1`. -/
theorem cocharacterLatticeEquiv_valuation_uniformizerPoint_inv :
    splitTorus.cocharacterLatticeEquiv F PUnit
        (valuation F PUnit (uniformizerPoint F)⁻¹).toAdd = fun _ => -1 := by
  rw [map_inv, toAdd_inv, map_neg, cocharacterLatticeEquiv_valuation_uniformizerPoint]
  rfl

/-- The real valuation of the one-coordinate uniformizer has coordinate `+1`. -/
theorem splitCocharacterCoordinates_realValuation_uniformizerPoint :
    RealTorusSpace.splitCocharacterCoordinates F PUnit
        (realValuation F PUnit (uniformizerPoint F)).toAdd = fun _ => 1 := by
  rw [splitCocharacterCoordinates_realValuation]
  funext i
  rw [MulEquiv.apply_symm_apply, fieldOrderUnits_uniformizerUnit, Int.cast_one]

/-- The real valuation of the one-coordinate inverse uniformizer has coordinate `-1`. -/
theorem splitCocharacterCoordinates_realValuation_uniformizerPoint_inv :
    RealTorusSpace.splitCocharacterCoordinates F PUnit
        (realValuation F PUnit (uniformizerPoint F)⁻¹).toAdd = fun _ => -1 := by
  rw [map_inv, toAdd_inv, map_neg, splitCocharacterCoordinates_realValuation_uniformizerPoint]
  rfl

end OneCoordinate

section Empty

variable [IsEmpty I]

/-- For empty `I` the lattice valuation vanishes. -/
theorem valuation_eq_one_of_isEmpty (t : rationalPoints (𝕋).toGrp) : valuation F I t = 1 := by
  apply Multiplicative.toAdd.injective
  apply (splitTorus.cocharacterLatticeEquiv F I).injective
  exact Subsingleton.elim _ _

/-- For empty `I` the real valuation vanishes. -/
theorem realValuation_eq_one_of_isEmpty (t : rationalPoints (𝕋).toGrp) :
    realValuation F I t = 1 := by
  apply Multiplicative.toAdd.injective
  exact RealTorusSpace.eq_zero_of_isEmpty_cocharacter F I _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For empty `I` the integral-unit kernel is the whole rational-point group. -/
theorem integralUnitKernel_eq_top_of_isEmpty : integralUnitKernel F I = ⊤ := by
  rw [eq_top_iff]
  intro t _
  rw [mem_integralUnitKernel]
  exact fun i => isEmptyElim i

theorem valuation_ker_eq_top_of_isEmpty : (valuation F I).ker = ⊤ := by
  rw [valuation_ker, integralUnitKernel_eq_top_of_isEmpty]

theorem realValuation_ker_eq_top_of_isEmpty : (realValuation F I).ker = ⊤ := by
  rw [realValuation_ker, integralUnitKernel_eq_top_of_isEmpty]

end Empty

end SplitTorusValuation

end Langlands.GroupScheme
