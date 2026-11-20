import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.BruhatTits.Parabolic.ProperPointCompactnessAdapter
import Langlands.Representation.Plancherel.ParabolicLeviLogarithmBounds
import Langlands.Analysis.Local.VectorFiltrationHaarModulusProof
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Algebra.Polynomial.Roots

/-! # Compact cocharacter values avoiding finitely many fixed weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
  Langlands.BruhatTits.DynamicUnipotentContainment
  Langlands.HaarModulus.VectorFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The normalized absolute displacement for a cocharacter weight on a field unit. -/
def fieldUnitDisplacementNorm (s : Fˣ) (d : ℤ) : ℝ≥0 :=
  scalingWithZero (1 - ((s ^ d : Fˣ) : F))

private theorem scalingWithZero_unit (s : Fˣ)
    (hs : LocalField.residueNormalizedAbsoluteValue F (s : F) = 1) :
    scalingWithZero (s : F) = 1 := by
  rw [scalingWithZero_of_ne_zero s.ne_zero,
    show Units.mk0 (s : F) s.ne_zero = s from Units.ext rfl]
  exact distribHaarChar_eq_one_of_abs_eq_one F s hs

/-- Opposite weights have equal displacement norm at a norm-one field unit. -/
theorem fieldUnitDisplacementNorm_neg (s : Fˣ)
    (hs : LocalField.residueNormalizedAbsoluteValue F (s : F) = 1) (d : ℤ) :
    fieldUnitDisplacementNorm s (-d) = fieldUnitDisplacementNorm s d := by
  let x : Fˣ := s ^ d
  have hx : scalingWithZero (x : F) = 1 := by
    rw [show (x : F) = (s : F) ^ d by simp [x], map_zpow₀, scalingWithZero_unit s hs, one_zpow]
  have hinv : scalingWithZero ((x⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hneg : scalingWithZero (-1 : F) = 1 :=
    scalingWithZero_unit (-1 : Fˣ) (by simp)
  have hsub : 1 - ((x⁻¹ : Fˣ) : F) = (-1 : F) * ((x⁻¹ : Fˣ) : F) * (1 - (x : F)) := by
    rw [Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [fieldUnitDisplacementNorm, zpow_neg, hsub, map_mul, map_mul, hneg, hinv,
    one_mul, one_mul]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finite_units_zpow_eq_one (d : ℤ) (hd : d ≠ 0) :
    Set.Finite {s : Fˣ | s ^ d = 1} := by
  let p : Polynomial F := Polynomial.X ^ d.natAbs - Polynomial.C 1
  have hp : p ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (Int.natAbs_pos.mpr hd) 1
  apply ((Polynomial.finite_setOfPred_isRoot hp).preimage Units.val_injective.injOn).subset
  intro s hs
  have hs' : s ^ d.natAbs = 1 := pow_natAbs_eq_one.mpr hs
  have he := congrArg (fun x : Fˣ => (x : F)) hs'
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, p, Polynomial.IsRoot.def,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero, Units.val_pow_eq_pow_val, Units.val_one] using he

private theorem singleton_one_units_not_open : ¬ IsOpen ({1} : Set Fˣ) := by
  intro hs
  let : T2Space F := BruhatTits.localField_t2Space F
  have hopen : IsOpen ((Units.val : Fˣ → F) '' ({1} : Set Fˣ)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := F)).isOpenMap _ hs
  rw [Set.image_singleton, Units.val_one] at hopen
  have hzero : IsOpen ({0} : Set F) := by
    convert hopen.preimage (continuous_id.add_const (1 : F)) using 1
    ext x
    simp
  exact BruhatTits.localField_not_discreteTopology F
    (discreteTopology_iff_isOpen_singleton_zero.mpr hzero)

/-- Every identity neighborhood in the field units contains a norm-one unit
avoiding the roots of unity of the specified nonzero exponents. -/
theorem exists_normOne_unit_avoiding_zpow
    {W : Set Fˣ} (hW : W ∈ 𝓝 (1 : Fˣ)) (D : Finset ℤ) :
    ∃ s ∈ W, LocalField.residueNormalizedAbsoluteValue F (s : F) = 1 ∧
      ∀ d ∈ D, d ≠ 0 → s ^ d ≠ 1 := by
  classical
  let : T2Space F := BruhatTits.localField_t2Space F
  let : NeBot (𝓝[≠] (1 : Fˣ)) :=
    ⟨fun h => singleton_one_units_not_open ((isOpen_singleton_iff_punctured_nhds (1 : Fˣ)).mpr h)⟩
  have hn : {s : Fˣ | LocalField.residueNormalizedAbsoluteValue F (s : F) = 1} ∈ 𝓝 (1 : Fˣ) := by
    filter_upwards [(fieldNormUnits_isLocallyConstant F).eventually_eq (1 : Fˣ)] with s hs
    have h := congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hs
    simpa only [Set.mem_ofPred_eq, fieldNormUnits_val, Units.val_one, NNReal.coe_one, map_one] using h
  let S := ⋃ d ∈ (D.erase 0 : Finset ℤ), {s : Fˣ | s ^ d = 1}
  have hS : S.Finite := (D.erase 0).finite_toSet.biUnion fun d hd =>
    finite_units_zpow_eq_one d (Finset.ne_of_mem_erase hd)
  have hinf := infinite_of_mem_nhds (1 : Fˣ) (inter_mem hW hn)
  obtain ⟨s, hs, hS'⟩ := (hinf.sdiff hS).nonempty
  refine ⟨s, hs.1, hs.2, fun d hd hd0 hpow => hS' ?_⟩
  exact Set.mem_iUnion₂.mpr ⟨d, Finset.mem_erase.mpr ⟨hd0, hd⟩, hpow⟩

section Cocharacter

open Dynamic.AffineChart

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

/-- Evaluating an actual cocharacter is continuous on the field units. -/
theorem continuous_cocharPoint : Continuous (cocharPoint χ) := by
  refine (continuous_iff_pointRing (cocharPoint χ)).2 fun b => ?_
  let q := AffineLine.laurentPoint (𝟙 (Spec (CommRingCat.of F))) ≫
    SemiCartesianMonoidalCategory.snd _ _ ≫ χ.hom.hom
  have he (s : Fˣ) : cocharPoint χ s = laurentSection s ≫ q := by
    simp only [q, cocharPoint, unitPoint, Category.assoc]
  simp_rw [he, pointRing_comp]
  change Continuous (fun s : Fˣ => (Spec.preimage (Spec.map (laurentEval s))) (pointRing q b))
  simp only [Spec.preimage_map]
  let p := pointRing q b
  change Continuous (fun s : Fˣ => LaurentPolynomial.eval₂ (RingHom.id F) s p)
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => simpa only [map_add] using hp.fun_add hr
  | C_mul_T d a =>
    simp only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, RingHom.id_apply]
    exact continuous_const.mul (Units.continuous_val.comp (continuous_id.zpow d))

/-- Every compact open subgroup contains a norm-one cocharacter value with
all specified nonzero weights different from one. -/
theorem exists_normOne_cocharPoint_mem
    (K : OpenSubgroup (RationalPoint F G.X)) (D : Finset ℤ) :
    ∃ s : Fˣ, cocharPoint χ s ∈ K ∧ LocalField.residueNormalizedAbsoluteValue F (s : F) = 1 ∧
      ∀ d ∈ D, d ≠ 0 → s ^ d ≠ 1 := by
  have h1 : cocharPoint χ 1 = 1 := by
    rw [← cocharPointHom_apply, map_one]
  have hW : (cocharPoint χ) ⁻¹' (K : Set (RationalPoint F G.X)) ∈ 𝓝 (1 : Fˣ) := by
    apply (K.isOpen.preimage (continuous_cocharPoint χ)).mem_nhds
    change cocharPoint χ 1 ∈ K.toSubgroup
    rw [h1]
    exact K.toSubgroup.one_mem
  exact exists_normOne_unit_avoiding_zpow hW D

end Cocharacter

end Langlands.Plancherel
