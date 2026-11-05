import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentHeight
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Haar volume of height balls in dynamic unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix MeasureTheory
open Langlands.GroupScheme.GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

section NormalizerConj

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {H : Subgroup Γ} {a : Γ}

/-- For `a` in the normalizer of a subgroup `H` of a topological group, the continuous
automorphism `x ↦ a⁻¹ * x * a` of `H`. -/
def normalizerInvConj (ha : a ∈ Subgroup.normalizer (H : Set Γ)) : H ≃ₜ* H where
  toFun x := ⟨a⁻¹ * x * a, (Subgroup.mem_normalizer_iff.1 ha _).2 (by
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using x.2)⟩
  invFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha _).1 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := by
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp] theorem coe_normalizerInvConj_apply (ha : a ∈ Subgroup.normalizer (H : Set Γ))
    (x : H) : (normalizerInvConj ha x : Γ) = a⁻¹ * x * a :=
  rfl

/-- The `k`-th iterate of `normalizerInvConj` is conjugation by `a ^ k`. -/
theorem coe_normalizerInvConj_iterate (ha : a ∈ Subgroup.normalizer (H : Set Γ)) (k : ℕ)
    (x : H) : (((⇑(normalizerInvConj ha))^[k] x : H) : Γ) = (a ^ k)⁻¹ * x * a ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, coe_normalizerInvConj_apply, pow_succ]
    group

end NormalizerConj

section HaarIterate

variable {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
  [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- A continuous automorphism `φ` divides Haar measures of preimages by its Haar character. -/
theorem measure_preimage_mulEquiv (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular]
    (φ : H ≃ₜ* H) (X : Set H) :
    ν (φ ⁻¹' X) = (((mulEquivHaarChar φ)⁻¹ : ℝ≥0) : ℝ≥0∞) * ν X := by
  have h := mulEquivHaarChar_smul_preimage ν (X := X) φ
  change ((mulEquivHaarChar φ : ℝ≥0) : ℝ≥0∞) * ν (φ ⁻¹' X) = ν X at h
  have hpos := mulEquivHaarChar_pos φ
  rw [← h, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hpos.ne', ENNReal.coe_one, one_mul]

/-- Iterating `measure_preimage_mulEquiv`. -/
theorem measure_preimage_iterate_mulEquiv (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular]
    (φ : H ≃ₜ* H) (X : Set H) (k : ℕ) :
    ν ((⇑φ)^[k] ⁻¹' X) = (((mulEquivHaarChar φ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * ν X := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ, Set.preimage_comp, measure_preimage_mulEquiv, ih, pow_succ]
    ring

/-- If the `k`-th iterate of a continuous automorphism maps `S` into `K`, then
`ν S ≤ (mulEquivHaarChar φ)⁻¹ ^ k * ν K`. -/
theorem measure_le_of_iterate_mem (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular]
    (φ : H ≃ₜ* H) {S K : Set H} {k : ℕ} (h : ∀ x ∈ S, (⇑φ)^[k] x ∈ K) :
    ν S ≤ (((mulEquivHaarChar φ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * ν K := by
  rw [← measure_preimage_iterate_mulEquiv]
  exact measure_mono h

end HaarIterate

section OffIdentity

variable {F : Type*} [NormedField F] [IsUltrametricDist F] {n : Type} [Fintype n]
  [DecidableEq n] [Nonempty n]

/-- The entries of `g - 1` are bounded by Waldspurger's norm of `g`. -/
theorem offIdentityNorm_le_glNorm (g : GL n F) : offIdentityNorm g ≤ glNorm g := by
  refine entryNorm_le fun i j => ?_
  rw [Matrix.sub_apply, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_le_glNorm g i j) ?_)
  rw [norm_neg]
  exact ((norm_le_entryNorm (1 : Matrix n n F) i j).trans_eq entryNorm_one).trans
    (one_le_glNorm g)

end OffIdentity

end Langlands.HarishChandraSchwartz

namespace Langlands.GroupScheme.MatrixRepresentation

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

/-- For a closed representation, the rational points of height at most `C` form a compact
set. -/
theorem isCompact_rationalMatrixNorm_le {N : ℕ} [Nonempty (Fin N)]
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ) (C : ℝ) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact {g : rationalPoints G | rationalMatrixNorm F ρ g ≤ C} := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hset : {g : rationalPoints G | rationalMatrixNorm F ρ g ≤ C} =
      {g : rationalPoints G | ∀ i j,
        LocalField.residueNormalizedAbsoluteValue F
            ((ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F) i j) ≤ C ∧
          LocalField.residueNormalizedAbsoluteValue F
            ((((ρ.rationalMatrix g)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) i j) ≤ C} := by
    ext g
    constructor
    · intro hg i j
      exact ⟨(HarishChandraSchwartz.norm_le_glNorm _ i j).trans hg,
        (HarishChandraSchwartz.norm_inv_le_glNorm _ i j).trans hg⟩
    · intro hg
      exact HarishChandraSchwartz.glNorm_le (fun i j => (hg i j).1) (fun i j => (hg i j).2)
  rw [hset]
  exact isCompact_rationalMatrix_entry_le F ρ hρ C


variable [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
local instance : T2Space F := BruhatTits.localField_t2Space F
local instance : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G

/-- **Volume of height balls in a contracted unipotent subgroup.** Let `χ` be a cocharacter of
an affine group `G` of finite type over a non-archimedean local field `F` with residue
cardinality `q`, `ρ₀` a closed representation, and `H` a closed subgroup of
`Ū(F) = U(χ⁻¹)(F)` normalized by every `χ(t)`. For every regular Haar measure `ν` on `H`
there are `C, B ≥ 0` with `ν {x ∈ H | ‖x‖_ρ₀ ≤ q ^ n} ≤ C * B ^ n` for all `n`. -/
theorem exists_measure_rationalMatrixNorm_le_pow
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (H : Subgroup (rationalPoints G)) (hHc : IsClosed (H : Set (rationalPoints G)))
    (hHU : H ≤ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints)
    (hHa : ∀ t : Fˣ, gmRationalPoint t ≫ χ.hom.hom ∈
      Subgroup.normalizer (H : Set (rationalPoints G)))
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular] :
    ∃ C B : ℝ≥0, ∀ n : ℕ,
      ν {x : H | rationalMatrixNorm F ρ₀ x ≤ (LocalField.residueCardinality F : ℝ) ^ n} ≤
        C * B ^ n := by
  have : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  obtain ⟨g₀, e₀, hg₀⟩ := exists_innerIso_comp_eq_diagonalCocharacter F (χ ≫ ρ₀)
  have hcl : IsClosedSubgroup
      (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) :=
    hρ₀.comp_iso _
  have hχ₁ : χ ≫ ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom =
      diagonalCocharacter (Fin N) (CommRingCat.of F) e₀ := by
    rw [← Category.assoc, hg₀]
  have hM1 : 1 ≤ HarishChandraSchwartz.glNorm
      (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) :=
    HarishChandraSchwartz.one_le_glNorm _
  have hcomp : ∀ x : rationalPoints G,
      rationalMatrixNorm F (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x ≤
        HarishChandraSchwartz.glNorm
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 *
          rationalMatrixNorm F ρ₀ x := by
    intro x
    change HarishChandraSchwartz.glNorm (rationalMatrix
        (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x) ≤
      HarishChandraSchwartz.glNorm
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 *
        HarishChandraSchwartz.glNorm (ρ₀.rationalMatrix x)
    rw [rationalMatrix_comp_innerIso]
    refine (HarishChandraSchwartz.glNorm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (HarishChandraSchwartz.glNorm_mul_le _ _)
      (HarishChandraSchwartz.glNorm_nonneg _)).trans_eq ?_
    rw [HarishChandraSchwartz.glNorm_inv]
    ring
  generalize ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom = ρ₁
    at hcl hχ₁ hcomp
  generalize HarishChandraSchwartz.glNorm
    (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) = M at hM1 hcomp
  have hq1 : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  let t : Fˣ := Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)
  have htn : ‖(t : F)‖ = (LocalField.residueCardinality F : ℝ)⁻¹ :=
    LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F)
  generalize (LocalField.residueCardinality F : ℝ) = q at hq1 htn ⊢
  have hq0 : 0 < q := zero_lt_one.trans hq1
  have hD : rationalMatrix ρ₁ (gmRationalPoint t ≫ χ.hom.hom) = diagonalUnits F e₀ t :=
    rationalMatrix_gmRationalPoint_comp hχ₁ t
  have hmem : ∀ x ∈ H, rationalMatrix ρ₁ x ∈ blockUnipotentSubgroup F (-e₀) := by
    intro x hx
    have : IsClosedImmersion ρ₁.hom.hom.left := hcl
    rw [rationalMatrix_mem_blockUnipotentSubgroup_iff]
    exact (Dynamic.mem_unipotent_iff_of_diagonal hχ₁ x).1 (hHU hx)
  obtain ⟨d, hd⟩ := HarishChandraSchwartz.exists_weight_gap_le e₀
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (M ^ 2) hq1
  have hK₀c : IsCompact {y : H | rationalMatrixNorm F ρ₁ y ≤ 1} :=
    hHc.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_rationalMatrixNorm_le F ρ₁ hcl 1)
  let φ := HarishChandraSchwartz.normalizerInvConj (hHa t)
  have hstep : ∀ n : ℕ, ∀ x ∈ {x : H | rationalMatrixNorm F ρ₀ x ≤ q ^ n},
      (⇑φ)^[n + m₀] x ∈ {y : H | rationalMatrixNorm F ρ₁ y ≤ 1} := by
    intro n x hx
    change rationalMatrixNorm F ρ₁ (((⇑φ)^[n + m₀] x : H) : rationalPoints G) ≤ 1
    rw [HarishChandraSchwartz.coe_normalizerInvConj_iterate]
    have hconj : rationalMatrix ρ₁
        (((gmRationalPoint t ≫ χ.hom.hom) ^ (n + m₀))⁻¹ * x *
          (gmRationalPoint t ≫ χ.hom.hom) ^ (n + m₀)) =
        (diagonalUnits F e₀ (t ^ (n + m₀)))⁻¹ * rationalMatrix ρ₁ x *
          diagonalUnits F e₀ (t ^ (n + m₀)) := by
      rw [map_mul, map_mul, map_inv, map_pow, hD, map_pow]
    have hx₁ := hmem x x.2
    have htk : ‖((t ^ (n + m₀) : Fˣ) : F)‖ = (q ^ (n + m₀))⁻¹ := by
      rw [Units.val_pow_eq_pow_val, norm_pow, htn, inv_pow]
    have htk1 : ‖((t ^ (n + m₀) : Fˣ) : F)‖ ≤ 1 := by
      rw [htk]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1.le)
    have hoff : HarishChandraSchwartz.offIdentityNorm
        ((diagonalUnits F e₀ (t ^ (n + m₀)))⁻¹ * rationalMatrix ρ₁ x *
          diagonalUnits F e₀ (t ^ (n + m₀))) ≤ 1 := by
      refine (HarishChandraSchwartz.offIdentityNorm_conj_le e₀ _ htk1 hx₁).trans ?_
      rw [htk]
      have h1 : HarishChandraSchwartz.offIdentityNorm (rationalMatrix ρ₁ x) ≤ q ^ (n + m₀) := by
        refine (HarishChandraSchwartz.offIdentityNorm_le_glNorm _).trans ?_
        change rationalMatrixNorm F ρ₁ x ≤ _
        refine (hcomp x).trans ?_
        rw [pow_add, mul_comm (q ^ n)]
        exact mul_le_mul hm₀.le hx (zero_le_one.trans (one_le_rationalMatrixNorm F ρ₀ x))
          (pow_nonneg hq0.le _)
      rw [inv_mul_le_iff₀ (pow_pos hq0 _), mul_one]
      exact h1
    change HarishChandraSchwartz.glNorm _ ≤ 1
    rw [hconj]
    refine (HarishChandraSchwartz.glNorm_le_max_offIdentityNorm_pow
      (HarishChandraSchwartz.diagonalUnits_conj_mem e₀ _ hx₁) hd).trans ?_
    rw [max_eq_left hoff, one_pow]
  refine ⟨(MeasureTheory.mulEquivHaarChar φ)⁻¹ ^ m₀ *
      (ν {y : H | rationalMatrixNorm F ρ₁ y ≤ 1}).toNNReal,
    (MeasureTheory.mulEquivHaarChar φ)⁻¹, fun n => ?_⟩
  refine (HarishChandraSchwartz.measure_le_of_iterate_mem ν φ (hstep n)).trans_eq ?_
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hK₀c.measure_lt_top.ne, pow_add, ENNReal.coe_pow]
  ring

/-- **Polynomial volume growth of height balls.** Under the hypotheses of
`exists_measure_rationalMatrixNorm_le_pow`, there are `C` and `D` with
`ν {x ∈ H | ‖x‖_ρ₀ ≤ R} ≤ C * R ^ D` for every real `R ≥ 1`. -/
theorem exists_measure_rationalMatrixNorm_le_mul_pow
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (H : Subgroup (rationalPoints G)) (hHc : IsClosed (H : Set (rationalPoints G)))
    (hHU : H ≤ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints)
    (hHa : ∀ t : Fˣ, gmRationalPoint t ≫ χ.hom.hom ∈
      Subgroup.normalizer (H : Set (rationalPoints G)))
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular] :
    ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R →
      ν {x : H | rationalMatrixNorm F ρ₀ x ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  obtain ⟨C, B, hCB⟩ := exists_measure_rationalMatrixNorm_le_pow F χ ρ₀ hρ₀ H hHc hHU hHa ν
  have hq1 : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  generalize (LocalField.residueCardinality F : ℝ) = q at hq1 hCB
  have hq0 : 0 ≤ q := zero_le_one.trans hq1.le
  obtain ⟨D, hD⟩ := pow_unbounded_of_one_lt (B : ℝ) hq1
  refine ⟨C * q ^ D, D, fun R hR => ?_⟩
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near hR hq1
  have hqn : q ^ (n + 1) ≤ q * R := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left hn₁ hq0
  calc ν {x : H | rationalMatrixNorm F ρ₀ x ≤ R}
      ≤ ν {x : H | rationalMatrixNorm F ρ₀ x ≤ q ^ (n + 1)} :=
        measure_mono fun x hx => (show rationalMatrixNorm F ρ₀ x ≤ R from hx).trans hn₂.le
    _ ≤ C * B ^ (n + 1) := hCB (n + 1)
    _ = ENNReal.ofReal ((C : ℝ) * (B : ℝ) ^ (n + 1)) := by
        rw [← NNReal.coe_pow, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul,
          ENNReal.coe_pow]
    _ ≤ ENNReal.ofReal (C * q ^ D * R ^ D) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ C.2
        calc (B : ℝ) ^ (n + 1) ≤ (q ^ D) ^ (n + 1) := pow_le_pow_left₀ B.2 hD.le _
          _ = (q ^ (n + 1)) ^ D := by rw [← pow_mul, ← pow_mul, mul_comm]
          _ ≤ (q * R) ^ D := pow_le_pow_left₀ (pow_nonneg hq0 _) hqn _
          _ = q ^ D * R ^ D := mul_pow q R D

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
