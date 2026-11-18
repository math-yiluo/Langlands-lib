import Langlands.GroupScheme.MatrixRepresentation.ParabolicOrbitWeightGap
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLineHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.BruhatTits.Cartan.RenardLeviCones

/-! # Actual norms of maximal-parabolic orbit coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Universal vanishing specializes to the actual field-valued entry. -/
theorem rationalMatrix_entry_eq_zero_of_pointMatrix_entry_eq_zero
    (tau : MatrixRepresentation G n) (g : rationalPoints G) (r j : n)
    (h : (tau.pointMatrix (Over.mk (𝟙 _)) g :
      Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤)) r j = 0) :
    (tau.rationalMatrix g : Matrix n n F) r j = 0 := by
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    ((tau.pointMatrix (Over.mk (𝟙 _)) g : Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤)) r j) = 0
  rw [h, map_zero]

/-- Actual conjugation scales each orbit coordinate by its actual torus character ratio. -/
theorem HasTorusCharacterDiagonal.rationalMatrix_conj_entry
    {tau : MatrixRepresentation G n} {i : T.toGrp ⟶ G}
    {characters : n → rationalCharacters T.toGrp}
    (hdiag : tau.HasTorusCharacterDiagonal i characters)
    (a : rationalPoints T.toGrp) (g : rationalPoints G) (r j : n) :
    (tau.rationalMatrix (rationalPoints.map i a * g * (rationalPoints.map i a)⁻¹) :
      Matrix n n F) r j =
        (rationalCharacterEval (characters r) a : F) *
          (tau.rationalMatrix g : Matrix n n F) r j *
            (rationalCharacterEval (characters j) a : F)⁻¹ := by
  rw [← map_inv (rationalPoints.map i), map_mul, map_mul, Units.val_mul,
    Units.val_mul, hdiag.rationalMatrix_eq_diagonal a,
    hdiag.rationalMatrix_eq_diagonal a⁻¹]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, map_inv, Units.val_inv_eq_inv_val]


/-- An exact all-test line stabilizer remains exact on actual rational points
and field-valued coordinate vectors. -/
theorem HasExactCoordinateLineStabilizer.isRationalLineStabilizer
    {tau : MatrixRepresentation G n} {S : SubgroupFunctor G} {j : n}
    (h : tau.HasExactCoordinateLineStabilizer S j) :
    tau.IsRationalLineStabilizer j S.rationalPoints := by
  intro g
  rw [h (Over.mk (𝟙 _)) g]
  exact (exists_mulVec_single_eq_smul_map_iff
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv _ j).symm

/-- A torus weight basis makes the distinguished coordinate of every
opposite-unipotent orbit point exactly one. -/
theorem rationalMatrix_line_entry_eq_one_of_mem_opposite_unipotent
    (tau : MatrixRepresentation G n)
    (chi : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (e : n → ℤ)
    (hchi : chi ≫ tau = GeneralLinear.diagonalCocharacter n (CommRingCat.of F) e)
    (u : rationalPoints G)
    (hu : u ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints) (j : n) :
    (tau.rationalMatrix u : Matrix n n F) j j = 1 := by
  have huj := tau.pointMatrix_entry_eq_one_of_mem_opposite_unipotent chi e hchi hu (le_refl (e j))
  rw [Matrix.one_apply_eq] at huj
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    ((tau.pointMatrix (Over.mk (𝟙 _)) u :
      Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤)) j j) = 1
  rw [huj, map_one]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [Fintype n] [DecidableEq n] in
/-- The norm of the actual character ratio is the exponential of its positive
integer order difference. -/
theorem norm_character_ratio_eq_exp (characters : n → rationalCharacters T.toGrp)
    (a : rationalPoints T.toGrp) (r j : n) :
    let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ‖(rationalCharacterEval (characters r) a : F)‖ *
        ‖(rationalCharacterEval (characters j) a : F)‖⁻¹ =
      Real.exp (Real.log (LocalField.residueCardinality F : ℝ) *
        (RenardLeviCones.characterOrder T
          ((rationalCharacters.equivCharacterLattice T) (characters j) -
            (rationalCharacters.equivCharacterLattice T) (characters r)) a : ℝ)) := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  dsimp only
  have hnorm (chi : rationalCharacters T.toGrp) :
      ‖(rationalCharacterEval chi a : F)‖ =
        Real.exp (Real.log (LocalField.residueCardinality F : ℝ) *
          (-((rationalCharacterValuation T.toGrp a).toAdd chi : ℝ))) := by
    have hq : 0 < (LocalField.residueCardinality F : ℝ) := by
      exact_mod_cast (zero_lt_one.trans (LocalField.residueCardinality_gt_one F))
    change LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval chi a : F) = _
    rw [← rationalNormLogarithm_spec T.toGrp a chi,
      rationalNormLogarithm_eq_intValuation, Real.rpow_def_of_pos hq]
  rw [hnorm, hnorm, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  simp only [RenardLeviCones.characterOrder, map_sub, AddEquiv.symm_apply_apply,
    Int.cast_sub]
  ring


/-- Multiplication on the right by the line stabilizer scales every orbit
coordinate by one common positive field norm. -/
theorem IsRationalLineStabilizer.orbitCoordinate_mul
    {tau : MatrixRepresentation G n} {j : n} {S : Subgroup (rationalPoints G)}
    (h : tau.IsRationalLineStabilizer j S) (u : rationalPoints G)
    (p : rationalPoints G) (hp : p ∈ S) :
    let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ∃ c > 0, ∀ r : n, ‖(tau.rationalMatrix (u * p) : Matrix n n F) r j‖ =
      c * ‖(tau.rationalMatrix u : Matrix n n F) r j‖ := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  obtain ⟨c, hc⟩ := h.exists_unit_of_mem hp
  dsimp only
  refine ⟨‖(c : F)‖, norm_pos_iff.mpr c.ne_zero, fun r => ?_⟩
  have hv : (tau.rationalMatrix (u * p) : Matrix n n F) *ᵥ Pi.single j 1 =
      (c : F) • ((tau.rationalMatrix u : Matrix n n F) *ᵥ Pi.single j 1) := by
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]
  have hentry := congrFun hv r
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hentry
  rw [hentry, norm_mul]

section Relative

variable [IsAffineHom G.X.hom]

/-- The algebraic omitted-root gap holds at every point of the actual full
closed torus chamber, including its compact norm-kernel factor. -/
theorem maximalParabolic_orbitOrder_gap
    (tau : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    {characters : n → rationalCharacters T.toGrp}
    (hdiag : tau.HasTorusCharacterDiagonal i characters)
    (j : n) (hline0 : (tau.restrict (Standard.parabolicHom i nu ∅)).PreservesCoordinateLine j)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    (hline : (tau.restrict
      (Standard.parabolicHom i nu (simpleRelativeRoots i nu \ {alpha}))).PreservesCoordinateLine j)
    (g : rationalPoints G) (r : n) (hr : r ≠ j)
    (hactive : (tau.rationalMatrix g : Matrix n n F) r j ≠ 0)
    (a : rationalPoints T.toGrp)
    (ha : ∀ beta ∈ simpleRelativeRoots i nu, 0 ≤ RenardLeviCones.characterOrder T beta a) :
    RenardLeviCones.characterOrder T alpha a ≤ latticePairing T alpha zeta *
      RenardLeviCones.characterOrder T
        ((rationalCharacters.equivCharacterLattice T) (characters j) -
          (rationalCharacters.equivCharacterLattice T) (characters r)) a := by
  obtain ⟨c, hc, _⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F T
    hi.isSplitSubtorus.1).2.2 a
  have hval := (CocharacterUniformizer.mem_normKernel_mul_section_inv_iff F T a c).mp hc
  have hdom : ∀ beta ∈ simpleRelativeRoots i nu, 0 ≤ latticePairing T beta c.toAdd := by
    intro beta hbeta
    rw [← hval beta]
    exact ha beta hbeta
  have hactive' : (tau.pointMatrix (Over.mk (𝟙 _)) g :
      Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤)) r j ≠ 0 := by
    intro hz
    exact hactive (rationalMatrix_entry_eq_zero_of_pointMatrix_entry_eq_zero tau g r j hz)
  have hg := tau.maximalParabolic_orbitPairing_gap i hG hi nu hnu hdiag j hline0
    alpha halpha zeta hzeta hline (Over.mk (𝟙 _)) g r hr hactive' c.toAdd hdom
  simpa only [← hval, RenardLeviCones.characterOrder] using hg


/-- Every off-line orbit coordinate grows at least exponentially in the
omitted simple-root order under actual chamber conjugation. Zero coordinates
satisfy the same inequality. -/
theorem maximalParabolic_orbit_norm_growth
    (tau : MatrixRepresentation G n) (i : T.toGrp ⟶ G)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    {characters : n → rationalCharacters T.toGrp}
    (hdiag : tau.HasTorusCharacterDiagonal i characters)
    (j : n) (hline0 : (tau.restrict (Standard.parabolicHom i nu ∅)).PreservesCoordinateLine j)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    (hline : (tau.restrict
      (Standard.parabolicHom i nu (simpleRelativeRoots i nu \ {alpha}))).PreservesCoordinateLine j)
    (g : rationalPoints G) (r : n) (hr : r ≠ j)
    (a : rationalPoints T.toGrp)
    (ha : ∀ beta ∈ simpleRelativeRoots i nu, 0 ≤ RenardLeviCones.characterOrder T beta a) :
    let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    Real.exp (Real.log (LocalField.residueCardinality F : ℝ) /
        (latticePairing T alpha zeta : ℝ) * (RenardLeviCones.characterOrder T alpha a : ℝ)) *
      ‖(tau.rationalMatrix g : Matrix n n F) r j‖ ≤
        ‖(tau.rationalMatrix (rationalPoints.map i a * g * (rationalPoints.map i a)⁻¹) :
          Matrix n n F) r j‖ := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  dsimp only
  by_cases hzero : (tau.rationalMatrix g : Matrix n n F) r j = 0
  · rw [hzero, norm_zero, mul_zero]
    exact norm_nonneg _
  have hgap : (RenardLeviCones.characterOrder T alpha a : ℝ) ≤
      (latticePairing T alpha zeta : ℝ) *
        (RenardLeviCones.characterOrder T
          ((rationalCharacters.equivCharacterLattice T) (characters j) -
            (rationalCharacters.equivCharacterLattice T) (characters r)) a : ℝ) := by
    exact_mod_cast tau.maximalParabolic_orbitOrder_gap i hG hi nu hnu hdiag j hline0
      alpha halpha zeta hzeta hline g r hr hzero a ha
  have hm : 0 < (latticePairing T alpha zeta : ℝ) := by
    exact_mod_cast hzeta.2.2 alpha halpha (by simp)
  have hlogq : 0 ≤ Real.log (LocalField.residueCardinality F : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (LocalField.residueCardinality_gt_one F).le
  have hexp : Real.log (LocalField.residueCardinality F : ℝ) /
        (latticePairing T alpha zeta : ℝ) * (RenardLeviCones.characterOrder T alpha a : ℝ) ≤
      Real.log (LocalField.residueCardinality F : ℝ) *
        (RenardLeviCones.characterOrder T
          ((rationalCharacters.equivCharacterLattice T) (characters j) -
            (rationalCharacters.equivCharacterLattice T) (characters r)) a : ℝ) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hm).mpr (by nlinarith [hgap])) hlogq
  calc
    _ ≤ Real.exp (Real.log (LocalField.residueCardinality F : ℝ) *
        (RenardLeviCones.characterOrder T
          ((rationalCharacters.equivCharacterLattice T) (characters j) -
            (rationalCharacters.equivCharacterLattice T) (characters r)) a : ℝ)) *
          ‖(tau.rationalMatrix g : Matrix n n F) r j‖ :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (norm_nonneg _)
    _ = _ := by
      rw [hdiag.rationalMatrix_conj_entry a g r j, norm_mul, norm_mul, norm_inv,
        ← norm_character_ratio_eq_exp characters a r j]
      ring

end Relative

section NormBounds

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.HarishChandraSchwartz

variable [Nonempty n]

/-- Polynomial comparison with an arbitrary closed embedding gives one
exponential coordinate bound in that embedding's original logarithmic height. -/
theorem exists_orbitCoordinate_exp_bound
    {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    (rho : MatrixRepresentation G m) (hrho : IsClosedSubgroup rho)
    (tau : MatrixRepresentation G n) :
    let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ∃ C > 0, ∀ (g : rationalPoints G) (r j : n),
      ‖(tau.rationalMatrix g : Matrix n n F) r j‖ ≤
        Real.exp (C * (1 + rationalHeight (F := F) rho g)) := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  obtain ⟨d, c, hc, hb⟩ := rationalMatrixNormComparison F G m n rho hrho tau
  dsimp only
  refine ⟨|Real.log c| + (d : ℝ) + 1, by positivity, fun g r j => ?_⟩
  have hpower : c * rationalMatrixNorm F rho g ^ d =
      Real.exp (Real.log c + (d : ℝ) * rationalHeight (F := F) rho g) := by
    rw [Real.exp_add, Real.exp_nat_mul, rationalHeight,
      Real.exp_log hc, Real.exp_log (rationalMatrixNorm_pos rho g)]
  calc
    _ ≤ rationalMatrixNorm F tau g := norm_le_glNorm _ r j
    _ ≤ c * rationalMatrixNorm F rho g ^ d := hb g
    _ = _ := hpower
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs := rationalHeight_nonneg rho g
      have hlog := le_abs_self (Real.log c)
      have habs := abs_nonneg (Real.log c)
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith

/-- On a compact set some orbit coordinate is uniformly bounded away from
zero, since every representing matrix is invertible. -/
theorem exists_orbitCoordinate_lower_bound [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (tau : MatrixRepresentation G n) (j : n) {K : Set (rationalPoints G)}
    (hK : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact K) :
    let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ∃ D ≥ 0, ∀ k ∈ K, ∃ r : n,
      Real.exp (-D) ≤ ‖(tau.rationalMatrix k : Matrix n n F) r j‖ := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_rationalHeight tau).continuousOn
  dsimp only
  refine ⟨max B 0, le_max_right _ _, fun k hk => ?_⟩
  have hnorm : rationalMatrixNorm F tau k ≤ Real.exp (max B 0) := by
    apply (Real.log_le_iff_le_exp (rationalMatrixNorm_pos tau k)).mp
    exact (hB (Set.mem_image_of_mem _ hk)).trans (le_max_left _ _)
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
    (fun r : n => ‖(tau.rationalMatrix k : Matrix n n F) r j‖) Finset.univ_nonempty
  have hv : ‖(tau.rationalMatrix k : Matrix n n F) *ᵥ Pi.single j 1‖ ≤
      ‖(tau.rationalMatrix k : Matrix n n F) r j‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro s
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hr s (Finset.mem_univ s)
  have hvec : ‖(Pi.single j (1 : F) : n → F)‖ ≤ rationalMatrixNorm F tau k *
      ‖(tau.rationalMatrix k : Matrix n n F) *ᵥ Pi.single j 1‖ := by
    calc
      _ = ‖(((tau.rationalMatrix k)⁻¹ : GL n F) : Matrix n n F) *ᵥ
          ((tau.rationalMatrix k : Matrix n n F) *ᵥ Pi.single j 1)‖ := by
        congr 1
        rw [Matrix.mulVec_mulVec]
        change Pi.single j 1 =
          (((tau.rationalMatrix k)⁻¹ * tau.rationalMatrix k : GL n F) : Matrix n n F) *ᵥ
            Pi.single j 1
        rw [inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      _ ≤ entryNorm (((tau.rationalMatrix k)⁻¹ : GL n F) : Matrix n n F) *
          ‖(tau.rationalMatrix k : Matrix n n F) *ᵥ Pi.single j 1‖ := norm_mulVec_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  rw [Pi.norm_single, norm_one] at hvec
  refine ⟨r, ?_⟩
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀' (Real.exp_pos _)]
  exact hvec.trans (mul_le_mul hnorm hv (norm_nonneg _) (Real.exp_pos _).le)

end NormBounds



section Neighborhood

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.HarishChandraSchwartz

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field

omit [LocallyOfFiniteType G.X.hom] in
/-- A proper orbit-height bound and a trivial vector stabilizer recover every
open subgroup of the opposite radical from sufficiently small off-line
coordinates. Only compactness and continuity are used for this recovery. -/
theorem exists_small_orbitCoordinates_mem_open
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho) (tau : MatrixRepresentation G n) (j : n)
    (U : Subgroup (rationalPoints G)) (hU : IsClosed (U : Set (rationalPoints G)))
    (hline : ∀ u ∈ U, (tau.rationalMatrix u : Matrix n n F) j j = 1)
    (hfix : ∀ u ∈ U, (tau.rationalMatrix u : Matrix n n F) *ᵥ Pi.single j 1 =
      Pi.single j 1 → u = 1)
    (C : ℝ) (D : ℕ)
    (hbound : ∀ u ∈ U, rationalMatrixNorm F rho u ≤
      C * max 1 (rationalVectorNorm F ((tau.rationalMatrix u : Matrix n n F) *ᵥ
        Pi.single j 1)) ^ D)
    (Gamma : OpenSubgroup U) :
    let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ∃ epsilon > 0, ∀ u : U,
      (∀ r : n, r ≠ j → ‖(tau.rationalMatrix u : Matrix n n F) r j‖ ≤ epsilon) → u ∈ Gamma := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  dsimp only
  let S : Set (rationalPoints G) := {u | u ∈ U ∧ ∀ r : n,
    LocalField.residueNormalizedAbsoluteValue F ((tau.rationalMatrix u : Matrix n n F) r j) ≤ 1}
  have hSclosed : IsClosed S := by
    have hset : S = (U : Set (rationalPoints G)) ∩ ⋂ r : n,
        {u | LocalField.residueNormalizedAbsoluteValue F
          ((tau.rationalMatrix u : Matrix n n F) r j) ≤ 1} := by
      ext u
      simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe]
    rw [hset]
    exact hU.inter (isClosed_iInter fun r => isClosed_le
      ((continuous_residueNormalizedAbsoluteValue F).comp
        (tau.continuous_rationalMatrix_entry r j)) continuous_const)
  have hScompact : IsCompact S := by
    apply (isCompact_rationalMatrixNorm_le F rho hrho C).of_isClosed_subset hSclosed
    intro u hu
    have hv : rationalVectorNorm F ((tau.rationalMatrix u : Matrix n n F) *ᵥ
        Pi.single j 1) ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro r
      simp only [Matrix.mulVec_single_one, Matrix.col_apply]
      change LocalField.residueNormalizedAbsoluteValue F
        ((tau.rationalMatrix u : Matrix n n F) r j) ≤ 1
      exact hu.2 r
    have hb := hbound u hu.1
    rw [max_eq_left hv, one_pow, mul_one] at hb
    exact hb
  obtain ⟨V, hV, hGamma⟩ := isOpen_induced_iff.mp Gamma.isOpen
  have hmem (u : U) : u ∈ Gamma ↔ (u : rationalPoints G) ∈ V :=
    (Set.ext_iff.mp hGamma u).symm
  have hone : (1 : rationalPoints G) ∈ V := (hmem 1).mp Gamma.one_mem
  let f : rationalPoints G → ℝ := fun u => rationalVectorNorm F
    ((tau.rationalMatrix u : Matrix n n F) *ᵥ Pi.single j 1 - Pi.single j 1)
  have hf : Continuous f := by
    apply continuous_norm_pi_comp (f := fun u : rationalPoints G =>
      (tau.rationalMatrix u : Matrix n n F) *ᵥ Pi.single j 1 - Pi.single j 1)
    intro r
    change Continuous fun u : rationalPoints G => LocalField.residueNormalizedAbsoluteValue F
      (((tau.rationalMatrix u : Matrix n n F) *ᵥ (Pi.single j (1 : F) : n → F) -
        (Pi.single j (1 : F) : n → F) : n → F) r)
    exact continuous_absoluteValue_rationalMatrix_mulVec_sub_apply F tau (Pi.single j 1) r
  have hsmall (u : U) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
      (hu : ∀ r : n, r ≠ j → ‖(tau.rationalMatrix u : Matrix n n F) r j‖ ≤ epsilon) :
      f u ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg hepsilon).mpr
    intro r
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.sub_apply,
        Pi.single_eq_same, hline u u.2, sub_self, norm_zero] using hepsilon
    · simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.sub_apply,
        Pi.single_eq_of_ne hr, sub_zero] using hu r hr
  have hsmallS (u : U) (epsilon : ℝ) (hepsilon : epsilon ≤ 1)
      (hu : ∀ r : n, r ≠ j → ‖(tau.rationalMatrix u : Matrix n n F) r j‖ ≤ epsilon) :
      (u : rationalPoints G) ∈ S := by
    refine ⟨u.2, fun r => ?_⟩
    by_cases hr : r = j
    · subst r
      rw [hline u u.2, map_one]
    · exact (hu r hr).trans hepsilon
  have houtside : IsCompact (S ∩ Vᶜ) := hScompact.inter_right hV.isClosed_compl
  by_cases hne : (S ∩ Vᶜ).Nonempty
  · obtain ⟨u0, hu0, hmin⟩ := houtside.exists_isMinOn hne hf.continuousOn
    have hpos : 0 < f u0 := by
      apply norm_pos_iff.mpr
      intro hz
      have huone := hfix u0 hu0.1.1 (sub_eq_zero.mp hz)
      exact hu0.2 (huone ▸ hone)
    refine ⟨min 1 (f u0 / 2), lt_min zero_lt_one (half_pos hpos), fun u hu => ?_⟩
    apply (hmem u).mpr
    by_contra hnot
    have huS := hsmallS u _ (min_le_left _ _) hu
    have hfu := hsmall u _ (le_min zero_le_one (half_pos hpos).le) hu
    have hmu := hmin ⟨huS, hnot⟩
    change f u0 ≤ f u at hmu
    have hle := min_le_right 1 (f u0 / 2)
    linarith
  · refine ⟨1, zero_lt_one, fun u hu => (hmem u).mpr ?_⟩
    by_contra hnot
    exact hne ⟨u, hsmallS u 1 le_rfl hu, hnot⟩


/-- Recovery of every open subgroup from the actual opposite-unipotent orbit
coordinates. The field norm is the residue-normalized absolute value. -/
def HasOrbitCoordinateNeighborhoodRecovery (tau : MatrixRepresentation G n) (j : n)
    (U : Subgroup (rationalPoints G)) : Prop :=
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  ∀ Gamma : OpenSubgroup U, ∃ C5 > 0, ∀ u : U,
    (∀ r : n, r ≠ j → ‖(tau.rationalMatrix u : Matrix n n F) r j‖ ≤ Real.exp (-C5)) →
      u ∈ Gamma

omit [LocallyOfFiniteType G.X.hom] in
/-- The local orbit-coordinate recovery required in II.3.5 is proved for
an actual parabolic eigenline from its exact stabilizer and diagonal
cocharacter equation. The opposite-orbit height comparison supplies
compactness, so no separability of the orbit map is needed. -/
theorem hasOrbitCoordinateNeighborhoodRecovery_of_parabolic_line
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho) (tau : MatrixRepresentation G n) (j : n)
    (chi : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (e : n → ℤ)
    (hchi : chi ≫ tau = GeneralLinear.diagonalCocharacter n (CommRingCat.of F) e)
    (hstab : tau.IsRationalLineStabilizer j (Dynamic.parabolic chi).rationalPoints) :
    tau.HasOrbitCoordinateNeighborhoodRecovery j
      (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints := by
  let U := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints
  have hU : IsClosed (U : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (Dynamic.unipotent (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.isClosedSubgroup_unipotentHom (Dynamic.oppositeCocharacter chi))
  have hline : ∀ u ∈ U, (tau.rationalMatrix u : Matrix n n F) j j = 1 := fun u hu =>
    rationalMatrix_line_entry_eq_one_of_mem_opposite_unipotent tau chi e hchi u hu j
  have hfix : ∀ u ∈ U, (tau.rationalMatrix u : Matrix n n F) *ᵥ Pi.single j 1 =
      Pi.single j 1 → u = 1 := fun u hu hfixed =>
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic chi hu
      (hstab.mem_of_mulVec_eq hfixed)
  have heigen : tau.IsCocharacterEigenvector chi (Pi.single j 1) := fun t => by
    obtain ⟨c, hc⟩ := hstab.exists_unit_of_mem (gmRationalPoint_comp_mem_parabolic chi t)
    exact ⟨c, hc⟩
  obtain ⟨C, D, _, hbound⟩ :=
    exists_rationalMatrixNorm_le_of_weightVector F chi rho hrho tau heigen hfix
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  intro Gamma
  obtain ⟨epsilon, hepsilon, hsmall⟩ :=
    exists_small_orbitCoordinates_mem_open rho hrho tau j U hU hline hfix C D hbound Gamma
  refine ⟨|Real.log epsilon| + 1, by positivity, fun u hu => hsmall u ?_⟩
  intro r hr
  refine (hu r hr).trans ?_
  calc
    Real.exp (-(|Real.log epsilon| + 1)) ≤ Real.exp (Real.log epsilon) := by
      apply Real.exp_le_exp.mpr
      have hlog := neg_abs_le (Real.log epsilon)
      linarith
    _ = epsilon := Real.exp_log hepsilon

end Neighborhood

end Langlands.GroupScheme.MatrixRepresentation
