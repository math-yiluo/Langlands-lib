import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeModulusLevelDataStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalModulusDeterminant
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalDeterminantLineStabilizerProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompactHeightEnvelope
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.Representation.Plancherel.RationalMatrixNormComparison

/-! # Integer levels and height of the actual opposite-radical weight -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Matrix
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [LocallyOfFiniteType G.X.hom] in
private theorem oppositeUnipotent_le_minimal (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) :
    Aubert.General.RationalPointFamily.oppositeUnipotent i ζ ≤
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).rationalPoints := by
  have hsign : ∀ α ∈ relativeRoots i,
      0 < latticePairing S α (-ζ) → 0 < latticePairing S α (-ν) := by
    intro α hα hneg
    have hz : latticePairing S α (-ζ) = -latticePairing S α ζ := map_neg _ _
    have hn : latticePairing S α (-ν) = -latticePairing S α ν := map_neg _ _
    rw [hz] at hneg
    rw [hn]
    have hν0 := hν α hα
    by_contra! hνp
    have hζp := hζ.pairing_nonneg_of_positive i ν (show α ∈ positiveRelativeRoots i ν from
      ⟨hα, by omega⟩)
    omega
  have h := (relativeRootSignInclusions F G hG S i hi (-ζ) (-ν)).2 hsign
  rw [groupHom_neg_comp_eq_oppositeCocharacter, groupHom_neg_comp_eq_oppositeCocharacter] at h
  exact h (Over.mk (𝟙 (Spec (CommRingCat.of F))))

private theorem exists_rationalMinimalModulusLevels
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {P U : GroupScheme (Spec (CommRingCat.of F))} {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    (hU : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iU)
    [IsAffine P.X.left] [IsAffineHom U.X.hom] {d : ℕ} (cU : Lie.FiniteCoordinates U d) :
    ∃ L : rationalPoints G → ℤ, IsLocallyConstant L ∧
      (∀ g, iwasawaWeight hPK (rationalMinimalModulus i ν) g =
        (LocalField.residueCardinality F : ℝ) ^ (-(L g : ℝ) / 2)) ∧
      (∀ g, (L g : ℝ) * Real.log (LocalField.residueCardinality F : ℝ) =
        -Real.log (LocalField.residueNormalizedAbsoluteValue F
          (Dynamic.adjointDeterminantPointValue iP (Dynamic.adjointDeterminantCharacter hP hU cU)
            (iwasawaFactor hPK g : rationalPoints G)))) := by
  let c := Dynamic.adjointDeterminantPointValue iP (Dynamic.adjointDeterminantCharacter hP hU cU)
  let q : ℝ := LocalField.residueCardinality F
  have hq : 1 < q := by
    change 1 < (LocalField.residueCardinality F : ℝ)
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hq0 : 0 < q := zero_lt_one.trans hq
  let L : rationalPoints G → ℤ := fun g =>
    -WithZero.log (FML.normalizedMultiplicativeValuation F (c (iwasawaFactor hPK g)))
  have hpow (g : rationalPoints G) :
      LocalField.residueNormalizedAbsoluteValue F (c (iwasawaFactor hPK g)) = q ^ (-(L g : ℝ)) := by
    have hc0 : c (iwasawaFactor hPK g) ≠ 0 := Units.ne_zero _
    rw [LocalField.residueNormalizedAbsoluteValue_of_ne_zero F hc0, ← Real.rpow_intCast]
    simp [q, L]
  have hw (g : rationalPoints G) :
      iwasawaWeight hPK (rationalMinimalModulus i ν) g = q ^ (-(L g : ℝ) / 2) := by
    simp only [iwasawaWeight, Real.coe_sqrt]
    rw [rationalMinimalModulus_eq_abs_adjointDeterminant hG hi hν hP hU cU]
    change Real.sqrt (LocalField.residueNormalizedAbsoluteValue F (c (iwasawaFactor hPK g))) = _
    rw [hpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  refine ⟨L, ?_, hw, fun g => ?_⟩
  · apply (IsLocallyConstant.iff_eventually_eq L).2
    intro g
    have hδ := rationalMinimalModulus_eq_one i ν hKo hKc
    filter_upwards [(isLocallyConstant_iwasawaWeight hδ hKo).eventually_eq g] with x hx
    rw [hw, hw] at hx
    have heq := congrArg Real.log hx
    rw [Real.log_rpow hq0, Real.log_rpow hq0] at heq
    have hlogs : Real.log q ≠ 0 := (Real.log_pos hq).ne'
    have he := mul_right_cancel₀ hlogs heq
    have hc : (L x : ℝ) = L g := by linarith
    exact_mod_cast hc
  · change (L g : ℝ) * Real.log q =
      -Real.log (LocalField.residueNormalizedAbsoluteValue F (c (iwasawaFactor hPK g)))
    rw [hpow, Real.log_rpow hq0, neg_mul, neg_neg]

/-- The two outer height inequalities from an eigenline with trivial stabilizer
in the opposite radical. -/
private theorem exists_eigenline_heightBounds
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    {v : n → F} (hv : v ≠ 0) {c : rationalPoints G → F}
    (hev : IsEigenvectorOn ρ v (Dynamic.parabolic χ).rationalPoints c)
    (hfix : ∀ x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints,
      (ρ.rationalMatrix x : Matrix n n F) *ᵥ v = v → x = 1)
    {K : Subgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G))) :
    ∃ C₀ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints,
        ∀ p ∈ (Dynamic.parabolic χ).rationalPoints, ∀ k ∈ K, x = p * k →
          C₁ * (1 + rationalHeight (F := F) ρ₀ x) ≤
            C₀ - Real.log (LocalField.residueNormalizedAbsoluteValue F (c p)) ∧
          C₀ - Real.log (LocalField.residueNormalizedAbsoluteValue F (c p)) ≤
            C₂ * (1 + rationalHeight (F := F) ρ₀ x) := by
  have : Nonempty n := by
    rcases isEmpty_or_nonempty n with h | h
    · exact (hv (Subsingleton.elim _ _)).elim
    · exact h
  have hχv : IsCocharacterEigenvector χ ρ v := fun t =>
    ⟨_, hev _ (gmRationalPoint_comp_mem_parabolic χ t)⟩
  obtain ⟨C, D, hC, hdispl⟩ :=
    exists_rationalMatrixNorm_le_of_weightVector F χ ρ₀ hρ₀ ρ hχv hfix
  obtain ⟨B, -, hB⟩ := exists_rationalVectorNorm_mulVec_inv_le F ρ v hK
  obtain ⟨A, hA⟩ := exists_abs_eigenvalue_le F χ ρ hv hev hK
  obtain ⟨d, M, hM, hMle⟩ := Plancherel.rationalMatrixNormComparison F G _ _ ρ₀ hρ₀ ρ
  obtain ⟨H, hH, hHK⟩ := exists_rationalHeight_le_on_compact ρ₀ K hK
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  let T := max 1 (max A B)
  have hT : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
  let e : ℝ := (D : ℝ) + 1
  have he : 0 < e := by dsimp [e]; positivity
  let C₀ := (1 + Real.log C) / e + Real.log T
  let Q := max 1 (C₀ + Real.log M + (d : ℝ) * H)
  have hQ : 1 ≤ Q := le_max_left _ _
  refine ⟨C₀, e⁻¹, Q + d, inv_pos.mpr he, by positivity, fun x hx p hp k hk hfac => ?_⟩
  set a := ‖c p‖ with ha_def
  change _ ≤ C₀ - Real.log a ∧ C₀ - Real.log a ≤ _
  have hProd := eigenvalue_mul_inv hv hev hp
  have ha : 0 < a := norm_pos_iff.2 (left_ne_zero_of_mul_eq_one hProd)
  have hcinv : c p⁻¹ = (c p)⁻¹ := eq_inv_of_mul_eq_one_right hProd
  have hvec : (ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v =
      (c p)⁻¹ • ((ρ.rationalMatrix k⁻¹ : Matrix n n F) *ᵥ v) := by
    rw [hfac, _root_.mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      hev _ ((Dynamic.parabolic χ).rationalPoints.inv_mem hp), Matrix.mulVec_smul, hcinv]
  have hTA : a ≤ T :=
    (hA x hx p hp k hk hfac).trans ((le_max_left A B).trans (le_max_right 1 _))
  have hT1 : 1 ≤ T * a⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ ha, one_mul]
    exact hTA
  have hTv : max 1 ‖(ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v‖ ≤ T * a⁻¹ := by
    refine max_le hT1 ?_
    rw [hvec, norm_smul, norm_inv, mul_comm a⁻¹]
    exact mul_le_mul_of_nonneg_right
      ((hB k hk).trans ((le_max_right A B).trans (le_max_right 1 _))) (inv_nonneg.2 ha.le)
  have hxnorm : rationalMatrixNorm F ρ₀ x ≤ C * (T * a⁻¹) ^ (D + 1) := by
    rw [← rationalMatrixNorm_inv F ρ₀ x]
    apply (hdispl _ ((Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints.inv_mem hx)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hTv _).trans
      (pow_le_pow_right₀ hT1 (Nat.le_succ _))
  have hxlog := Real.log_le_log (rationalMatrixNorm_pos ρ₀ x) hxnorm
  rw [Real.log_mul hC.ne' (pow_ne_zero _ (mul_pos hT (inv_pos.2 ha)).ne'),
    Real.log_pow, Real.log_mul hT.ne' (inv_ne_zero ha.ne'), Real.log_inv] at hxlog
  change rationalHeight (F := F) ρ₀ x ≤
    Real.log C + ((D + 1 : ℕ) : ℝ) * (Real.log T - Real.log a) at hxlog
  rw [Nat.cast_add, Nat.cast_one] at hxlog
  have hlower : e⁻¹ * (1 + rationalHeight (F := F) ρ₀ x) ≤ C₀ - Real.log a := by
    rw [inv_mul_eq_div, div_le_iff₀ he]
    dsimp [C₀]
    rw [add_sub_assoc, add_mul, div_mul_cancel₀ _ he.ne', mul_comm _ e]
    dsimp [e] at *
    linarith
  have hEigenNorm : a⁻¹ ≤ rationalMatrixNorm F ρ p := by
    have hbound := norm_mulVec_le (ρ.rationalMatrix p⁻¹ : Matrix n n F) v
    rw [hev _ ((Dynamic.parabolic χ).rationalPoints.inv_mem hp), hcinv,
      norm_smul, norm_inv] at hbound
    have hEntry := le_of_mul_le_mul_right hbound (norm_pos_iff.2 hv)
    change a⁻¹ ≤ glNorm (ρ.rationalMatrix p)
    rw [← glNorm_inv, ← map_inv]
    exact hEntry.trans (le_max_left _ _)
  have hplog := Real.log_le_log (inv_pos.2 ha) (hEigenNorm.trans (hMle p))
  rw [Real.log_inv, Real.log_mul hM.ne' (pow_ne_zero _ (rationalMatrixNorm_pos ρ₀ p).ne'),
    Real.log_pow] at hplog
  change -Real.log a ≤ Real.log M + (d : ℝ) * rationalHeight (F := F) ρ₀ p at hplog
  have hpk : p = x * k⁻¹ := by rw [hfac, mul_inv_cancel_right]
  have hpσ : rationalHeight (F := F) ρ₀ p ≤ rationalHeight (F := F) ρ₀ x + H := by
    rw [hpk]
    have h := rationalHeight_mul_le ρ₀ x k⁻¹
    rw [rationalHeight_inv] at h
    exact h.trans (add_le_add le_rfl (hHK ⟨k, hk⟩))
  refine ⟨hlower, ?_⟩
  have hdσ := mul_le_mul_of_nonneg_left hpσ (Nat.cast_nonneg (α := ℝ) d)
  have hσ := rationalHeight_nonneg ρ₀ x
  nlinarith [le_max_right (1 : ℝ) (C₀ + Real.log M + (d : ℝ) * H),
    mul_nonneg (by linarith : 0 ≤ Q) hσ]

/-- The actual minimal Iwasawa weight has measurable residue-cardinality levels on the
opposite standard radical, with both outer inequalities of Waldspurger II.3.4. -/
theorem rationalOppositeModulusLevelData : RationalOppositeModulusLevelDataStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J ζ hζ K hKo hPK hKc N _ ρ₀ hρ₀
  let χ := CommGroupScheme.groupHom ν ≫ i
  let P := Dynamic.Affine.parabolicScheme χ
  let U := Dynamic.Affine.unipotentScheme χ
  let iP := Dynamic.Affine.parabolicHom χ
  let iU := Dynamic.Affine.unipotentHom χ
  have hP : (Dynamic.parabolic χ).IsRepresentedBy iP :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hU : (Dynamic.unipotent χ).IsRepresentedBy iU :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have : IsAffineHom P.X.hom := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  have : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  have hUc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have : IsAffineHom U.X.hom := hUc.isAffineHom
  have : LocallyOfFiniteType U.X.hom := hUc.locallyOfFiniteType
  have : Mono iU.hom.hom := hU.1
  let cG := Lie.finiteCoordinates G
  let cU := Lie.finiteCoordinates U
  obtain ⟨L, hL, hw, hlog⟩ := exists_rationalMinimalModulusLevels hG hi hν hKo hKc hPK hP hU cU
  have hv := Dynamic.adjointExteriorCoordinates_ne_zero (iU := iU) cG cU (CommAlgCat.of _ F)
    (Field.toIsField F)
  have hev := Dynamic.isEigenvectorOn_adjointExteriorCoordinates hP hU cG cU
  have hfix := rationalMinimalDeterminantLineStabilizer F G hG S i hi ν hν U iU hU _ _ cG cU
  obtain ⟨C₀, C₁, C₂, hC₁, hC₂, hbounds⟩ :=
    exists_eigenline_heightBounds χ ρ₀ hρ₀ _ hv hev hfix hKc
  have hsub := oppositeUnipotent_le_minimal hG hi hν hζ
  refine ⟨fun x => L x, hL.continuous.measurable.comp measurable_subtype_coe, fun x => hw x,
    C₀, C₁, C₂, hC₁, hC₂, fun x => ?_⟩
  let p := iwasawaFactor hPK (x : rationalPoints G)
  have hPeq : standardParabolicPoints i ν ∅ = (Dynamic.parabolic χ).rationalPoints := by
    change (standardParabolic i ν ∅).carrier _ = (Dynamic.parabolic χ).carrier _
    rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
  have hp : (p : rationalPoints G) ∈ (Dynamic.parabolic χ).rationalPoints := hPeq.le p.2
  obtain ⟨k, hk, hx⟩ := exists_iwasawaFactor hPK (x : rationalPoints G)
  change _ ≤ C₀ + (L x : ℝ) * Real.log (LocalField.residueCardinality F : ℝ) ∧
    C₀ + (L x : ℝ) * Real.log (LocalField.residueCardinality F : ℝ) ≤ _
  rw [hlog]
  simpa only [sub_eq_add_neg] using hbounds x (hsub x.2) p hp k hk hx

end Langlands.HarishChandraSchwartz
