import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLineCharacter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.EigenlineIwasawaBounds
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompactHeightEnvelope
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalModulusDeterminant
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeWeightContractionStatement

/-! # Contraction of an opposite-unipotent weight-vector orbit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.GeneralLinear

namespace Langlands.HarishChandraSchwartz

private theorem norm_mulVec_diagonal_conj_le
    {F : Type u} [NormedField F] {n : Type} [Fintype n] [DecidableEq n]
    {e : n → ℤ} {g : GL n F} (hg : g ∈ blockUnipotentSubgroup F (-e))
    {b : ℤ} {w : n → F} (hw : ∀ i, e i ≠ b → w i = 0)
    {t : Fˣ} (ht : ‖(t : F)‖ ≤ 1) (m : ℕ) :
    ‖(((diagonalUnits F e (t ^ m))⁻¹ * g * diagonalUnits F e (t ^ m) : GL n F) :
        Matrix n n F) *ᵥ w‖ ≤ max ‖w‖ (‖(t : F)‖ ^ m * ‖(g : Matrix n n F) *ᵥ w‖) := by
  let s := t ^ m
  have hs : 0 < ‖(s : F)‖ := norm_pos_iff.2 s.ne_zero
  have hsn : ‖(s : F)‖ ≤ 1 := by
    rw [show (s : F) = (t : F) ^ m from Units.val_pow_eq_pow_val _ _, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ht
  have hw' (i : n) (hi : b ≤ e i) : ((g : Matrix n n F) *ᵥ w) i = w i := by
    rw [mem_blockUnipotentSubgroup] at hg
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · rw [hg i i le_rfl, Matrix.one_apply_eq, one_mul]
    · intro j _ hji
      by_cases hj : e j = b
      · rw [hg i j (by simpa [hj] using hi), Matrix.one_apply_ne (Ne.symm hji), zero_mul]
      · rw [hw j hj, mul_zero]
    · simp
  have hdiag : (diagonalUnits F e s : Matrix n n F) *ᵥ w = ((s ^ b : Fˣ) : F) • w := by
    ext i
    rw [coe_diagonalUnits, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hi : e i = b
    · rw [hi]
    · rw [hw i hi, mul_zero, mul_zero]
  have hcoord (i : n) :
      ((((diagonalUnits F e s)⁻¹ * g * diagonalUnits F e s : GL n F) : Matrix n n F) *ᵥ w) i =
        ((s ^ (b - e i) : Fˣ) : F) * ((g : Matrix n n F) *ᵥ w) i := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hdiag, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← map_inv,
      coe_diagonalUnits, Matrix.mulVec_diagonal, ← mul_assoc, ← Units.val_mul,
      _root_.inv_zpow', ← _root_.zpow_add, sub_eq_add_neg]
  change ‖(((diagonalUnits F e s)⁻¹ * g * diagonalUnits F e s : GL n F) : Matrix n n F) *ᵥ w‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (le_max_left _ _ |>.trans' (norm_nonneg _))).2
  intro i
  rw [hcoord]
  by_cases hi : b ≤ e i
  · rw [hw' i hi]
    by_cases he : e i = b
    · rw [he, sub_self, zpow_zero, Units.val_one, one_mul]
      exact (norm_le_pi_norm _ i).trans (le_max_left _ _)
    · rw [hw i he, mul_zero, norm_zero]
      exact (norm_nonneg _).trans (le_max_left _ _)
  · rw [norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow]
    have hpow : ‖(s : F)‖ ^ (b - e i) ≤ ‖(t : F)‖ ^ m := by
      have h := zpow_le_zpow_right_of_le_one₀ hs hsn (show (1 : ℤ) ≤ b - e i by omega)
      simpa only [zpow_one, show (s : F) = (t : F) ^ m from Units.val_pow_eq_pow_val _ _,
        norm_pow] using h
    exact (mul_le_mul hpow (norm_le_pi_norm _ i) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)).trans
      (le_max_right _ _)

end Langlands.HarishChandraSchwartz

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.HarishChandraSchwartz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- On an opposite unipotent orbit, inverse conjugation by powers of a
cocharacter value contracts every changed coordinate of a weight vector. -/
private theorem exists_rationalVectorNorm_conj_pow_le
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) {v : n → F}
    (hv : IsCocharacterEigenvector χ ρ v)
    (t : Fˣ) (ht : LocalField.residueNormalizedAbsoluteValue F (t : F) < 1) :
    let a : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (x : rationalPoints G),
        x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints →
        rationalVectorNorm F ((ρ.rationalMatrix ((a ^ m)⁻¹ * x * a ^ m) : Matrix n n F) *ᵥ v) ≤
          C * max (rationalVectorNorm F v)
            (LocalField.residueNormalizedAbsoluteValue F (t : F) ^ m *
              rationalVectorNorm F ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v)) := by
  let a : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom
  obtain ⟨g, e, hg⟩ := exists_innerIso_comp_eq_diagonalCocharacter F (χ ≫ ρ)
  let ρ' : MatrixRepresentation G n := ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom
  have hχ : χ ≫ ρ' = diagonalCocharacter n (CommRingCat.of F) e := by
    change χ ≫ ρ ≫ _ = _
    rw [← Category.assoc, hg]
  let J := rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g
  let w := (J : Matrix n n F) *ᵥ v
  have htrans (x : rationalPoints G) :
      (ρ'.rationalMatrix x : Matrix n n F) *ᵥ w =
        (J : Matrix n n F) *ᵥ ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v) :=
    rationalMatrix_comp_innerIso_mulVec ρ g x v
  obtain ⟨c, hc⟩ := hv t
  have hdiag : (diagonalUnits F e t : Matrix n n F) *ᵥ w = c • w := by
    rw [← rationalMatrix_gmRationalPoint_comp hχ t, htrans, hc, Matrix.mulVec_smul]
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  have ht' : ‖(t : F)‖ < 1 := ht
  obtain ⟨b, hwb⟩ := exists_weight_block_of_mulVec_eq_smul ht'.ne hdiag
  obtain ⟨A, hA, hAb⟩ := exists_norm_mulVec_le (J : Matrix n n F)
  obtain ⟨B, hB, hBb⟩ := exists_norm_mulVec_le ((J⁻¹ : GL n F) : Matrix n n F)
  let A' := max 1 A
  let B' := max 1 B
  have hA' : 0 < A' := zero_lt_one.trans_le (le_max_left _ _)
  have hB' : 0 < B' := zero_lt_one.trans_le (le_max_left _ _)
  have hupper (y : n → F) : ‖(J : Matrix n n F) *ᵥ y‖ ≤ A' * ‖y‖ :=
    (hAb y).trans (mul_le_mul_of_nonneg_right (le_max_right 1 _) (norm_nonneg _))
  have hlower (y : n → F) : ‖y‖ ≤ B' * ‖(J : Matrix n n F) *ᵥ y‖ := by
    have h := hBb ((J : Matrix n n F) *ᵥ y)
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right 1 _) (norm_nonneg _))
  refine ⟨B' * A', mul_pos hB' hA', fun m x hx => ?_⟩
  have hx' : ρ'.rationalMatrix x ∈ blockUnipotentSubgroup F (-e) := by
    rw [rationalMatrix_mem_blockUnipotentSubgroup_iff]
    have h := Dynamic.unipotent_le_comap _ ρ' _ hx
    rw [SubgroupFunctor.mem_comap, Dynamic.oppositeCocharacter, Category.assoc, hχ,
      inv_comp_diagonalCocharacter, unipotent_diagonalCocharacter] at h
    exact h
  have hpow : ρ'.rationalMatrix (a ^ m) = diagonalUnits F e (t ^ m) := by
    rw [map_pow, map_pow]
    exact congrArg (fun y : GL n F => y ^ m) (rationalMatrix_gmRationalPoint_comp hχ t)
  have hconj := norm_mulVec_diagonal_conj_le hx' hwb ht'.le m
  rw [← hpow, ← map_inv, ← map_mul, ← map_mul, htrans, htrans] at hconj
  change ‖(ρ.rationalMatrix ((a ^ m)⁻¹ * x * a ^ m) : Matrix n n F) *ᵥ v‖ ≤ _
  have hq : 0 ≤ ‖(t : F)‖ ^ m := pow_nonneg (norm_nonneg _) _
  calc
    _ ≤ B' * ‖(J : Matrix n n F) *ᵥ
        ((ρ.rationalMatrix ((a ^ m)⁻¹ * x * a ^ m) : Matrix n n F) *ᵥ v)‖ := hlower _
    _ ≤ B' * max ‖w‖ (‖(t : F)‖ ^ m *
          ‖(J : Matrix n n F) *ᵥ ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v)‖) :=
      mul_le_mul_of_nonneg_left hconj hB'.le
    _ ≤ B' * (A' * max ‖v‖
          (‖(t : F)‖ ^ m * ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ v‖)) := by
      apply mul_le_mul_of_nonneg_left _ hB'.le
      refine max_le ((hupper v).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hA'.le)) ?_
      calc
        _ ≤ ‖(t : F)‖ ^ m * (A' * ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ v‖) :=
          mul_le_mul_of_nonneg_left (hupper _) hq
        _ = A' * (‖(t : F)‖ ^ m * ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ v‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hA'.le
    _ = _ := by rw [mul_assoc]; rfl

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.HarishChandraSchwartz

open Langlands.GroupScheme Langlands.GroupScheme.MatrixRepresentation
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {P K : Subgroup (rationalPoints G)} (hPK : IsIwasawaPair P K)
  {δ : P →* ℝ≥0ˣ}
  {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) {v : n → F}
  {c : rationalPoints G → F}

/-- The inverse squared Iwasawa weight is comparable to the norm of the action
of the inverse on the common eigenvector, by compactness of the right factor. -/
private theorem exists_inverse_iwasawaWeight_sq_bounds
    (hv : v ≠ 0) (hev : IsEigenvectorOn ρ v P c)
    (hδ : ∀ p : P, (((δ p : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      LocalField.residueNormalizedAbsoluteValue F (c p))
    (hK : IsCompact (K : Set (rationalPoints G))) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ x : rationalPoints G,
      (iwasawaWeight hPK δ x)⁻¹ ^ 2 ≤
        A * rationalVectorNorm F ((ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v) ∧
      rationalVectorNorm F ((ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v) ≤
        B * (iwasawaWeight hPK δ x)⁻¹ ^ 2 := by
  have : Nonempty n := by
    rcases isEmpty_or_nonempty n with h | h
    · exact (hv (Subsingleton.elim _ _)).elim
    · exact h
  obtain ⟨H, -, hH⟩ := exists_rationalHeight_le_on_compact ρ K hK
  obtain ⟨B, -, hB⟩ := exists_rationalVectorNorm_mulVec_inv_le F ρ v hK
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  let A := Real.exp H / ‖v‖
  have hApos : 0 < A := div_pos (Real.exp_pos _) hvpos
  refine ⟨A, max 1 B, hApos, zero_lt_one.trans_le (le_max_left _ _), fun x => ?_⟩
  let p := iwasawaFactor hPK x
  obtain ⟨k, hk, hx⟩ := exists_iwasawaFactor hPK x
  have hcinv := eq_inv_of_mul_eq_one_right (eigenvalue_mul_inv hv hev p.2)
  have hs : (iwasawaWeight hPK δ x) ^ 2 = ‖c p‖ := by
    change ((NNReal.sqrt (δ p : ℝ≥0) : ℝ≥0) : ℝ) ^ 2 = ‖c p‖
    rw [← NNReal.coe_pow, NNReal.sq_sqrt]
    exact hδ p
  have hvec : (ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v =
      (c p)⁻¹ • ((ρ.rationalMatrix k⁻¹ : Matrix n n F) *ᵥ v) := by
    rw [hx, _root_.mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      hev _ (P.inv_mem p.2), Matrix.mulVec_smul, hcinv]
  have hknorm : entryNorm (ρ.rationalMatrix k : Matrix n n F) ≤ Real.exp H := by
    have h := Real.exp_le_exp.mpr (hH ⟨k, hk⟩)
    change Real.exp (Real.log (rationalMatrixNorm F ρ k)) ≤ Real.exp H at h
    rw [Real.exp_log (rationalMatrixNorm_pos ρ k)] at h
    exact (le_max_left _ _).trans h
  have hVK := norm_mulVec_le (ρ.rationalMatrix k : Matrix n n F)
    ((ρ.rationalMatrix k⁻¹ : Matrix n n F) *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
    map_one, Units.val_one, Matrix.one_mulVec] at hVK
  let y := (ρ.rationalMatrix k⁻¹ : Matrix n n F) *ᵥ v
  have hy : 1 ≤ A * ‖y‖ := by
    dsimp only [A]
    rw [div_mul_eq_mul_div, le_div_iff₀ hvpos, one_mul]
    exact hVK.trans (mul_le_mul_of_nonneg_right hknorm (norm_nonneg _))
  change _ ≤ A * ‖(ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v‖ ∧
    ‖(ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v‖ ≤ _
  rw [hvec, norm_smul, norm_inv, ← hs, ← inv_pow]
  constructor
  · calc
      _ = (iwasawaWeight hPK δ x)⁻¹ ^ 2 * 1 := (mul_one _).symm
      _ ≤ (iwasawaWeight hPK δ x)⁻¹ ^ 2 * (A * ‖y‖) :=
        mul_le_mul_of_nonneg_left hy (sq_nonneg _)
      _ = _ := by
        change _ = A * ((iwasawaWeight hPK δ x)⁻¹ ^ 2 * ‖y‖)
        ring
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ((hB k hk).trans (le_max_right 1 B)) (sq_nonneg _)

/-- Power contraction of the inverse Iwasawa weight from an algebraic eigenline.
The contraction base is the square root of the normalized norm of the unit. -/
private theorem exists_inverse_iwasawaWeight_conj_pow_le
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hv : v ≠ 0) (hev : IsEigenvectorOn ρ v P c) (hχv : IsCocharacterEigenvector χ ρ v)
    (hδ : ∀ p : P, (((δ p : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      LocalField.residueNormalizedAbsoluteValue F (c p))
    (hK : IsCompact (K : Set (rationalPoints G)))
    (t : Fˣ) (ht : LocalField.residueNormalizedAbsoluteValue F (t : F) < 1) :
    let a : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (x : rationalPoints G),
      x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints →
      (iwasawaWeight hPK δ ((a ^ m)⁻¹ * x * a ^ m))⁻¹ ≤
        C * (1 + (Real.sqrt (LocalField.residueNormalizedAbsoluteValue F (t : F))) ^ m *
          (iwasawaWeight hPK δ x)⁻¹) := by
  let a : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom
  let w := iwasawaWeight hPK δ
  let q := LocalField.residueNormalizedAbsoluteValue F (t : F)
  have hq : 0 ≤ q := (LocalField.residueNormalizedAbsoluteValue F).nonneg _
  obtain ⟨A, B, hA, hB, hbounds⟩ := exists_inverse_iwasawaWeight_sq_bounds hPK ρ hv hev hδ hK
  obtain ⟨D, hD, hconj⟩ := exists_rationalVectorNorm_conj_pow_le F χ ρ hχv t ht
  let E := A * D * max (rationalVectorNorm F v) B
  have hE : 0 < E := mul_pos (mul_pos hA hD) (hB.trans_le (le_max_right _ _))
  refine ⟨Real.sqrt E, Real.sqrt_pos.2 hE, fun m x hx => ?_⟩
  let y := (a ^ m)⁻¹ * x * a ^ m
  let s := Real.sqrt q ^ m * (w x)⁻¹
  have hxpos : 0 ≤ (w x)⁻¹ := inv_nonneg.2 (iwasawaWeight_nonneg _)
  have hypos : 0 ≤ (w y)⁻¹ := inv_nonneg.2 (iwasawaWeight_nonneg _)
  have hs : 0 ≤ s := mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hxpos
  have hsq : s ^ 2 = q ^ m * (w x)⁻¹ ^ 2 := by
    dsimp only [s]
    rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt hq]
  have hyinv : y⁻¹ = (a ^ m)⁻¹ * x⁻¹ * a ^ m := by dsimp only [y]; group
  have h := hconj m x⁻¹ ((Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints.inv_mem hx)
  rw [← hyinv] at h
  change (w y)⁻¹ ≤ Real.sqrt E * (1 + s)
  apply (sq_le_sq₀ hypos (mul_nonneg (Real.sqrt_nonneg _) (by linarith))).mp
  rw [mul_pow, Real.sq_sqrt hE.le]
  calc
    _ ≤ A * rationalVectorNorm F ((ρ.rationalMatrix y⁻¹ : Matrix n n F) *ᵥ v) :=
      (hbounds y).1
    _ ≤ A * (D * max (rationalVectorNorm F v)
        (q ^ m * rationalVectorNorm F ((ρ.rationalMatrix x⁻¹ : Matrix n n F) *ᵥ v))) :=
      mul_le_mul_of_nonneg_left h hA.le
    _ ≤ E * (1 + s) ^ 2 := by
      dsimp only [E]
      rw [← mul_assoc, mul_assoc (A * D)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA.le hD.le)
      have hnonneg : 0 ≤ max (rationalVectorNorm F v) B := hB.le.trans (le_max_right _ _)
      have h1 : 1 ≤ (1 + s) ^ 2 := by nlinarith [sq_nonneg s]
      have h2 : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
      refine max_le ((le_max_left (rationalVectorNorm F v) B).trans ?_) ?_
      · exact (le_mul_of_one_le_right hnonneg h1)
      · calc
          _ ≤ q ^ m * (B * (w x)⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (hbounds x).2 (pow_nonneg hq _)
          _ = B * s ^ 2 := by rw [hsq]; ring
          _ ≤ _ := mul_le_mul (le_max_right _ _) h2 (sq_nonneg _) hnonneg

/-- Waldspurger II.4.1 (1) along powers of a cocharacter value with norm less than one.
The integrated subgroup and the minimal Iwasawa weight are the actual point groups. -/
theorem rationalOppositeWeightContraction : RationalOppositeWeightContractionStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν ζ K hPK hK t ht
  let χ := CommGroupScheme.groupHom ν ≫ i
  let ξ := CommGroupScheme.groupHom ζ ≫ i
  let iP := Dynamic.Affine.parabolicHom χ
  let iU := Dynamic.Affine.unipotentHom χ
  have hP : (Dynamic.parabolic χ).IsRepresentedBy iP :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hU : (Dynamic.unipotent χ).IsRepresentedBy iU :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  have : IsAffine (Dynamic.Affine.parabolicScheme χ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom
  have hUc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have : IsAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom := hUc.isAffineHom
  have : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme χ).X.hom := hUc.locallyOfFiniteType
  have : Mono iU.hom.hom := hU.1
  let cG := Lie.finiteCoordinates G
  let cU := Lie.finiteCoordinates (Dynamic.Affine.unipotentScheme χ)
  let v := Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ F)
  let c := Dynamic.adjointDeterminantPointValue iP (Dynamic.adjointDeterminantCharacter hP hU cU)
  have hv : v ≠ 0 := Dynamic.adjointExteriorCoordinates_ne_zero cG cU (CommAlgCat.of _ F)
    (Field.toIsField F)
  have hev := Dynamic.isEigenvectorOn_adjointExteriorCoordinates hP hU cG cU
  have hPeq : standardParabolicPoints i ν ∅ = (Dynamic.parabolic χ).rationalPoints := by
    change (standardParabolic i ν ∅).carrier _ = (Dynamic.parabolic χ).carrier _
    rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
  have hevP : IsEigenvectorOn (Dynamic.adjointExteriorRepresentation cG) v
      (standardParabolicPoints i ν ∅) c := fun g hg => hev g (hPeq.le hg)
  have hevξ : IsCocharacterEigenvector ξ (Dynamic.adjointExteriorRepresentation cG) v := by
    intro u
    let g := gmRationalPoint u ≫ ξ.hom.hom
    have hg : g ∈ (SubgroupFunctor.range ξ).rationalPoints := ⟨gmRationalPoint u, rfl⟩
    have hZ := Dynamic.range_comp_le_centralizer_comp i (CommGroupScheme.groupHom ζ)
      (CommGroupScheme.groupHom ν) _ hg
    exact ⟨c g, hev g (Dynamic.centralizer_le_parabolic χ _ hZ)⟩
  obtain ⟨C, hC, h⟩ :=
    exists_inverse_iwasawaWeight_conj_pow_le hPK _ ξ hv hevP hevξ
      (rationalMinimalModulus_eq_abs_adjointDeterminant hG hi hν hP hU cU) hK t ht
  exact ⟨C, hC, fun m x => h m x x.2⟩

end Langlands.HarishChandraSchwartz
