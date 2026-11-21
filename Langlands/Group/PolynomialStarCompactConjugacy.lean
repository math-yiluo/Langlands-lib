import Langlands.Group.InternalPolarFactors
import Mathlib.Analysis.Matrix.Order

/-! # Compact conjugacy in a self-adjoint algebraic matrix group -/

noncomputable section

universe u

namespace Langlands.Group.PolynomialStarCompactConjugacy

open Matrix Set
open scoped ComplexOrder
open Langlands.Group.AlgebraicMatrixPowers Langlands.Group.AlgebraicPolar

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

private def realTrace (A : Matrix n n 𝕜) : ℝ := RCLike.re A.trace

omit [DecidableEq n] in
private theorem continuous_realTrace : Continuous (realTrace (n := n) (𝕜 := 𝕜)) := by
  unfold realTrace Matrix.trace Matrix.diag
  fun_prop

omit [DecidableEq n] in
private theorem realTrace_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    0 ≤ realTrace A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

omit [DecidableEq n] in
private theorem realTrace_pos {A : Matrix n n 𝕜} (hA : A.PosSemidef) (hne : A ≠ 0) :
    0 < realTrace A := by
  apply lt_of_le_of_ne (realTrace_nonneg hA)
  intro heq
  apply hne (hA.trace_eq_zero_iff.mp ?_)
  apply RCLike.ext
  · simpa only [map_zero] using (show RCLike.re A.trace = 0 from heq.symm)
  · simpa only [map_zero] using (RCLike.nonneg_iff.mp hA.trace_nonneg).2

private theorem posDef_unit_iff_posSemidef (A : GL n 𝕜) :
    A.val.PosDef ↔ A.val.PosSemidef := by
  refine ⟨PosDef.posSemidef, fun hA => ?_⟩
  apply hA.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  refine lt_of_le_of_ne (hA.eigenvalues_nonneg i) ?_
  intro heq
  have hz := hA.isHermitian.mulVec_eigenvectorBasis i
  rw [← heq, zero_smul] at hz
  have hz' := (Matrix.mulVec_injective_of_isUnit A.isUnit)
    (hz.trans (Matrix.mulVec_zero A.val).symm)
  exact hA.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
    ((WithLp.ofLp_eq_zero 2).mp hz')

private theorem isCompact_traceSlice (R : ℝ) :
    IsCompact {A : Matrix n n 𝕜 | A.PosSemidef ∧ realTrace A ≤ R} := by
  let f (x : Matrix.unitaryGroup n 𝕜 × (n → ℝ)) : Matrix n n 𝕜 :=
    (x.1 : Matrix n n 𝕜) * diagonal (fun i => RCLike.ofReal (x.2 i)) *
      star (x.1 : Matrix n n 𝕜)
  have hf : Continuous f := by
    unfold f
    fun_prop
  have hU : IsCompact (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
    apply (isCompact_closedBall (0 : 𝕜) 1).matrix.of_isClosed_subset isClosed_unitary
    intro U hU i j
    exact mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hU i j)
  let := isCompact_iff_compactSpace.mp hU
  let C : Set (Matrix.unitaryGroup n 𝕜 × (n → ℝ)) :=
    univ ×ˢ (univ.pi fun _ : n => Icc 0 R)
  have hC : IsCompact C :=
    isCompact_univ.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  apply (hC.image hf).of_isClosed_subset
    (posSemidef_is_closed.inter (isClosed_le continuous_realTrace continuous_const))
  intro A hA
  refine ⟨(hA.1.isHermitian.eigenvectorUnitary, hA.1.isHermitian.eigenvalues),
    ⟨mem_univ _, ?_⟩, ?_⟩
  · intro i _
    refine ⟨hA.1.eigenvalues_nonneg i, ?_⟩
    have hsum : realTrace A = ∑ j, hA.1.isHermitian.eigenvalues j := by
      simp only [realTrace, hA.1.isHermitian.trace_eq_sum_eigenvalues, map_sum,
        RCLike.ofReal_re]
    exact (Finset.single_le_sum (fun j _ => hA.1.eigenvalues_nonneg j)
      (Finset.mem_univ i)).trans (hsum ▸ hA.2)
  · simpa only [f, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hA.1.isHermitian.spectral_theorem.symm

private def traceEnergy (A : GL n 𝕜) : ℝ :=
  realTrace A.val + realTrace A⁻¹.val

private theorem continuous_traceEnergy : Continuous (traceEnergy (n := n) (𝕜 := 𝕜)) :=
  (continuous_realTrace.comp Units.continuous_val).add
    (continuous_realTrace.comp (Units.continuous_val.comp continuous_inv))

private theorem posDef_val_inv {A : GL n 𝕜} (hA : A.val.PosDef) : A⁻¹.val.PosDef := by
  simpa only [Matrix.coe_units_inv] using hA.inv

private theorem isCompact_traceEnergySublevel (R : ℝ) :
    IsCompact {A : GL n 𝕜 | A.val.PosDef ∧ traceEnergy A ≤ R} := by
  let C := {A : Matrix n n 𝕜 | A.PosSemidef ∧ realTrace A ≤ R}
  have hC : IsCompact C := isCompact_traceSlice R
  have hprod : IsCompact (C ×ˢ (MulOpposite.unop ⁻¹' C)) :=
    hC.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hC)
  refine (Units.isClosedEmbedding_embedProduct.isCompact_preimage hprod).of_isClosed_subset ?_ ?_
  · simp only [posDef_unit_iff_posSemidef]
    exact (posSemidef_is_closed.preimage Units.continuous_val).inter
      (isClosed_le continuous_traceEnergy continuous_const)
  · intro A hA
    have hInv := posDef_val_inv hA.1
    have hbound : realTrace A.val + realTrace A⁻¹.val ≤ R := hA.2
    change A.val ∈ C ∧ A⁻¹.val ∈ C
    exact ⟨⟨hA.1.posSemidef, by linarith [realTrace_nonneg hInv.posSemidef]⟩,
      ⟨hInv.posSemidef, by linarith [realTrace_nonneg hA.1.posSemidef]⟩⟩

private theorem realTrace_midpoint_lt (g b : GL n 𝕜)
    (hb : star b = b) (hne : b ≠ 1) :
    2 * realTrace (g * b * star g).val <
      realTrace (g * star g).val + realTrace (g * b * b * star g).val := by
  let S := g.val * (b.val - 1)
  have heq : (g * star g).val + (g * b * b * star g).val -
      (g * b * star g).val - (g * b * star g).val = S * Sᴴ := by
    have hb' : b.valᴴ = b.val := congrArg Units.val hb
    simp only [S, Units.val_mul, Units.coe_star, Matrix.star_eq_conjTranspose,
      conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hb']
    noncomm_ring
  have hS : S ≠ 0 := by
    intro hS
    apply hne
    apply Units.ext
    apply sub_eq_zero.mp
    have h := congrArg (fun M : Matrix n n 𝕜 => g⁻¹.val * M) hS
    simpa only [S, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
      mul_zero] using h
  have hpos : 0 < realTrace (S * Sᴴ) :=
    realTrace_pos (posSemidef_self_mul_conjTranspose S)
      (fun h => hS (trace_mul_conjTranspose_self_eq_zero_iff.mp (by simp only [h, trace_zero])))
  rw [← heq] at hpos
  simp only [realTrace, trace_sub, trace_add, map_sub, map_add] at hpos ⊢
  linarith

private theorem traceEnergy_midpoint_lt (g b : GL n 𝕜)
    (hb : star b = b) (hne : b ≠ 1) :
    2 * traceEnergy (g * b * star g) <
      traceEnergy (g * star g) + traceEnergy (g * b * b * star g) := by
  have h := realTrace_midpoint_lt g b hb hne
  have hInv := realTrace_midpoint_lt (star g)⁻¹ b⁻¹
    (by rw [star_inv, hb]) (by simpa using hne)
  have hInv' :
      2 * realTrace (g * b * star g)⁻¹.val <
        realTrace (g * star g)⁻¹.val + realTrace (g * b * b * star g)⁻¹.val := by
    simpa only [star_inv, star_star, _root_.mul_inv_rev, mul_assoc] using hInv
  unfold traceEnergy
  linarith

private theorem posDef_congr {A : GL n 𝕜} (g : GL n 𝕜) (hA : A.val.PosDef) :
    (g * A * star g).val.PosDef :=
  g.isUnit.posDef_star_right_conjugate_iff.mpr hA

private def compactEnergy (L : Subgroup (GL n 𝕜)) (A : GL n 𝕜) : ℝ :=
  sSup ((fun h => traceEnergy (h * A * star h)) '' (L : Set (GL n 𝕜)))

private theorem continuous_compactEnergy {L : Subgroup (GL n 𝕜)}
    (hL : IsCompact (L : Set (GL n 𝕜))) : Continuous (compactEnergy L) :=
  hL.continuous_sSup (by
    change Continuous fun x : GL n 𝕜 × GL n 𝕜 => traceEnergy (x.2 * x.1 * star x.2)
    exact continuous_traceEnergy.comp
      ((continuous_snd.mul continuous_fst).mul (continuous_star.comp continuous_snd)))

private theorem continuousOn_orbitEnergy (A : GL n 𝕜) (L : Subgroup (GL n 𝕜)) :
    ContinuousOn (fun h => traceEnergy (h * A * star h)) (L : Set (GL n 𝕜)) :=
  (continuous_traceEnergy.comp ((continuous_id.mul continuous_const).mul continuous_star)).continuousOn

private theorem le_compactEnergy {L : Subgroup (GL n 𝕜)} (hL : IsCompact (L : Set (GL n 𝕜)))
    (A h : GL n 𝕜) (hh : h ∈ L) :
    traceEnergy (h * A * star h) ≤ compactEnergy L A :=
  le_csSup (hL.bddAbove_image (continuousOn_orbitEnergy A L)) (mem_image_of_mem _ hh)

private theorem compactEnergy_congr (L : Subgroup (GL n 𝕜)) (A h : GL n 𝕜) (hh : h ∈ L) :
    compactEnergy L (h * A * star h) = compactEnergy L A := by
  unfold compactEnergy
  congr 1
  ext r
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * h, L.mul_mem hg hh, by simp only [star_mul, mul_assoc]⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * h⁻¹, L.mul_mem hg (L.inv_mem hh), ?_⟩
    simp only [star_mul, star_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]

private theorem exists_isMinOn_compactEnergy (H L : Subgroup (GL n 𝕜))
    (hH : IsClosed (H : Set (GL n 𝕜))) (hL : IsCompact (L : Set (GL n 𝕜))) :
    ∃ A ∈ {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef},
      IsMinOn (compactEnergy L) {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef} A := by
  let r := compactEnergy L 1
  let C := {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef ∧ compactEnergy L g ≤ r}
  have hC : IsCompact C := by
    apply (isCompact_traceEnergySublevel (n := n) (𝕜 := 𝕜) r).of_isClosed_subset
    · simp only [C, posDef_unit_iff_posSemidef]
      exact hH.inter ((posSemidef_is_closed.preimage Units.continuous_val).inter
        (isClosed_le (continuous_compactEnergy hL) continuous_const))
    · intro A hA
      have hE : traceEnergy A ≤ compactEnergy L A := by
        simpa only [one_mul, star_one, mul_one] using le_compactEnergy hL A 1 L.one_mem
      exact ⟨hA.2.1, hE.trans hA.2.2⟩
  have hOne : (1 : GL n 𝕜) ∈ C := ⟨H.one_mem, by simpa only [Units.val_one] using
    (PosDef.one : (1 : Matrix n n 𝕜).PosDef), le_rfl⟩
  obtain ⟨A, hA, hmin⟩ :=
    hC.exists_isMinOn ⟨1, hOne⟩ (continuous_compactEnergy hL).continuousOn
  refine ⟨A, ⟨hA.1, hA.2.1⟩, fun g hg => ?_⟩
  by_cases h : compactEnergy L g ≤ r
  · exact hmin (show g ∈ C from ⟨hg.1, hg.2, h⟩)
  · exact hA.2.2.trans (le_of_lt (lt_of_not_ge h))

set_option maxHeartbeats 600000 in
private theorem unique_isMinOn_compactEnergy (H L : Subgroup (GL n 𝕜))
    (hpoly : IsPolynomiallyDefined H) (hL : IsCompact (L : Set (GL n 𝕜)))
    {A B : GL n 𝕜} (hAH : A ∈ H) (hBH : B ∈ H) (hA : A.val.PosDef) (hB : B.val.PosDef)
    (hminA : IsMinOn (compactEnergy L) {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef} A)
    (hminB : IsMinOn (compactEnergy L) {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef} B) :
    A = B := by
  by_contra hne
  obtain ⟨a, haH, ha, haa⟩ := exists_positive_sqrt H hpoly A hA hAH
  have hsa : star a = a := Units.ext ha.isHermitian.star_eq
  have hsaInv : star a⁻¹ = a⁻¹ := by rw [star_inv, hsa]
  have hC : (a⁻¹ * B * a⁻¹).val.PosDef := by
    simpa only [hsaInv] using posDef_congr a⁻¹ hB
  have hCH : a⁻¹ * B * a⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem haH) hBH) (H.inv_mem haH)
  obtain ⟨b, hbH, hb, hbb⟩ := exists_positive_sqrt H hpoly _ hC hCH
  have hsb : star b = b := Units.ext hb.isHermitian.star_eq
  have hB' : a * b * b * a = B := by
    rw [mul_assoc a b b, hbb]
    group
  have hbne : b ≠ 1 := by
    intro h
    rw [h, mul_one, mul_one, haa] at hB'
    exact hne hB'
  let M := a * b * a
  have hM : M ∈ {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef} :=
    ⟨H.mul_mem (H.mul_mem haH hbH) haH, by
      simpa only [M, hsa] using posDef_congr a hb⟩
  obtain ⟨h, hh, hmax, -⟩ := hL.exists_sSup_image_eq_and_ge ⟨1, L.one_mem⟩
    (continuousOn_orbitEnergy M L)
  have hmid := traceEnergy_midpoint_lt (h * a) b hsb hbne
  have hmid' : 2 * traceEnergy (h * M * star h) <
      traceEnergy (h * A * star h) + traceEnergy (h * B * star h) := by
    rw [← haa, ← hB']
    simpa only [M, star_mul, hsa, mul_assoc] using hmid
  have hAm : compactEnergy L A ≤ compactEnergy L M := hminA hM
  have hBm : compactEnergy L B ≤ compactEnergy L M := hminB hM
  have hFA := le_compactEnergy hL A h hh
  have hFB := le_compactEnergy hL B h hh
  have hFM : compactEnergy L M = traceEnergy (h * M * star h) := hmax
  linarith

/-- A compact subgroup of a closed, self-adjoint polynomial matrix group is
conjugate by an element of the group into its unitary subgroup. -/
theorem exists_conj_unitary
    (H L : Subgroup (GL n 𝕜)) (hH : IsClosed (H : Set (GL n 𝕜)))
    (hpoly : IsPolynomiallyDefined H) (hstar : ∀ g ∈ H, star g ∈ H)
    (hL : IsCompact (L : Set (GL n 𝕜))) (hle : L ≤ H) :
    ∃ a ∈ H, ∀ h ∈ L, (a⁻¹ * h * a).val ∈ Matrix.unitaryGroup n 𝕜 := by
  obtain ⟨A, hA, hminA⟩ := exists_isMinOn_compactEnergy H L hH hL
  obtain ⟨a, haH, ha, haa⟩ := exists_positive_sqrt H hpoly A hA.2 hA.1
  have hsa : star a = a := Units.ext ha.isHermitian.star_eq
  refine ⟨a, haH, fun h hh => ?_⟩
  have hB : h * A * star h ∈ {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef} :=
    ⟨H.mul_mem (H.mul_mem (hle hh) hA.1) (hstar h (hle hh)), posDef_congr h hA.2⟩
  have hminB : IsMinOn (compactEnergy L) {g : GL n 𝕜 | g ∈ H ∧ g.val.PosDef}
      (h * A * star h) := by
    intro g hg
    change compactEnergy L (h * A * star h) ≤ compactEnergy L g
    rw [compactEnergy_congr L A h hh]
    exact hminA hg
  have hfix := unique_isMinOn_compactEnergy H L hpoly hL hB.1 hA.1 hB.2 hA.2 hminB hminA
  have hu : (a⁻¹ * h * a) * star (a⁻¹ * h * a) = 1 := by
    simp only [star_mul, star_inv, hsa]
    calc
      _ = a⁻¹ * (h * (a * a) * star h) * a⁻¹ := by group
      _ = 1 := by rw [haa, hfix, ← haa]; group
  exact Matrix.mem_unitaryGroup_iff.mpr (congrArg Units.val hu)

end Langlands.Group.PolynomialStarCompactConjugacy
