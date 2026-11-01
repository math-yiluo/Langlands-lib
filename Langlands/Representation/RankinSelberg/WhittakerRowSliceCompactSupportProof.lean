import Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement
import Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof
import Langlands.Representation.RankinSelberg.IntegralDeterminant
import Langlands.Analysis.Local.QuotientTopology
import Langlands.Group.GL.UpperBruhatCells
import Langlands.Group.GL.NormalizedCharacter
import Langlands.HarmonicAnalysis.PadicLatticeTopology
import Langlands.LocalField.Uniformizer

/-!
# Proof of compact support of Whittaker row data on a determinant slice

JPSS (1983), Section 4.6, printed page 412: on each fixed determinant slice the
norm of `W(g) Φ(η g)` has compact support on `N_(n+1) \ GL_(n+1)`. At a point of
the support, the Iwasawa decomposition `g = u · diag(a) · κ`, the published uniform
simple-root bound and the row Schwartz–Bruhat bound bound every `|a_i|` above, and
the fixed determinant bounds every `|a_i|` below. The support therefore lies in the
image of a compact set of diagonal annuli times the integral subgroup, which is
compact in the Hausdorff quotient.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Iwasawa diagonal bounds at a nonvanishing point. If the adjacent diagonal ratios
are bounded by `R` wherever `W` is nonzero, and the last row of `g` lies in the box
`|x_j| ≤ C`, then `g = u · diag(a) · κ` with `u` upper unipotent, `κ` integral and
`|a_i| ≤ R^(n-i) C` for every diagonal entry. -/
theorem exists_iwasawa_diagonal_le_of_simpleRoot (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (W : WhittakerFunctions ψ n) {R C : ℝ},
      0 < R → 0 ≤ C →
      (∀ (a : Fin (n + 1) → F.Carrierˣ) (κ : Langlands.GeneralLinear (n + 1) F.Carrier),
        κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
        W.val (Iwasawa.diagonalUnits a * κ) ≠ 0 →
        ∀ i : Fin n,
          T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) ≤ R) →
      ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier, W.val g ≠ 0 →
        (∀ j, T.normalizedAbs (lastRow g j) ≤ C) →
        ∃ u ∈ upperUnipotent (n + 1) F.Carrier, ∃ a : Fin (n + 1) → F.Carrierˣ,
          ∃ κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n,
            g = u * (Iwasawa.diagonalUnits a * κ) ∧
            ∀ i : Fin (n + 1),
              T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) ≤ R ^ (n - i.val) * C := by
  let := T.topology
  let := T.valuativeRel
  intro ψ W R C hR hC hroot g hW hrow
  obtain ⟨b, hb, k, hk, rfl⟩ :=
    Iwasawa.exists_upperTriangular_mul (ValuativeRel.valuation F.Carrier) g
  have hd : ∀ i, b i i ≠ 0 := by
    intro i h0
    apply Matrix.GeneralLinearGroup.det_ne_zero b
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  set a : Fin (n + 1) → F.Carrierˣ := fun i => Units.mk0 (b i i) (hd i) with ha
  set D := Iwasawa.diagonalUnits a with hD
  set u := b * D⁻¹ with hu
  have hval : u.val = b.val * Matrix.diagonal fun i => (b i i)⁻¹ := by
    rw [hu, Units.val_mul, hD, ← map_inv, Iwasawa.diagonalUnits_val]
    congr 1
  have humem : u ∈ upperUnipotent (n + 1) F.Carrier := by
    refine ⟨?_, fun i => ?_⟩
    · rw [hval]
      exact hb.mul (Matrix.blockTriangular_diagonal _)
    · change u.val i i = 1
      rw [hval, Matrix.mul_diagonal, mul_inv_cancel₀ (hd i)]
  have hg : b * k = u * (D * k) := by
    rw [hu, mul_assoc, inv_mul_cancel_left]
  refine ⟨u, humem, a, k, hk, hg, ?_⟩
  rw [hg] at hW hrow
  -- Simple-root bounds at the point `D k`.
  have hWD : W.val (D * k) ≠ 0 := by
    intro h
    apply hW
    have h1 : W.val (u * (D * k)) = _ := W.property ⟨u, humem⟩ (D * k)
    rw [h1, h, mul_zero]
  have hratio := hroot a k hk hWD
  -- The last diagonal entry is bounded through the last row.
  have hrow' : ∀ j, T.normalizedAbs (lastRow (D * k) j) ≤ C := by
    have h1 : lastRow (u * (D * k)) = lastRow (D * k) :=
      lastRow_unipotent_mul ⟨u, humem⟩ (D * k)
    rw [← h1]
    exact hrow
  have hkmem := (Conductor.mem_integralSubgroup _ n k).1 hk
  have hlast : ((a (Fin.last n) : F.Carrierˣ) : F.Carrier) =
      ∑ j, lastRow (D * k) j * (k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) j
        (Fin.last n) := by
    have h : (D * k).val * (k⁻¹).val = D.val := by
      rw [← Units.val_mul, mul_inv_cancel_right]
    have h2 := congrFun (congrFun h (Fin.last n)) (Fin.last n)
    rw [Matrix.mul_apply, hD, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq] at h2
    exact h2.symm
  have hlastle : T.normalizedAbs ((a (Fin.last n) : F.Carrierˣ) : F.Carrier) ≤ C := by
    rw [hlast]
    refine normalizedAbs_finsetSum_le T _ _ hC fun j _ => ?_
    rw [T.normalizedAbs_mul]
    have hk1 : T.normalizedAbs
        ((k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) j (Fin.last n)) ≤ 1 :=
      (T.normalizedAbs_le_one_iff_mem_integers _).2 (hkmem.2 j (Fin.last n))
    calc T.normalizedAbs (lastRow (D * k) j) *
          T.normalizedAbs ((k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) j (Fin.last n))
        ≤ C * 1 := mul_le_mul (hrow' j) hk1 (T.normalizedAbs_nonneg _) hC
      _ = C := mul_one C
  -- Reverse induction along the diagonal.
  intro i
  induction i using Fin.reverseInduction with
  | last => simpa using hlastle
  | cast i ih =>
    have hsplit : ((a i.castSucc : F.Carrierˣ) : F.Carrier) =
        ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) *
          ((a i.succ : F.Carrierˣ) : F.Carrier) := by
      rw [← Units.val_mul, div_mul_cancel]
    have hexp : n - i.castSucc.val = (n - i.succ.val) + 1 := by
      rw [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hsplit, T.normalizedAbs_mul, hexp, pow_succ', mul_assoc]
    exact mul_le_mul (hratio i) ih (T.normalizedAbs_nonneg _) hR.le

/-- The units in a closed normalized-absolute-value annulus `c ≤ |a| ≤ M`, with
`0 < c`, form a compact set in the topology of units. -/
theorem isCompact_normalizedAbs_annulus_units {c M : ℝ} (hc : 0 < c) :
    letI := T.topology
    IsCompact {a : F.Carrierˣ |
      c ≤ T.normalizedAbs (a : F.Carrier) ∧ T.normalizedAbs (a : F.Carrier) ≤ M} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt M hq
  let S : Set F.Carrier := {x | c ≤ T.normalizedAbs x ∧ T.normalizedAbs x ≤ M}
  have hne : ∀ x ∈ S, x ≠ 0 := by
    rintro x hx rfl
    have h := hx.1
    rw [T.normalizedAbs_zero] at h
    linarith
  have hScl : IsClosed S :=
    (isClosed_le continuous_const T.continuous_normalizedAbs).inter
      (isClosed_le T.continuous_normalizedAbs continuous_const)
  have hsub : S ⊆ (T.additiveLattice (N : ℤ) : Set F.Carrier) := by
    intro x hx
    let y : F.Carrierˣ := LocalFactor.PadicAbelian.uniformizerUnit T ^ (-(N : ℤ))
    have hy : T.normalizedAbs (y : F.Carrier) = (T.residueCardinality : ℝ) ^ (N : ℤ) := by
      rw [LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs, neg_neg]
    have hle : T.normalizedAbs x ≤ T.normalizedAbs (y : F.Carrier) := by
      rw [hy, zpow_natCast]
      exact hx.2.trans hN.le
    have hv := (T.normalizedAbs_le_iff_of_ne_zero (hne x hx) y.ne_zero).1 hle
    rw [LocalFactor.PadicAbelian.uniformizerUnit_zpow_value, neg_neg] at hv
    exact (T.mem_additiveLattice _ x).2 hv
  have hS : IsCompact S :=
    (T.isCompact_additiveLattice (N : ℤ)).of_isClosed_subset hScl hsub
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS fun x hx => ?_
  exact ⟨Units.mk0 x (hne x hx), rfl⟩

/-- JPSS (1983), Section 4.6, printed page 412: on each fixed determinant slice the
norm of `W(g) Φ(η g)` has compact support on the actual quotient
`N_(n+1) \ GL_(n+1)`, for every actual coefficient of every smooth representation. -/
theorem whittakerRowSliceCompactSupport {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    WhittakerRowSliceCompactSupportStatement.{uF,uV} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  have : T2Space F.Carrier := inferInstance
  have : T2Space (LeftUnipotentQuotient n F.Carrier) :=
    leftQuotient_t2Space _ (GeneralLinear.UpperUnipotent.isClosed (R := F.Carrier))
  intro ψ V _ _ π hπ ℓ W Φ k
  obtain ⟨R, hR, hroot⟩ := Whittaker.smoothSimpleRootSupport.{uF, uV} F T n ψ V π hπ ℓ W
  obtain ⟨C, hC, hΦ⟩ := exists_schwartzBruhat_row_bound T n Φ
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  -- A uniform upper bound `M` and the lower bound `c = q^(-k) / M^n`.
  set M : ℝ := max R 1 ^ n * max C 1 with hM
  have hM1 : 1 ≤ M :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_right _ _)) (le_max_right _ _)
  set c : ℝ := (T.residueCardinality : ℝ) ^ (-k) / M ^ n with hc
  have hc0 : 0 < c :=
    div_pos (zpow_pos (zero_lt_one.trans hq) _) (pow_pos (zero_lt_one.trans_le hM1) _)
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let A : Set (Fin (n + 1) → F.Carrierˣ) := Set.univ.pi fun _ =>
    {a : F.Carrierˣ | c ≤ T.normalizedAbs (a : F.Carrier) ∧ T.normalizedAbs (a : F.Carrier) ≤ M}
  have hA : IsCompact A :=
    isCompact_univ_pi fun _ => isCompact_normalizedAbs_annulus_units T hc0
  have hK : IsCompact (K : Set G) := by
    change IsCompact (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set G)
    rw [← Conductor.levelSubgroup_zero]
    exact Conductor.isCompact_levelOpenSubgroup F.Carrier n 0
  let Ψ : (Fin (n + 1) → F.Carrierˣ) × G → LeftUnipotentQuotient n F.Carrier := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.diagonalUnits x.1 * x.2)
  have hΨ : Continuous Ψ :=
    (leftQuotient_isOpenQuotientMap _).continuous.comp
      (((GeneralLinear.continuous_diagonalUnits (n + 1)).comp continuous_fst).mul
        continuous_snd)
  refine HasCompactSupport.intro ((hA.prod hK).image hΨ) ?_
  intro q hq0
  induction q using Quotient.inductionOn with
  | h g =>
    by_contra hne
    apply hq0
    rw [← ne_eq, Set.indicator_apply_ne_zero] at hne
    obtain ⟨hslice, hsupp⟩ := hne
    rw [mk_mem_determinantSlice_iff_normalizedAbs] at hslice
    rw [Function.mem_support, whittakerNorm_mk, quotientLastRow_mk] at hsupp
    have hW : W.val.val g ≠ 0 := fun h => hsupp (by rw [h, norm_zero, zero_mul])
    have hP : Φ (lastRow g) ≠ 0 := fun h => hsupp (by rw [h, norm_zero, mul_zero])
    obtain ⟨u, hu, a, κ, hκ, rfl, hbound⟩ :=
      exists_iwasawa_diagonal_le_of_simpleRoot T n ψ W.val hR hC hroot g hW (hΦ _ hP)
    -- Upper bounds.
    have hupper : ∀ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) ≤ M := by
      intro i
      calc T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) ≤ R ^ (n - i.val) * C :=
            hbound i
        _ ≤ max R 1 ^ (n - i.val) * max C 1 :=
            mul_le_mul (pow_le_pow_left₀ hR.le (le_max_left _ _) _) (le_max_left _ _) hC
              (pow_nonneg (hR.le.trans (le_max_left _ _)) _)
        _ ≤ M :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_right _ _) (Nat.sub_le _ _))
              (zero_le_one.trans (le_max_right _ _))
    -- The fixed determinant.
    have hdet : (GeneralLinear.determinant (u * (Iwasawa.diagonalUnits a * κ)) : F.Carrier) =
        (∏ i, ((a i : F.Carrierˣ) : F.Carrier)) * Matrix.det κ.val := by
      have h1 : GeneralLinear.determinant (u * (Iwasawa.diagonalUnits a * κ)) =
          GeneralLinear.determinant (Iwasawa.diagonalUnits a * κ) :=
        determinant_unipotent_mul ⟨u, hu⟩ (Iwasawa.diagonalUnits a * κ)
      rw [h1]
      change Matrix.det ((Iwasawa.diagonalUnits a).val * κ.val) = _
      rw [Matrix.det_mul, Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
    have hprod : T.normalizedAbs (∏ i, ((a i : F.Carrierˣ) : F.Carrier)) =
        ∏ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) := by
      rw [← normalizedAbsoluteValue_apply, map_prod]
      rfl
    have hall : ∏ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) =
        (T.residueCardinality : ℝ) ^ (-k) := by
      rw [← hslice, hdet, T.normalizedAbs_mul, hprod,
        normalizedAbs_det_of_mem_integralSubgroup T hκ, mul_one]
    -- Lower bounds.
    have hlower : ∀ i, c ≤ T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) := by
      intro i
      have herase : ∏ j ∈ Finset.univ.erase i, T.normalizedAbs ((a j : F.Carrierˣ) : F.Carrier)
          ≤ M ^ n := by
        calc ∏ j ∈ Finset.univ.erase i, T.normalizedAbs ((a j : F.Carrierˣ) : F.Carrier)
            ≤ ∏ _j ∈ Finset.univ.erase i, M :=
              Finset.prod_le_prod₀ (fun j _ => T.normalizedAbs_nonneg _)
                fun j _ => hupper j
          _ = M ^ n := by
              rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
                Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
      rw [hc, div_le_iff₀ (pow_pos (zero_lt_one.trans_le hM1) _), ← hall,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      exact mul_le_mul_of_nonneg_left herase (T.normalizedAbs_nonneg _)
    refine ⟨(a, κ), ⟨fun i _ => ⟨hlower i, hupper i⟩, hκ⟩, ?_⟩
    apply Quotient.sound
    change QuotientGroup.rightRel _ (Iwasawa.diagonalUnits a * κ)
      (u * (Iwasawa.diagonalUnits a * κ))
    rw [QuotientGroup.rightRel_apply, mul_inv_cancel_right]
    exact hu

end Langlands.RankinSelberg
