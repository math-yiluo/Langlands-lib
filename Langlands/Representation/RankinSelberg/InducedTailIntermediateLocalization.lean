import Langlands.Group.GL.LowerBlockLocalizationCoordinates
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.RankinSelberg.RankOneExtensionSpanTransfer
import Langlands.Representation.Whittaker.CoefficientRightStabilizer

/-! # Smooth test invariance for the intermediate lower-block comparison -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear Whittaker HarmonicAnalysis Topology

universe uF uV

section Matrices

variable {F : Type uF} [Field F] {a d : ℕ}

/-- With vanishing off-diagonal coordinate and identity final block, the
lower chart is the published standard rank inclusion. -/
theorem lowerBlockPair_zero_one (g : Langlands.GeneralLinear a F) :
    lowerBlockPair g (0 : Matrix (Fin d) (Fin a) F) 1 = rankInclusion d g := by
  apply Units.ext
  rfl

/-- The iterated JPSS identity extension agrees with the actual standard rank
inclusion after the specified rank reindexing. -/
theorem rankInclusion_eq_appendIdentity (n d : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
        (rankInclusion d g) = appendIdentity n d g := by
  apply Units.ext
  ext i j
  change rankInclusion d g (Fin.cast (by omega) i) (Fin.cast (by omega) j) = _
  rw [rankInclusion_entry, appendIdentity_entry]
  simp

/-- The diagonal restriction of the lower chart is the literal JPSS
identity extension with no coordinate permutation. -/
theorem lowerBlockPair_eq_appendIdentity (n d : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
      (lowerBlockPair g (0 : Matrix (Fin d) (Fin (n + 1)) F) 1) =
        appendIdentity n d g := by
  rw [lowerBlockPair_zero_one, rankInclusion_eq_appendIdentity]

/-- The rank-inclusion identity also keeps an independently specified source
rank and transports its input by the stated equality. -/
theorem rankInclusion_eq_appendIdentity_of_rank_eq (n d : ℕ) {a : ℕ}
    (ha : a = n + 1) (g : Langlands.GeneralLinear a F) :
    reindex (finCongr (by omega : a + d = n + d + 1)) (rankInclusion d g) =
      appendIdentity n d (reindex (finCongr ha) g) := by
  subst a
  have hself : reindex (finCongr (rfl : n + 1 = n + 1)) g = g := by
    apply Units.ext
    rfl
  rw [hself]
  exact rankInclusion_eq_appendIdentity n d g

/-- The full lower-block localization chart is precisely the identity extension
of its test-rank lower-block matrix, with both rank transports displayed. -/
theorem lowerBlockLocalization_eq_outer_appendIdentity (n c : ℕ)
    (hn : a + d = n + 1) (g : Langlands.GeneralLinear a F)
    (x : Matrix (Fin d) (Fin a) F) (h : lowerTriangularSubgroup d F) :
    reindex (finCongr (by omega : a + d + c = n + c + 1))
      (lowerBlockLocalization c g x h) =
        appendIdentity n c (reindex (finCongr hn) (lowerBlockPair g x h)) :=
  rankInclusion_eq_appendIdentity_of_rank_eq n c hn (lowerBlockPair g x h)

/-- On the diagonal restriction, all the middle and final identity coordinates
coalesce into the single identity extension used in the extension theorem. -/
theorem lowerBlockLocalization_eq_appendIdentity (n d c : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    reindex (finCongr (by omega : (n + 1) + d + c = n + (d + c) + 1))
      (lowerBlockLocalization c g (0 : Matrix (Fin d) (Fin (n + 1)) F) 1) =
        appendIdentity n (d + c) g := by
  apply Units.ext
  ext i j
  change rankInclusion c (lowerBlockPair g 0 1)
    (Fin.cast (by omega) i) (Fin.cast (by omega) j) = _
  rw [lowerBlockPair_zero_one]
  simp only [rankInclusion_entry, appendIdentity_entry, Fin.val_cast, Fin.cast_inj]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- The diagonal chart agrees with the extension theorem's actual full-rank
matrix after the two explicit rank casts. -/
theorem lowerBlockLocalization_diagonal_fullRank (n d c a : ℕ)
    (ha : a + 1 = d + c) (g : Langlands.GeneralLinear (n + 1) F) :
    reindex (finCongr (by omega : (n + 1) + d + c = (a + 1) + (n + 1)))
        (lowerBlockLocalization c g (0 : Matrix (Fin d) (Fin (n + 1)) F) 1) =
      reindex (finCongr (by omega : n + (a + 1) + 1 = (a + 1) + (n + 1)))
        (appendIdentity n (a + 1) g) := by
  have he := congrArg
    (reindex (finCongr (by omega : n + (d + c) + 1 = (a + 1) + (n + 1))))
    (lowerBlockLocalization_eq_appendIdentity n d c g)
  apply Units.ext
  ext i j
  have hij := congrArg (fun M => M i j) he
  change lowerBlockLocalization c g 0 1
      (Fin.cast (by omega : (a + 1) + (n + 1) = (n + 1) + d + c) i)
      (Fin.cast (by omega) j) =
    appendIdentity n (d + c) g (Fin.cast (by omega) i) (Fin.cast (by omega) j) at hij
  change lowerBlockLocalization c g 0 1
      (Fin.cast (by omega : (a + 1) + (n + 1) = (n + 1) + d + c) i)
      (Fin.cast (by omega) j) =
    appendIdentity n (a + 1) g (Fin.cast (by omega) i) (Fin.cast (by omega) j)
  rw [hij]
  simp only [appendIdentity_entry, Fin.val_cast, Fin.cast_inj]

/-- The off-diagonal and final-block parameters form a right perturbation
independent of the leading block. -/
theorem lowerBlockPair_right_factor (g : Langlands.GeneralLinear a F)
    (x : Matrix (Fin d) (Fin a) F) (h : lowerTriangularSubgroup d F) :
    lowerBlockPair g x h = lowerBlockPair g 0 1 * lowerBlockPair 1 x h := by
  simp only [lowerBlockPair, ← map_mul]
  apply congrArg (reindex finSumFinEquiv)
  apply Units.ext
  change Matrix.fromBlocks g.val 0 x h.val.val =
    Matrix.fromBlocks g.val 0 0 1 * Matrix.fromBlocks 1 0 x h.val.val
  simp [Matrix.fromBlocks_multiply]

/-- The perturbation at zero and identity is the identity matrix. -/
theorem lowerBlockPair_one_zero_one :
    lowerBlockPair (1 : Langlands.GeneralLinear a F)
      (0 : Matrix (Fin d) (Fin a) F) 1 = 1 := by
  calc
    _ = reindex (R := F) finSumFinEquiv (1 :
        Matrix.GeneralLinearGroup (Fin a ⊕ Fin d) F) := by
      unfold lowerBlockPair
      apply congrArg (reindex finSumFinEquiv)
      apply Units.ext
      change Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 1 = 1
      exact Matrix.fromBlocks_one
    _ = 1 := map_one _

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Joint continuity of the actual right perturbation, including its inverse
matrix in the matrix-unit topology. -/
theorem continuous_lowerBlockPair_perturbation :
    Continuous (fun p : Matrix (Fin d) (Fin a) F × lowerTriangularSubgroup d F =>
      lowerBlockPair (1 : Langlands.GeneralLinear a F) p.1 p.2) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun p : Matrix (Fin d) (Fin a) F × lowerTriangularSubgroup d F =>
      (Matrix.fromBlocks 1 0 p.1 p.2.val.val).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm)
    exact (continuous_const.matrix_fromBlocks continuous_const continuous_fst
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd))).matrix_submatrix _ _
  · change Continuous (fun p : Matrix (Fin d) (Fin a) F × lowerTriangularSubgroup d F =>
      (Matrix.fromBlocks 1 0 (-p.2.val⁻¹.val * p.1 * 1) p.2.val⁻¹.val).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm)
    exact (continuous_const.matrix_fromBlocks continuous_const
      ((((Units.continuous_coe_inv.comp
        (continuous_subtype_val.comp continuous_snd)).neg).matrix_mul
          continuous_fst).matrix_mul continuous_const)
      (Units.continuous_coe_inv.comp
        (continuous_subtype_val.comp continuous_snd))).matrix_submatrix _ _

end Matrices

section Coefficients

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {a d n : ℕ} (hn : a + d = n + 1)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : UnitaryAdditiveCharacter F)
variable (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- A fixed smooth test coefficient is unchanged on sufficiently small
rectangular and lower-triangular perturbations, uniformly in the leading block.
Both neighborhoods are actual neighborhoods at zero and identity. -/
theorem exists_lowerBlockPair_test_neighborhoods
    (hσ : IsSmooth σ) (W : InverseWhittakerFunctions ψ n)
    (hW : W ∈ inverseWhittakerSet ψ n σ) :
    ∃ (Ux : Set (Matrix (Fin d) (Fin a) F))
      (Uh : Set (lowerTriangularSubgroup d F)),
      Ux ∈ 𝓝 (0 : Matrix (Fin d) (Fin a) F) ∧
      Uh ∈ 𝓝 (1 : lowerTriangularSubgroup d F) ∧
      ∀ (g : Langlands.GeneralLinear a F)
        (x : Matrix (Fin d) (Fin a) F) (h : lowerTriangularSubgroup d F),
        x ∈ Ux → h ∈ Uh →
        W.val (reindex (finCongr hn) (lowerBlockPair g x h)) =
          W.val (reindex (finCongr hn) (lowerBlockPair g 0 1)) := by
  obtain ⟨ℓ, hℓ⟩ := hW
  let w : (coefficientModel σ ℓ).toSubmodule := ⟨W, hℓ⟩
  obtain ⟨J, hJ⟩ := model_isSmooth σ hσ ℓ w
  let f : Matrix (Fin d) (Fin a) F × lowerTriangularSubgroup d F →
      Langlands.GeneralLinear (n + 1) F :=
    fun p => reindex (finCongr hn) (lowerBlockPair 1 p.1 p.2)
  have hf : Continuous f :=
    (reindexContinuous (finCongr hn)).continuous.comp continuous_lowerBlockPair_perturbation
  have hf1 : f (0, 1) = 1 := by
    simp only [f, lowerBlockPair_one_zero_one, map_one]
  have hpre : f ⁻¹' (J : Set _) ∈ 𝓝
      ((0 : Matrix (Fin d) (Fin a) F), (1 : lowerTriangularSubgroup d F)) := by
    apply hf.continuousAt.preimage_mem_nhds
    rw [hf1]
    exact J.mem_nhds_one
  obtain ⟨Ux, hUx, Uh, hUh, hsub⟩ := mem_nhds_prod_iff.mp hpre
  refine ⟨Ux, Uh, hUx, hUh, ?_⟩
  intro g x h hx hh
  have hj : f (x, h) ∈ J := hsub ⟨hx, hh⟩
  have hfix := congrArg
    (fun v : (coefficientModel σ ℓ).toSubmodule =>
      v.val.val (reindex (finCongr hn) (lowerBlockPair g 0 1)))
    (hJ ⟨f (x, h), hj⟩)
  change W.val (reindex (finCongr hn) (lowerBlockPair g 0 1) * f (x, h)) =
    W.val (reindex (finCongr hn) (lowerBlockPair g 0 1)) at hfix
  rw [lowerBlockPair_right_factor, map_mul]
  exact hfix

end Coefficients

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The actual determinant-norm-one locus in the lower-triangular group is an
identity neighborhood. It may be intersected with the smooth-test neighborhood
before applying arbitrarily small localization. -/
theorem lowerTriangular_det_one_nhds (d : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    {h : lowerTriangularSubgroup d F.Carrier |
      T.normalizedAbs (Matrix.det h.val.val) = 1} ∈
        𝓝 (1 : lowerTriangularSubgroup d F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let K : OpenSubgroup (Langlands.GeneralLinear d F.Carrier) :=
    ⟨(T.determinantNorm d).ker, T.isOpen_ker_determinantNorm d⟩
  have hpre :
      (fun h : lowerTriangularSubgroup d F.Carrier => h.val) ⁻¹' (K : Set _) ∈
        𝓝 (1 : lowerTriangularSubgroup d F.Carrier) := by
    apply (K.isOpen.preimage continuous_subtype_val).mem_nhds
    exact K.one_mem
  convert hpre using 1
  ext h
  change T.normalizedAbs (Matrix.det h.val.val) = 1 ↔
    T.determinantNorm d h.val = 1
  rw [← Units.val_inj, ← NNReal.coe_inj]
  rfl

end Padic

end Langlands.RankinSelberg.InducedTailIntermediate
