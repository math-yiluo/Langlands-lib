import Langlands.Automorphic.CuspidalL2.Decay
import Langlands.Automorphic.CuspidalAdmissible.SquareZeroL2

/-!
# The pointwise square-mean estimate for a unipotent translate in the cusp

For a function on the adelic group with smooth archimedean slices, rationally left invariant
and right invariant under an open subgroup of the finite adelic group, the squared difference
`|φ(u(Y) g) - φ(g)|²` at a point `g = torInf x · q` (with `q` in a compact set and every
across-the-block gap of `x` at most `-ℓ`) is bounded by `exp(-2ℓ)` times a constant times the
integral over `s ∈ [0, 1]` of the squared basis derivatives at the left translates
`u_∞(s W_∞) g`. Here `W_∞` depends only on `Y` and lies, after scaling by any `s ∈ [0, 1]`,
in a fixed compact set. The argument follows the inductive step of the Library's
`blockDecay_of_cuspidal`, with the mean value estimate replaced by its square-mean form.
-/

noncomputable section

universe u

open MeasureTheory NumberField
open scoped Classical Topology ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.CuspidalAdmissible

/-- `‖∑ c_k v_k‖² ≤ (∑ |c_k|)² ∑ ‖v_k‖²`. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → ℂ) :
    ‖∑ k ∈ s, (c k : ℂ) * v k‖ ^ 2 ≤ (∑ k ∈ s, |c k|) ^ 2 * ∑ k ∈ s, ‖v k‖ ^ 2 := by
  set A := ∑ k ∈ s, ‖v k‖ ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hv : ∀ k ∈ s, ‖v k‖ ≤ Real.sqrt A := fun k hk =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) hk)
  have h1 : ‖∑ k ∈ s, (c k : ℂ) * v k‖ ≤ (∑ k ∈ s, |c k|) * Real.sqrt A := by
    calc ‖∑ k ∈ s, (c k : ℂ) * v k‖ ≤ ∑ k ∈ s, ‖(c k : ℂ) * v k‖ := norm_sum_le _ _
      _ = ∑ k ∈ s, |c k| * ‖v k‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ k ∈ s, |c k| * Real.sqrt A :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hv k hk) (abs_nonneg _)
      _ = (∑ k ∈ s, |c k|) * Real.sqrt A := by rw [Finset.sum_mul]
  have h2 : 0 ≤ ‖∑ k ∈ s, (c k : ℂ) * v k‖ := norm_nonneg _
  calc ‖∑ k ∈ s, (c k : ℂ) * v k‖ ^ 2 ≤ ((∑ k ∈ s, |c k|) * Real.sqrt A) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
    _ = (∑ k ∈ s, |c k|) ^ 2 * A := by rw [mul_pow, Real.sq_sqrt hA0]

theorem enorm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → ℂ) :
    ‖∑ k ∈ s, (c k : ℂ) * v k‖ₑ ^ 2 ≤
      ENNReal.ofReal ((∑ k ∈ s, |c k|) ^ 2) * ∑ k ∈ s, ‖v k‖ₑ ^ 2 := by
  have h := norm_sum_mul_sq_le s c v
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hsum : ∑ k ∈ s, ‖v k‖ₑ ^ 2 = ENNReal.ofReal (∑ k ∈ s, ‖v k‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hsum, ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

end Langlands.Automorphic.CuspidalAdmissible

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

open ArchimedeanGL in
/-- **Pointwise square-mean cusp estimate.** -/
theorem exists_cusp_pointwise {a b : ℕ} (h : a + b = n)
    (L : Subgroup (FiniteAdelicGL K n)) (hL : IsOpen (L : Set (FiniteAdelicGL K n)))
    (Q : Set (AdelicGL K n)) (hQ : IsCompact Q) :
    ∃ (𝒲 : Set (Matrix (Fin a) (Fin b) (InfiniteAdeles K))) (B : ℝ), IsCompact 𝒲 ∧
      ∀ Y : Matrix (Fin a) (Fin b) (Adeles K), ∃ Wi : Matrix (Fin a) (Fin b) (InfiniteAdeles K),
        (∀ s ∈ Set.Icc (0 : ℝ) 1, PositiveRealIdeles.infiniteRealEmbedding K s • Wi ∈ 𝒲) ∧
        ∀ (φ : AdelicGL K n → ℂ)
          (dφ : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → AdelicGL K n → ℂ),
          (∀ (γ : RationalGL K n) g, φ (AdelicGL.rational K n γ * g) = φ g) →
          (∀ g, ∀ ℓ ∈ L, φ (g * AdelicGL.ofFinite K n ℓ) = φ g) →
          (∀ y : FiniteAdelicGL K n, ∃ s : SmoothFunctions K n,
            (∀ g, s.val g = φ (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) ∧
            ∀ k g, (smoothDifferential K n (lieDirection K n k) s).val g =
              dφ k (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) →
        ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
          (∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
            x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -ℓ) →
          ∀ q ∈ Q,
            ‖φ (GeneralLinear.blockUnipotent h Y *
                (AdelicGL.ofInfinite K n (torInf K n x) * q)) -
              φ (AdelicGL.ofInfinite K n (torInf K n x) * q)‖ₑ ^ 2 ≤
            ENNReal.ofReal ((Real.exp (-ℓ) * B) ^ 2) *
              ∫⁻ s in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (AdelicGL.ofInfinite K n
                (GeneralLinear.blockUnipotent h
                  (PositiveRealIdeles.infiniteRealEmbedding K s • Wi)) *
                (AdelicGL.ofInfinite K n (torInf K n x) * q))‖ₑ ^ 2 := by
  have hQf : IsCompact (AdelicGL.finite K n '' Q) :=
    hQ.image (map_continuous (AdelicGL.finite K n))
  obtain ⟨δ, hδ, hδL⟩ := exists_nsmul_conj_blockUnipotent_mem K n h L hL hQf
  set D : Set (InfiniteAdeles K) :=
    (fun z => (δ : InfiniteAdeles K) * z) '' archimedeanFundamentalSet K with hDdef
  have hD : IsCompact D :=
    (isCompact_archimedeanFundamentalSet K).image (continuous_const.mul continuous_id)
  set 𝒲 := scaledBlockSet K (a := a) (b := b) D with h𝒲def
  have h𝒲 : IsCompact 𝒲 := isCompact_scaledBlockSet hD
  obtain ⟨B, hB⟩ := (h𝒲.prod hQ).exists_bound_of_continuousOn
    (f := fun p : Matrix (Fin a) (Fin b) (InfiniteAdeles K) × AdelicGL K n =>
      ∑ k, |(lieBasis K n).coord k (conjNilpotent h (AdelicGL.infinite K n p.2) p.1)|)
    (Continuous.continuousOn (continuous_finsetSum _ fun k _ =>
      (((lieBasis K n).coord k).continuous_of_finiteDimensional.comp
        ((continuous_conjNilpotent h).comp
          (((map_continuous (AdelicGL.infinite K n)).comp continuous_snd).prodMk
            continuous_fst))).abs))
  refine ⟨𝒲, B, h𝒲, fun Y => ?_⟩
  obtain ⟨ξ, W, hW, rfl⟩ := exists_matrix_decomposition K hδ Y
  set Wi : Matrix (Fin a) (Fin b) (InfiniteAdeles K) :=
    ((δ : Adeles K) • W).map (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeles K)) with hWi
  set Wf : Matrix (Fin a) (Fin b) (FiniteAdeles K) :=
    ((δ : Adeles K) • W).map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeles K)) with hWf
  have hWfδ : Wf = δ • W.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeles K)) := by
    refine Matrix.ext fun p r => ?_
    change ((δ : Adeles K) * W p r).2 = δ • (W p r).2
    rw [Prod.snd_mul, Prod.snd_natCast, nsmul_eq_mul]
  have hWiD : ∀ p r, Wi p r ∈ D := fun p r => ⟨(W p r).1, (hW p r).1, by
    change (δ : InfiniteAdeles K) * (W p r).1 = ((δ : Adeles K) * W p r).1
    rw [Prod.fst_mul, Prod.fst_natCast]⟩
  refine ⟨Wi, fun s hs => ?_, fun φ dφ hrat hlevel hslice x ℓ hℓ hgap q hq => ?_⟩
  · have heq : PositiveRealIdeles.infiniteRealEmbedding K s • Wi = Matrix.of fun p r =>
        PositiveRealIdeles.infiniteRealEmbedding K (s * 1) * Wi p r := by
      ext p r
      rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
    rw [heq]
    exact mem_scaledBlockSet _ (fun p r => ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩) _ hWiD
  set e := finSumFinEquiv.trans (finCongr h) with he
  set qi := AdelicGL.infinite K n q with hqi
  set qf := AdelicGL.finite K n q with hqf
  have hq_dec : q = AdelicGL.ofInfinite K n qi * AdelicGL.ofFinite K n qf :=
    AdelicGL.eq_ofInfinite_mul_ofFinite K n q
  have hg : AdelicGL.ofInfinite K n (torInf K n x) * q =
      AdelicGL.ofInfinite K n (torInf K n x * qi) * AdelicGL.ofFinite K n qf := by
    conv_lhs => rw [hq_dec]
    rw [map_mul, mul_assoc]
  obtain ⟨s0, hs0, hs0d⟩ := hslice qf
  have hLmem : qf⁻¹ * GeneralLinear.blockUnipotent h Wf * qf ∈ L := by
    rw [hWfδ]
    exact hδL _ (fun p r => (hW p r).2) qf ⟨q, hq, rfl⟩
  have hsplit : AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h Wi) *
      AdelicGL.ofFinite K n (GeneralLinear.blockUnipotent h Wf) *
        (AdelicGL.ofInfinite K n (torInf K n x) * q) =
      AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h Wi * torInf K n x * qi) *
        AdelicGL.ofFinite K n qf *
        AdelicGL.ofFinite K n (qf⁻¹ * GeneralLinear.blockUnipotent h Wf * qf) := by
    refine AdelicGL.ext_infinite_finite K n ?_ ?_ <;> simp [hqi, hqf, mul_assoc]
  have hval1 : φ (GeneralLinear.blockUnipotent h
        (ξ.map (algebraMap K (Adeles K)) + (δ : Adeles K) • W) *
        (AdelicGL.ofInfinite K n (torInf K n x) * q)) =
      φ (AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h Wi * torInf K n x * qi) *
        AdelicGL.ofFinite K n qf) := by
    rw [GeneralLinear.blockUnipotent_add, ← Langlands.Automorphic.rational_blockUnipotent,
      AdelicGL.blockUnipotent_eq K n h ((δ : Adeles K) • W), mul_assoc, hrat, hsplit,
      hlevel _ _ hLmem]
  -- Torus conjugation.
  set Y' : Matrix (Fin a) (Fin b) (InfiniteAdeles K) := Matrix.of fun p r =>
    PositiveRealIdeles.infiniteRealEmbedding K
      (Real.exp (x (e (Sum.inr r)) - x (e (Sum.inl p)))) * Wi p r with hY'
  have htors : ∀ s : ℝ, GeneralLinear.blockUnipotent h
      (PositiveRealIdeles.infiniteRealEmbedding K s • Wi) * torInf K n x =
      torInf K n x * GeneralLinear.blockUnipotent h
        (PositiveRealIdeles.infiniteRealEmbedding K s • Y') := by
    intro s
    have hconj := torInf_inv_mul_blockUnipotent_mul K n h x
      (PositiveRealIdeles.infiniteRealEmbedding K s • Wi)
    have hY's : (Matrix.of fun i j => PositiveRealIdeles.infiniteRealEmbedding K
        (Real.exp (x (finSumFinEquiv.trans (finCongr h) (Sum.inr j)) -
          x (finSumFinEquiv.trans (finCongr h) (Sum.inl i)))) *
        (PositiveRealIdeles.infiniteRealEmbedding K s • Wi) i j) =
        PositiveRealIdeles.infiniteRealEmbedding K s • Y' := by
      ext p r
      rw [hY', Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul]
      ring
    rw [hY's] at hconj
    rw [← hconj]
    simp only [mul_assoc, mul_inv_cancel_left]
  have htor : GeneralLinear.blockUnipotent h Wi * torInf K n x =
      torInf K n x * GeneralLinear.blockUnipotent h Y' := by
    have := htors 1
    simpa only [map_one, one_smul] using this
  set Y'' : Matrix (Fin a) (Fin b) (InfiniteAdeles K) := Matrix.of fun p r =>
    PositiveRealIdeles.infiniteRealEmbedding K
      (Real.exp (x (e (Sum.inr r)) - x (e (Sum.inl p)) + ℓ)) * Wi p r with hY''
  have hY'Y'' : Y' = PositiveRealIdeles.infiniteRealEmbedding K (Real.exp (-ℓ)) • Y'' := by
    ext p r
    rw [hY', hY'', Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, smul_eq_mul,
      ← mul_assoc, ← map_mul, ← Real.exp_add]
    congr 3
    ring
  have hY''mem : Y'' ∈ 𝒲 := by
    refine mem_scaledBlockSet _ (fun p r => ⟨(Real.exp_pos _).le, ?_⟩) _ hWiD
    rw [Real.exp_le_one_iff]
    linarith [hgap p r]
  set Zm := conjNilpotent h qi Y' with hZm
  have hZ : (realLieAlgebraToMatrix K n) ((realLieAlgebraToMatrix K n).symm Zm) *
      (realLieAlgebraToMatrix K n) ((realLieAlgebraToMatrix K n).symm Zm) = 0 := by
    rw [LinearEquiv.apply_symm_apply]
    exact conjNilpotent_mul_self h qi Y'
  set X0 := torInf K n x * qi with hX0
  have hX0Z : ∀ (t : ℝ) (Z : ArchimedeanMatrix K n) (hZ : Z * Z = 0),
      Z = conjNilpotent h qi (PositiveRealIdeles.infiniteRealEmbedding K t • Y') →
      X0 * squareZeroElement Z hZ =
        torInf K n x *
          GeneralLinear.blockUnipotent h (PositiveRealIdeles.infiniteRealEmbedding K t • Y') *
          qi := by
    intro t Z hZ hZe
    rw [squareZeroElement_eq_conj h qi _ Z hZ hZe, hX0]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hcoef : ∑ k, |(lieBasis K n).repr Zm k| ≤ Real.exp (-ℓ) * B := by
    have hsm : Zm = Real.exp (-ℓ) • conjNilpotent h qi Y'' := by
      rw [hZm, hY'Y'', conjNilpotent_smul]
    have hb := hB (Y'', q) ⟨hY''mem, hq⟩
    simp only [Module.Basis.coord_apply] at hb
    rw [hsm]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans hb) (Real.exp_pos _).le
  have hL2 := enorm_sub_sq_le_lintegral_squareZero s0 X0
    ((realLieAlgebraToMatrix K n).symm Zm) hZ
  have hleft : s0.val (X0 * squareZeroElement
      ((realLieAlgebraToMatrix K n) ((realLieAlgebraToMatrix K n).symm Zm)) hZ) =
      φ (GeneralLinear.blockUnipotent h
        (ξ.map (algebraMap K (Adeles K)) + (δ : Adeles K) • W) *
        (AdelicGL.ofInfinite K n (torInf K n x) * q)) := by
    rw [hX0Z 1 _ _ (by rw [LinearEquiv.apply_symm_apply, map_one, one_smul]), map_one, one_smul,
      hs0, hval1, ← htor]
  have hright : s0.val X0 = φ (AdelicGL.ofInfinite K n (torInf K n x) * q) := by
    rw [hs0, hg]
  rw [hleft, hright] at hL2
  refine hL2.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
  rw [smoothDifferential_val_eq_sum]
  have hpt : X0 * squareZeroElement
      (s • (realLieAlgebraToMatrix K n) ((realLieAlgebraToMatrix K n).symm Zm))
      (smul_mul_smul_eq_zero hZ s) =
      torInf K n x *
        GeneralLinear.blockUnipotent h (PositiveRealIdeles.infiniteRealEmbedding K s • Y') *
        qi :=
    hX0Z s _ _ (by rw [LinearEquiv.apply_symm_apply, hZm, conjNilpotent_smul])
  rw [hpt]
  have hterm : ∀ k, (smoothDifferential K n (lieDirection K n k) s0).val
      (torInf K n x *
        GeneralLinear.blockUnipotent h (PositiveRealIdeles.infiniteRealEmbedding K s • Y') *
        qi) =
      dφ k (AdelicGL.ofInfinite K n
        (GeneralLinear.blockUnipotent h (PositiveRealIdeles.infiniteRealEmbedding K s • Wi)) *
        (AdelicGL.ofInfinite K n (torInf K n x) * q)) := by
    intro k
    rw [hs0d k, ← htors s, hq_dec]
    simp only [map_mul, mul_assoc]
  simp only [hterm]
  refine (Langlands.Automorphic.CuspidalAdmissible.enorm_sum_mul_sq_le Finset.univ (fun k => (lieBasis K n).repr Zm k) _).trans ?_
  gcongr

end Langlands.Global
