import Langlands.Automorphic.CuspidalL2.FiniteAbsorption
import Langlands.Automorphic.CuspidalL2.UnipotentMeanValue

/-! # Rapid decay of cuspidal families along a maximal block -/

noncomputable section
universe u
open scoped Classical Topology
open NumberField
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GeneralLinear

variable {R : Type*} [CommRing R] {a b n : ℕ}

/-- The nilpotent part of a block unipotent matrix. -/
theorem blockUnipotent_val_sub_one (h : a + b = n) (X : Matrix (Fin a) (Fin b) R) :
    (blockUnipotent h X : Matrix (Fin n) (Fin n) R) - 1 =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks 0 X 0 0) := by
  ext k l
  obtain ⟨p, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective k
  obtain ⟨q, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective l
  rcases p with i | i <;> rcases q with j | j <;>
    simp [blockUnipotent_val, Matrix.one_apply]
  all_goals intro hc; have := congrArg Fin.val hc; simp at this; omega

theorem blockNilpotent_mul_self (h : a + b = n) (X : Matrix (Fin a) (Fin b) R) :
    Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks 0 X 0 0) *
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks 0 X 0 0) = 0 := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  simp

end Langlands.GeneralLinear

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

omit [NumberField K] in
/-- The real embedding into the infinite adeles is compatible with the real structure of
the mixed space. -/
theorem ringEquiv_mixedSpace_infiniteRealEmbedding (s : ℝ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (PositiveRealIdeles.infiniteRealEmbedding K s) =
      algebraMap ℝ (mixedEmbedding.mixedSpace K) s := by
  apply Prod.ext
  · funext v
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
      (PositiveRealIdeles.realEmbedding K v.1 s) = s
    simp only [PositiveRealIdeles.realEmbedding, v.2, ↓reduceDIte]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal v.2).apply_symm_apply s
  · funext v
    change InfinitePlace.Completion.extensionEmbedding v.1
      (PositiveRealIdeles.realEmbedding K v.1 s) = (s : ℂ)
    have hv : ¬ v.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr v.2
    simp only [PositiveRealIdeles.realEmbedding, hv, ↓reduceDIte]
    exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.2).apply_symm_apply _

namespace ArchimedeanGL

variable {K n}

/-- The square-zero matrix `g⁻¹ u(Y) g - 1`, in archimedean coordinates. -/
def conjNilpotent {a b : ℕ} (h : a + b = n) (g : InfiniteAdelicGL K n)
    (Y : Matrix (Fin a) (Fin b) (InfiniteAdeles K)) : ArchimedeanMatrix K n :=
  (archimedeanGLCoordinates K n (g⁻¹ * GeneralLinear.blockUnipotent h Y * g) :
    ArchimedeanMatrix K n) - 1

omit [NumberField K] in
theorem conjNilpotent_eq {a b : ℕ} (h : a + b = n) (g : InfiniteAdelicGL K n)
    (Y : Matrix (Fin a) (Fin b) (InfiniteAdeles K)) :
    conjNilpotent h g Y =
      (((archimedeanGLCoordinates K n g)⁻¹ : ArchimedeanGL K n) : ArchimedeanMatrix K n) *
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks 0 (Y.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom)
            0 0) *
        (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) := by
  have hbu : archimedeanGLCoordinates K n (GeneralLinear.blockUnipotent h Y) =
      GeneralLinear.blockUnipotent h
        (Y.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom) :=
    GeneralLinear.map_blockUnipotent _ h Y
  rw [conjNilpotent, map_mul, map_mul, map_inv, hbu, ← GeneralLinear.blockUnipotent_val_sub_one,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]

omit [NumberField K] in
theorem conjNilpotent_mul_self {a b : ℕ} (h : a + b = n) (g : InfiniteAdelicGL K n)
    (Y : Matrix (Fin a) (Fin b) (InfiniteAdeles K)) :
    conjNilpotent h g Y * conjNilpotent h g Y = 0 := by
  rw [conjNilpotent_eq]
  set A := (((archimedeanGLCoordinates K n g)⁻¹ : ArchimedeanGL K n) : ArchimedeanMatrix K n)
  set B := (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)
  set Nl := Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
    (Matrix.fromBlocks 0 (Y.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom) 0 0)
  have hBA : B * A = 1 := Units.mul_inv _
  have hN : Nl * Nl = 0 := GeneralLinear.blockNilpotent_mul_self h _
  rw [show A * Nl * B * (A * Nl * B) = A * (Nl * (B * A) * Nl) * B by
    simp only [Matrix.mul_assoc], hBA, Matrix.mul_one, hN, Matrix.mul_zero, Matrix.zero_mul]

omit [NumberField K] in
theorem squareZeroElement_eq_conj {a b : ℕ} (h : a + b = n) (g : InfiniteAdelicGL K n)
    (Y : Matrix (Fin a) (Fin b) (InfiniteAdeles K)) (Z : ArchimedeanMatrix K n)
    (hZ : Z * Z = 0) (hZY : Z = conjNilpotent h g Y) :
    squareZeroElement Z hZ = g⁻¹ * GeneralLinear.blockUnipotent h Y * g := by
  subst hZY
  apply (archimedeanGLCoordinates K n).injective
  rw [squareZeroElement, ContinuousMulEquiv.apply_symm_apply]
  apply Units.ext
  rw [squareZeroUnit_val, conjNilpotent, add_sub_cancel]

omit [NumberField K] in
theorem conjNilpotent_smul {a b : ℕ} (h : a + b = n) (g : InfiniteAdelicGL K n)
    (Y : Matrix (Fin a) (Fin b) (InfiniteAdeles K)) (s : ℝ) :
    conjNilpotent h g (PositiveRealIdeles.infiniteRealEmbedding K s • Y) =
      s • conjNilpotent h g Y := by
  have hmap : (PositiveRealIdeles.infiniteRealEmbedding K s • Y).map
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom =
      s • Y.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom := by
    refine Matrix.ext fun p r => ?_
    change InfiniteAdeleRing.ringEquiv_mixedSpace K
        (PositiveRealIdeles.infiniteRealEmbedding K s * Y p r) =
      s • InfiniteAdeleRing.ringEquiv_mixedSpace K (Y p r)
    rw [map_mul, ringEquiv_mixedSpace_infiniteRealEmbedding, Algebra.smul_def]
  have hre : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (mixedEmbedding.mixedSpace K),
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (s • M) = s • Matrix.reindex (finSumFinEquiv.trans (finCongr h))
          (finSumFinEquiv.trans (finCongr h)) M := by
    intro M
    rfl
  have hblock : Matrix.fromBlocks (0 : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace K))
      (s • Y.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom) 0
      (0 : Matrix (Fin b) (Fin b) (mixedEmbedding.mixedSpace K)) =
      s • Matrix.fromBlocks 0 (Y.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom) 0 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero, smul_zero, smul_zero]
  rw [conjNilpotent_eq, conjNilpotent_eq, hmap, hblock, hre, Matrix.mul_smul, Matrix.smul_mul]

omit [NumberField K] in
theorem continuous_conjNilpotent {a b : ℕ} (h : a + b = n) :
    Continuous fun p : InfiniteAdelicGL K n × Matrix (Fin a) (Fin b) (InfiniteAdeles K) =>
      conjNilpotent h p.1 p.2 := by
  unfold conjNilpotent
  refine Continuous.sub ?_ continuous_const
  exact Units.continuous_val.comp ((archimedeanGLCoordinates K n).continuous.comp
    ((continuous_fst.inv.mul ((GeneralLinear.continuous_blockUnipotent h).comp continuous_snd)).mul
      continuous_fst))

variable (K n)

/-- A fixed real basis of the archimedean matrix algebra. -/
def lieBasis :
    Module.Basis (Fin (Module.finrank ℝ (ArchimedeanMatrix K n))) ℝ (ArchimedeanMatrix K n) :=
  Module.finBasis ℝ (ArchimedeanMatrix K n)

/-- The real Lie algebra directions given by `lieBasis`. -/
def lieDirection (k : Fin (Module.finrank ℝ (ArchimedeanMatrix K n))) : RealLieAlgebra K n :=
  (realLieAlgebraToMatrix K n).symm (lieBasis K n k)

variable {K n}

/-- A directional derivative is the combination of the basis derivatives with the basis
coordinates of the direction. -/
theorem smoothDifferential_val_eq_sum (f : SmoothFunctions K n) (Zm : ArchimedeanMatrix K n)
    (y : InfiniteAdelicGL K n) :
    (smoothDifferential K n ((realLieAlgebraToMatrix K n).symm Zm) f).val y =
      ∑ k, ((lieBasis K n).repr Zm k : ℂ) *
        (smoothDifferential K n (lieDirection K n k) f).val y := by
  simp only [smoothDifferential_apply, lieDirection, LinearEquiv.apply_symm_apply]
  conv_lhs => rw [← (lieBasis K n).sum_repr Zm]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, ContinuousLinearMap.map_smul, Complex.real_smul]

end ArchimedeanGL

/-- Archimedean block matrices whose entries are `t * z` with `0 ≤ t ≤ 1` and `z ∈ D`. -/
def scaledBlockSet {a b : ℕ} (D : Set (InfiniteAdeles K)) :
    Set (Matrix (Fin a) (Fin b) (InfiniteAdeles K)) :=
  {Y | ∀ p r, Y p r ∈ (fun z : ℝ × InfiniteAdeles K =>
    PositiveRealIdeles.infiniteRealEmbedding K z.1 * z.2) '' (Set.Icc 0 1 ×ˢ D)}

omit [NumberField K] in
variable {K} in
theorem isCompact_scaledBlockSet {a b : ℕ} {D : Set (InfiniteAdeles K)} (hD : IsCompact D) :
    IsCompact (scaledBlockSet K (a := a) (b := b) D) := by
  have hE : IsCompact ((fun z : ℝ × InfiniteAdeles K =>
      PositiveRealIdeles.infiniteRealEmbedding K z.1 * z.2) '' (Set.Icc 0 1 ×ˢ D)) :=
    (isCompact_Icc.prod hD).image
      (((PositiveRealIdeles.continuous_infiniteRealEmbedding K).comp continuous_fst).mul
        continuous_snd)
  have : scaledBlockSet K (a := a) (b := b) D = Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (fun z : ℝ × InfiniteAdeles K =>
        PositiveRealIdeles.infiniteRealEmbedding K z.1 * z.2) '' (Set.Icc 0 1 ×ˢ D) := by
    ext W
    exact ⟨fun hW i _ j _ => hW i j, fun hW i j => hW i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hE

omit [NumberField K] in
variable {K} in
theorem mem_scaledBlockSet {a b : ℕ} {D : Set (InfiniteAdeles K)}
    (t : Fin a → Fin b → ℝ) (ht : ∀ p r, t p r ∈ Set.Icc (0 : ℝ) 1)
    (z : Fin a → Fin b → InfiniteAdeles K) (hz : ∀ p r, z p r ∈ D) :
    (Matrix.of fun p r => PositiveRealIdeles.infiniteRealEmbedding K (t p r) * z p r) ∈
      scaledBlockSet K D :=
  fun p r => ⟨(t p r, z p r), ⟨ht p r, hz p r⟩, rfl⟩

open ArchimedeanGL in
/-- **Abstract rapid decay along a maximal block.** Let `φ i` be a family of functions on the
adelic group, closed under the basis derivatives `der k`, left invariant under rational
points, right invariant under a common open subgroup `L` of the finite adelic group, with
smooth archimedean slices, cuspidal along the block `(a, b)` in the mean-value form `hcusp`,
and bounded on `torInf x * Q` by `C * w x` for compact `Q` with finite parts in `F₀`. Then on
the region where every across-the-block gap `x_r - x_p` is at most `-ℓ ≤ 0`, each `φ i`
gains the extra factor `exp (-N ℓ)` for every `N`. -/
theorem blockDecay_of_cuspidal {ι : Type*} {a b : ℕ} (h : a + b = n)
    (φ : ι → AdelicGL K n → ℂ)
    (der : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → ι → ι)
    (hrat : ∀ i (γ : RationalGL K n) g, φ i (AdelicGL.rational K n γ * g) = φ i g)
    (L : Subgroup (FiniteAdelicGL K n)) (hL : IsOpen (L : Set (FiniteAdelicGL K n)))
    (hlevel : ∀ i g, ∀ ℓ ∈ L, φ i (g * AdelicGL.ofFinite K n ℓ) = φ i g)
    (hslice : ∀ i (y : FiniteAdelicGL K n), ∃ s : SmoothFunctions K n,
      (∀ g, s.val g = φ i (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) ∧
      ∀ k g, (smoothDifferential K n (lieDirection K n k) s).val g =
        φ (der k i) (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y))
    (hcusp : ∀ i g (M : ℝ), (∀ Y : Matrix (Fin a) (Fin b) (Adeles K),
      ‖φ i (GeneralLinear.blockUnipotent h Y * g) - φ i g‖ ≤ M) → ‖φ i g‖ ≤ M)
    (F₀ : Set (FiniteAdelicGL K n)) (w : (Fin n → ℝ) → ℝ)
    (hgrowth : ∀ i (Q : Set (AdelicGL K n)), IsCompact Q →
      (∀ q ∈ Q, AdelicGL.finite K n q ∈ F₀) → ∃ C : ℝ, ∀ x, ∀ q ∈ Q,
        ‖φ i (AdelicGL.ofInfinite K n (torInf K n x) * q)‖ ≤ C * w x)
    (N : ℕ) (i : ι) (Q : Set (AdelicGL K n)) (hQ : IsCompact Q)
    (hQF : ∀ q ∈ Q, AdelicGL.finite K n q ∈ F₀) :
    ∃ C : ℝ, ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
        x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -ℓ) →
      ∀ q ∈ Q, ‖φ i (AdelicGL.ofInfinite K n (torInf K n x) * q)‖ ≤
        C * Real.exp (-(N * ℓ)) * w x := by
  induction N generalizing i Q with
  | zero =>
    obtain ⟨C, hC⟩ := hgrowth i Q hQ hQF
    exact ⟨C, fun x ℓ _ _ q hq => by simpa using hC x q hq⟩
  | succ N ih =>
    have hQf : IsCompact (AdelicGL.finite K n '' Q) :=
      hQ.image (map_continuous (AdelicGL.finite K n))
    obtain ⟨δ, hδ, hδL⟩ := exists_nsmul_conj_blockUnipotent_mem K n h L hL hQf
    set D : Set (InfiniteAdeles K) :=
      (fun z => (δ : InfiniteAdeles K) * z) '' archimedeanFundamentalSet K with hDdef
    have hD : IsCompact D :=
      (isCompact_archimedeanFundamentalSet K).image (continuous_const.mul continuous_id)
    set 𝒲 := scaledBlockSet K (a := a) (b := b) D with h𝒲def
    have h𝒲 : IsCompact 𝒲 := isCompact_scaledBlockSet hD
    set Q' : Set (AdelicGL K n) :=
      (fun p : Matrix (Fin a) (Fin b) (InfiniteAdeles K) × AdelicGL K n =>
        AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h p.1) * p.2) '' (𝒲 ×ˢ Q)
      with hQ'def
    have hQ' : IsCompact Q' :=
      (h𝒲.prod hQ).image (((map_continuous (AdelicGL.ofInfinite K n)).comp
        ((GeneralLinear.continuous_blockUnipotent h).comp continuous_fst)).mul continuous_snd)
    have hQ'F : ∀ q ∈ Q', AdelicGL.finite K n q ∈ F₀ := by
      rintro _ ⟨p, hp, rfl⟩
      simpa using hQF p.2 hp.2
    choose C hC using fun k => ih (der k i) Q' hQ' hQ'F
    obtain ⟨B, hB⟩ := (h𝒲.prod hQ).exists_bound_of_continuousOn
      (f := fun p : Matrix (Fin a) (Fin b) (InfiniteAdeles K) × AdelicGL K n =>
        ∑ k, |(lieBasis K n).coord k (conjNilpotent h (AdelicGL.infinite K n p.2) p.1)|)
      (Continuous.continuousOn (continuous_finsetSum _ fun k _ =>
        (((lieBasis K n).coord k).continuous_of_finiteDimensional.comp
          ((continuous_conjNilpotent h).comp
            (((map_continuous (AdelicGL.infinite K n)).comp continuous_snd).prodMk
              continuous_fst))).abs))
    refine ⟨B * ∑ k, C k, fun x ℓ hℓ hgap q hq => ?_⟩
    set e := finSumFinEquiv.trans (finCongr h) with he
    set qi := AdelicGL.infinite K n q with hqi
    set qf := AdelicGL.finite K n q with hqf
    set E : ℝ := Real.exp (-(N * ℓ)) * w x with hE
    have hq_dec : q = AdelicGL.ofInfinite K n qi * AdelicGL.ofFinite K n qf :=
      AdelicGL.eq_ofInfinite_mul_ofFinite K n q
    have hg : AdelicGL.ofInfinite K n (torInf K n x) * q =
        AdelicGL.ofInfinite K n (torInf K n x * qi) * AdelicGL.ofFinite K n qf := by
      conv_lhs => rw [hq_dec]
      rw [map_mul, mul_assoc]
    obtain ⟨s0, hs0, hs0d⟩ := hslice i qf
    refine hcusp i _ _ fun Y => ?_
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
    -- The translate by `u(Y)` reduces to an archimedean translate of the slice.
    have hval1 : φ i (GeneralLinear.blockUnipotent h
          (ξ.map (algebraMap K (Adeles K)) + (δ : Adeles K) • W) *
          (AdelicGL.ofInfinite K n (torInf K n x) * q)) =
        φ i (AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h Wi * torInf K n x * qi) *
          AdelicGL.ofFinite K n qf) := by
      rw [GeneralLinear.blockUnipotent_add, ← Langlands.Automorphic.rational_blockUnipotent,
        AdelicGL.blockUnipotent_eq K n h ((δ : Adeles K) • W), mul_assoc, hrat, hsplit,
        hlevel i _ _ hLmem]
    -- Torus conjugation.
    set Y' : Matrix (Fin a) (Fin b) (InfiniteAdeles K) := Matrix.of fun p r =>
      PositiveRealIdeles.infiniteRealEmbedding K
        (Real.exp (x (e (Sum.inr r)) - x (e (Sum.inl p)))) * Wi p r with hY'
    have htor : GeneralLinear.blockUnipotent h Wi * torInf K n x =
        torInf K n x * GeneralLinear.blockUnipotent h Y' := by
      rw [hY', ← torInf_inv_mul_blockUnipotent_mul]
      simp only [mul_assoc, mul_inv_cancel_left]
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
    have hYsmem : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        PositiveRealIdeles.infiniteRealEmbedding K s • Y' ∈ 𝒲 := by
      intro s hs
      have heq : PositiveRealIdeles.infiniteRealEmbedding K s • Y' = Matrix.of fun p r =>
          PositiveRealIdeles.infiniteRealEmbedding K
            (s * Real.exp (x (e (Sum.inr r)) - x (e (Sum.inl p)))) * Wi p r := by
        ext p r
        rw [hY', Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, smul_eq_mul, map_mul,
          mul_assoc]
      rw [heq]
      refine mem_scaledBlockSet _ (fun p r => ⟨mul_nonneg hs.1 (Real.exp_pos _).le, ?_⟩) _ hWiD
      have : Real.exp (x (e (Sum.inr r)) - x (e (Sum.inl p))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith [hgap p r]
      nlinarith [hs.1, hs.2, (Real.exp_pos (x (e (Sum.inr r)) - x (e (Sum.inl p)))).le]
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
    -- Coefficients of the direction are `O(exp (-ℓ))`.
    have hcoef : ∑ k, |(lieBasis K n).repr Zm k| ≤ Real.exp (-ℓ) * B := by
      have hsm : Zm = Real.exp (-ℓ) • conjNilpotent h qi Y'' := by
        rw [hZm, hY'Y'', conjNilpotent_smul]
      have hb := hB (Y'', q) ⟨hY''mem, hq⟩
      simp only [Module.Basis.coord_apply] at hb
      rw [hsm]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans hb) (Real.exp_pos _).le
    have hmvt := norm_sub_le_of_squareZero s0 X0 ((realLieAlgebraToMatrix K n).symm Zm) hZ
      (Real.exp (-ℓ) * B * ((∑ k, C k) * E)) (by
        intro s hs
        rw [smoothDifferential_val_eq_sum]
        have hpt : X0 * squareZeroElement
            (s • (realLieAlgebraToMatrix K n) ((realLieAlgebraToMatrix K n).symm Zm))
            (smul_mul_smul_eq_zero hZ s) =
            torInf K n x *
              GeneralLinear.blockUnipotent h (PositiveRealIdeles.infiniteRealEmbedding K s • Y') *
              qi :=
          hX0Z s _ _ (by rw [LinearEquiv.apply_symm_apply, hZm, conjNilpotent_smul])
        rw [hpt]
        have hterm : ∀ k, ‖(smoothDifferential K n (lieDirection K n k) s0).val
            (torInf K n x *
              GeneralLinear.blockUnipotent h (PositiveRealIdeles.infiniteRealEmbedding K s • Y') *
              qi)‖ ≤ C k * E := by
          intro k
          rw [hs0d k, map_mul, map_mul, mul_assoc, mul_assoc, ← hq_dec]
          refine (hC k x ℓ hℓ hgap
            (AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h
              (PositiveRealIdeles.infiniteRealEmbedding K s • Y')) * q)
            ⟨(_, q), ⟨hYsmem s hs, hq⟩, rfl⟩).trans (le_of_eq ?_)
          rw [hE, mul_assoc]
        have hnonneg : ∀ k, 0 ≤ C k * E := fun k => (norm_nonneg _).trans (hterm k)
        calc _ ≤ ∑ k, ‖((lieBasis K n).repr Zm k : ℂ) *
                (smoothDifferential K n (lieDirection K n k) s0).val
                  (torInf K n x * GeneralLinear.blockUnipotent h
                    (PositiveRealIdeles.infiniteRealEmbedding K s • Y') * qi)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ k, |(lieBasis K n).repr Zm k| * ∑ j, C j * E := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left ((hterm k).trans
                (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ k))) (abs_nonneg _)
          _ = (∑ k, |(lieBasis K n).repr Zm k|) * ∑ j, C j * E := by rw [Finset.sum_mul]
          _ ≤ Real.exp (-ℓ) * B * ((∑ k, C k) * E) := by
              rw [← Finset.sum_mul]
              exact mul_le_mul_of_nonneg_right hcoef
                (by rw [Finset.sum_mul]; exact Finset.sum_nonneg fun j _ => hnonneg j))
    have hleft : s0.val (X0 * squareZeroElement
        ((realLieAlgebraToMatrix K n) ((realLieAlgebraToMatrix K n).symm Zm)) hZ) =
        φ i (GeneralLinear.blockUnipotent h
          (ξ.map (algebraMap K (Adeles K)) + (δ : Adeles K) • W) *
          (AdelicGL.ofInfinite K n (torInf K n x) * q)) := by
      rw [hX0Z 1 _ _ (by rw [LinearEquiv.apply_symm_apply, map_one, one_smul]), map_one, one_smul,
        hs0, hval1, ← htor]
    have hright : s0.val X0 = φ i (AdelicGL.ofInfinite K n (torInf K n x) * q) := by
      rw [hs0, hg]
    rw [hleft, hright] at hmvt
    refine hmvt.trans (le_of_eq ?_)
    rw [hE, show -(((N + 1 : ℕ) : ℝ) * ℓ) = -ℓ + -(N * ℓ) by push_cast; ring, Real.exp_add]
    ring

end Langlands.Global
