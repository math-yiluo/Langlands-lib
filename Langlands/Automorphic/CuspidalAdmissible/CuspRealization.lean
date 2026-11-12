import Langlands.Automorphic.CuspidalAdmissible.CuspIntegral
import Langlands.Automorphic.CuspidalAdmissible.SiegelGeometry
import Langlands.Automorphic.CuspidalAdmissible.Unfolding
import Langlands.Automorphic.CuspidalL2.SiegelCover
import Langlands.Automorphic.CuspidalUnitaryForm

/-!
# The cusp estimate for a cuspidal realization

On the part of a Siegel set lying over the determinant band where the torus coordinate has a
drop larger than `T` at a block position, the square integral of an `L`-invariant realized
vector is at most `exp(-2(T - 2nK))` times a constant times the band integrals of its basis
derivatives. The constant comes from the cusp estimate `exists_lintegral_cusp_le` and the
multiplicity of an enlarged Siegel set, which Siegel finiteness bounds.
-/

noncomputable section

universe uF

open MeasureTheory NumberField
open scoped Classical Topology ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Block unipotent matrices are unitriangular. -/
theorem isUnitriangular_blockUnipotent {a b : ℕ} (h : a + b = n)
    (X : Matrix (Fin a) (Fin b) R) :
    PrimitiveAdelicHeight.IsUnitriangular
      ((GeneralLinear.blockUnipotent h X : GeneralLinear n R) : Matrix (Fin n) (Fin n) R) := by
  set e := finSumFinEquiv.trans (finCongr h) with he
  have hval : ∀ σ, (e σ).val = Sum.elim (fun p : Fin a => p.val) (fun r : Fin b => a + r.val) σ := by
    intro σ
    cases σ <;> simp [he]
  have hentry : ∀ σ τ, ((GeneralLinear.blockUnipotent h X : GeneralLinear n R) :
      Matrix (Fin n) (Fin n) R) (e σ) (e τ) = Matrix.fromBlocks 1 X 0 1 σ τ := by
    intro σ τ
    rw [GeneralLinear.blockUnipotent_val, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · obtain ⟨σ, rfl⟩ := e.surjective i
    obtain ⟨τ, rfl⟩ := e.surjective j
    rw [hentry]
    have hlt : (e τ).val < (e σ).val := hij
    rw [hval, hval] at hlt
    cases σ with
    | inl p =>
      cases τ with
      | inl q =>
        have : p ≠ q := fun hpq => by subst hpq; simp at hlt
        simp [Matrix.fromBlocks, this]
      | inr r => simp at hlt; omega
    | inr r =>
      cases τ with
      | inl q => simp [Matrix.fromBlocks]
      | inr s =>
        have : r ≠ s := fun hrs => by subst hrs; simp at hlt
        simp [Matrix.fromBlocks, this]
  · obtain ⟨σ, rfl⟩ := e.surjective i
    rw [hentry]
    cases σ <;> simp [Matrix.fromBlocks]

variable (F : Type uF) [Field F] [NumberField F] (n)

theorem ofInfinite_apply (g : InfiniteAdelicGL F n) (i j : Fin n) :
    (AdelicGL.ofInfinite F n g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
      ((g : Matrix (Fin n) (Fin n) (InfiniteAdeles F)) i j,
        (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) i j) := by
  apply Prod.ext
  · change AdelicGL.infinite F n (AdelicGL.ofInfinite F n g) i j = _
    rw [AdelicGL.infinite_ofInfinite]
  · change AdelicGL.finite F n (AdelicGL.ofInfinite F n g) i j = _
    rw [AdelicGL.finite_ofInfinite]
    rfl

theorem isUnitriangular_ofInfinite {g : InfiniteAdelicGL F n}
    (hg : PrimitiveAdelicHeight.IsUnitriangular (g : Matrix (Fin n) (Fin n) (InfiniteAdeles F))) :
    PrimitiveAdelicHeight.IsUnitriangular
      ((AdelicGL.ofInfinite F n g : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hne : i ≠ j := fun hh => by subst hh; exact lt_irrefl _ hij
    rw [ofInfinite_apply, hg.1 hij]
    apply Prod.ext
    · rfl
    · exact Matrix.one_apply_ne hne
  · rw [ofInfinite_apply, hg.2 i]
    apply Prod.ext
    · rfl
    · exact Matrix.one_apply_eq i

theorem determinantNorm_of_isUnitriangular {g : AdelicGL F n}
    (hg : PrimitiveAdelicHeight.IsUnitriangular (g : Matrix (Fin n) (Fin n) (Adeles F))) :
    AdelicBlockDeterminantCharacter.determinantNorm F n g = 1 := by
  have hdet : AdelicGL.determinant F n g = 1 := by
    apply Units.ext
    exact PrimitiveAdelicHeight.IsUnitriangular.det_eq_one hg
  change (IdeleAbsoluteValue.full F) (AdelicGL.determinant F n g) = 1
  rw [hdet, map_one]

end Langlands.Global

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.ContinuousRationalFunctions
  Langlands.Automorphic.CuspidalL2 Langlands.Automorphic.OperatorDeterminantSlice

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance cuspRealIsAffine : _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance cuspRealSmooth : _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The cusp region at the block position `a`: points of a Siegel set over the band whose
torus coordinate (in a fixed compact frame `Q₁`, chamber constant `K`) drops by more than `T`
at `a`. -/
def cuspRegion (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F)) (c : ℝ)
    (Q₁ : Set (AdelicGL F n)) (K : ℝ) (a : Fin n) (T : ℝ) : Set (AdelicGL F n) :=
  {g | g ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c ∧ point F n g ∈ band F n ∧
    ∃ (x : Fin n → ℝ) (q : AdelicGL F n), q ∈ Q₁ ∧
      g = AdelicGL.ofInfinite F n (torInf F n x) * q ∧ Chamber K x ∧ T < chamberDrop x a}

local instance cuspRealRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspRealContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspRealSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspRealFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance cuspRealStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance cuspRealSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The band integral of the squared norm of a realized vector. -/
abbrev bandNorm (f : S.Space) : ℝ≥0∞ :=
  ∫⁻ q in band F n, ‖toQuotient F n S f q‖ₑ ^ 2 ∂quotientHaarMeasure F n

/-- The basis derivative `D_k f`. -/
abbrev basisDerivative (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) (f : S.Space) :
    S.Space :=
  S.envelopingAction (OperatorRealization.basisGenerator F n k) f

theorem slice_data_one (f : S.Space) (y : FiniteAdelicGL F n) :
    ∃ s : ArchimedeanGL.SmoothFunctions F n,
      (∀ g, s.val g = evaluate F n (S.toContinuous f)
        (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y)) ∧
      ∀ k g, (ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.lieDirection F n k) s).val g =
        evaluate F n (S.toContinuous (basisDerivative S k f))
          (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y) := by
  obtain ⟨s, hs1, hs2⟩ := S.slice_data f 1 y
  have h1 : S.envelopingAction 1 f = f := LinearMap.congr_fun (map_one S.envelopingAction) f
  refine ⟨s, fun g => (hs1 g).trans ?_, fun k g => (hs2 k g).trans ?_⟩
  · exact congrArg (fun v => evaluate F n (S.toContinuous v)
      (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y)) h1
  · exact congrArg (fun u => evaluate F n (S.toContinuous (S.envelopingAction u f))
      (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y)) (mul_one _)

/-- On a cusp region, every across-the-block gap of the torus coordinate is at most
`-(T - 2nK)`. -/
theorem cuspRegion_gap {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)}
    {c : ℝ} {Q₁ : Set (AdelicGL F n)} {K : ℝ} (hK : 0 ≤ K) {a : Fin n} (ha : 0 < a.val)
    {b : ℕ} (h : a.val + b = n) {T : ℝ} {g : AdelicGL F n}
    (hg : g ∈ cuspRegion ΩN C c Q₁ K a T) :
    ∃ (x : Fin n → ℝ) (q : AdelicGL F n), q ∈ Q₁ ∧
      g = AdelicGL.ofInfinite F n (torInf F n x) * q ∧
      ∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
        x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -(T - 2 * n * K) := by
  obtain ⟨-, -, x, q, hq, rfl, hch, hdrop⟩ := hg
  refine ⟨x, q, hq, rfl, fun p r => ?_⟩
  have hi : (finSumFinEquiv.trans (finCongr h) (Sum.inl p)).val < a.val := by
    simp
  have hj : a.val ≤ (finSumFinEquiv.trans (finCongr h) (Sum.inr r)).val := by
    simp
  have := gap_le_of_chamber hK x hch a ha _ _ hi hj
  linarith

/-- Unitriangular left translates keep the determinant band. -/
theorem point_mul_mem_band {u g : AdelicGL F n}
    (hu : PrimitiveAdelicHeight.IsUnitriangular (u : Matrix (Fin n) (Fin n) (Adeles F)))
    (hg : point F n g ∈ band F n) : point F n (u * g) ∈ band F n := by
  have hdet : quotientDeterminantNorm F n (point F n (u * g)) =
      quotientDeterminantNorm F n (point F n g) := by
    rw [quotientDeterminantNorm_point, quotientDeterminantNorm_point, map_mul,
      determinantNorm_of_isUnitriangular (F := F) (n := n) hu, one_mul]
  change 1 < (quotientDeterminantNorm F n (point F n (u * g)) : ℝ≥0) ∧
    (quotientDeterminantNorm F n (point F n (u * g)) : ℝ≥0) < 2
  rw [hdet]
  exact hg

/-- The number of rational translates meeting a Siegel set, as an extended real. -/
def siegelMultiplicity (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F))
    (c : ℝ) : ℝ≥0∞ :=
  ({γ : RationalGL F n | ∃ g ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c,
    AdelicGL.rational F n γ * g ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c}.encard : ℝ≥0∞)

theorem siegelMultiplicity_ne_top
    (hSF : PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement.{uF})
    {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)} {c : ℝ}
    (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C) (hC1 : C ⊆ NormOneIdeleClass.normOneIdeles F) (hc : 0 < c) :
    siegelMultiplicity ΩN C c ≠ ⊤ := by
  have hfin := hSF F n ΩN C c hΩ hΩN hC hC1 hc
  unfold siegelMultiplicity
  exact ENat.toENNReal_ne_top.mpr hfin.encard_lt_top.ne

/-- **Unfolding over a Siegel set.** The square integral of a realized vector over the part of
a Siegel set lying over the band is at most the multiplicity times its band integral. -/
theorem lintegral_siegelBand_le [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)} {c : ℝ}
    (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C) (f : S.Space) :
    ∫⁻ g in PrimitiveAdelicHeight.siegelSetGL F n ΩN C c ∩ point F n ⁻¹' band F n,
        ‖evaluate F n (S.toContinuous f) g‖ₑ ^ 2 ∂matrixHaarMeasure F n ≤
      siegelMultiplicity ΩN C c * bandNorm S f := by
  have ht : MeasurableSet (PrimitiveAdelicHeight.siegelSetGL F n ΩN C c ∩
      point F n ⁻¹' band F n) :=
    (measurableSet_siegelSetGL F n ΩN C c hΩ hΩN hC).inter
      ((continuous_point F n).measurable (measurableSet_band F n))
  have hle := lintegral_le_mul_quotient F n (band F n) (measurableSet_band F n) _ ht
    (fun x hx => hx.2) (siegelMultiplicity ΩN C c)
    (fun x => by
      unfold siegelMultiplicity
      exact ENat.toENNReal_le.mpr ((Set.encard_le_encard fun γ hγ => hγ.1).trans
        (encard_rational_mul_mem_le F n _ x)))
    (fun q => ‖toQuotient F n S f q‖ₑ ^ 2)
    ((toQuotient F n S f).continuous.measurable.enorm.pow_const 2)
  refine le_trans (le_of_eq ?_) hle
  refine lintegral_congr fun g => ?_
  rw [toQuotient_point]

set_option maxHeartbeats 1000000 in
/-- **Cusp estimate for a realization.** On the cusp region at a block position `a`, the square
integral of an `L`-invariant vector is at most `exp(-2(T - 2nK))` times a fixed finite constant
times the band integrals of its basis derivatives. -/
theorem exists_cuspRegion_le [CompactSpace (AdeleQuotient F)]
    [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    (hSF : PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement.{uF}) (hS : S.IsCuspidal)
    (L : Subgroup (FiniteAdelicGL F n)) (hL : IsOpen (L : Set (FiniteAdelicGL F n)))
    {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)} {c : ℝ}
    (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C) (hC1 : C ⊆ NormOneIdeleClass.normOneIdeles F) (hc : 0 < c)
    {Q₁ : Set (AdelicGL F n)} (hQ₁ : IsCompact Q₁) {K : ℝ} (hK : 0 ≤ K)
    (a : Fin n) (ha : 0 < a.val) :
    ∃ c₁ : ℝ≥0∞, c₁ ≠ ⊤ ∧ ∀ T : ℝ, 2 * n * K ≤ T → ∀ e : S.Space,
      (∀ l ∈ L, S.finiteRepresentation l e = e) →
      ∫⁻ g in cuspRegion ΩN C c Q₁ K a T, ‖evaluate F n (S.toContinuous e) g‖ₑ ^ 2
          ∂matrixHaarMeasure F n ≤
        ENNReal.ofReal (Real.exp (-(T - 2 * n * K)) ^ 2) * c₁ *
          ∑ k, bandNorm S (basisDerivative S k e) := by
  have hab : a.val + (n - a.val) = n := Nat.add_sub_cancel' a.isLt.le
  have hb : 0 < n - a.val := Nat.sub_pos_of_lt a.isLt
  obtain ⟨𝒲, B, h𝒲, hmain⟩ := exists_lintegral_cusp_le F n hab L hL Q₁ hQ₁
  set U : Set (AdelicGL F n) :=
    (fun V => AdelicGL.ofInfinite F n (GeneralLinear.blockUnipotent hab V)) '' 𝒲 with hUdef
  have hU : IsCompact U := h𝒲.image ((map_continuous (AdelicGL.ofInfinite F n)).comp
    (GeneralLinear.continuous_blockUnipotent hab))
  have hUtri : ∀ u ∈ U, PrimitiveAdelicHeight.IsUnitriangular
      (u : Matrix (Fin n) (Fin n) (Adeles F)) := by
    rintro _ ⟨V, -, rfl⟩
    exact isUnitriangular_ofInfinite (F := F) (n := n) (isUnitriangular_blockUnipotent hab V)
  set ΩN' := (fun p : AdelicGL F n × Matrix (Fin n) (Fin n) (Adeles F) =>
    (p.1 : Matrix (Fin n) (Fin n) (Adeles F)) * p.2) '' (U ×ˢ ΩN) with hΩN'def
  have hΩ' : IsCompact ΩN' := isCompact_mul_image F n U hU hΩ
  have hΩN' := isUnitriangular_mul_image F n U hUtri hΩN
  set M := siegelMultiplicity ΩN' C c with hMdef
  have hM : M ≠ ⊤ := siegelMultiplicity_ne_top hSF hΩ' hΩN' hC hC1 hc
  refine ⟨ENNReal.ofReal (B ^ 2) * M, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM,
    fun T hT e he => ?_⟩
  have hℓ : 0 ≤ T - 2 * n * K := by linarith
  have : SFinite (matrixHaarMeasure F n) := by
    unfold matrixHaarMeasure
    infer_instance
  have hcusp := hmain (S.toContinuous e)
    (fun k => evaluate F n (S.toContinuous (basisDerivative S k e)))
    (fun g => S.constantTerm_eq_zero hS hab ha hb e g)
    (fun k => continuous_evaluate F n _)
    (fun g l hl => (OperatorRealization.evaluate_finiteRepresentation S l e g).symm.trans
      (congrArg (fun v => evaluate F n (S.toContinuous v) g) (he l hl)))
    (fun y => slice_data_one S e y)
    (matrixHaarMeasure F n) (T - 2 * n * K) hℓ (cuspRegion ΩN C c Q₁ K a T)
    (PrimitiveAdelicHeight.siegelSetGL F n ΩN' C c ∩ point F n ⁻¹' band F n)
    (fun g hg => cuspRegion_gap hK ha hab hg)
    (fun V hV g hg => ⟨mul_mem_siegelSetGL F n U ⟨V, hV, rfl⟩ hg.1,
      point_mul_mem_band (hUtri _ ⟨V, hV, rfl⟩) hg.2.1⟩)
  refine hcusp.trans ?_
  have hunf : ∀ k, ∫⁻ g in PrimitiveAdelicHeight.siegelSetGL F n ΩN' C c ∩ point F n ⁻¹' band F n,
      ‖evaluate F n (S.toContinuous (basisDerivative S k e)) g‖ₑ ^ 2 ∂matrixHaarMeasure F n ≤
      M * bandNorm S (basisDerivative S k e) := fun k =>
    lintegral_siegelBand_le S hΩ' hΩN' hC _
  calc ENNReal.ofReal ((Real.exp (-(T - 2 * n * K)) * B) ^ 2) *
        ∑ k, ∫⁻ g in PrimitiveAdelicHeight.siegelSetGL F n ΩN' C c ∩ point F n ⁻¹' band F n,
          ‖evaluate F n (S.toContinuous (basisDerivative S k e)) g‖ₑ ^ 2 ∂matrixHaarMeasure F n
      ≤ ENNReal.ofReal ((Real.exp (-(T - 2 * n * K)) * B) ^ 2) *
          ∑ k, M * bandNorm S (basisDerivative S k e) := by
        gcongr with k
        exact hunf k
    _ = ENNReal.ofReal (Real.exp (-(T - 2 * n * K)) ^ 2) * (ENNReal.ofReal (B ^ 2) * M) *
          ∑ k, bandNorm S (basisDerivative S k e) := by
        rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ← Finset.mul_sum]
        ring

end Langlands.Automorphic.CuspidalAdmissible
