import Langlands.Representation.Archimedean.RealTiedMinorScalar
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial

/-!
# Minor products: from the minor vectors to an `O(n)`-fixed vector

Wallach (1971), Theorem 3.2, in algebraic form, for a list `ds` of real blocks without
discrete-series block whose odd positions `R` form a bottom segment.
-/

noncomputable section

open Matrix Finset

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTiedMinorProduct

open MatrixMinor JacquetMinor GramFormula PrincipalSeriesExtension
  RealTemperedCommutantReduction RealStrictCharacterLanglandsQuotient RealTiedMinorScalar

variable {n : ℕ}

/-! ## Minors on `GL_n(ℝ)` -/

/-- The minor `g ↦ det g_{A,B}` on `GL_n(ℝ)`, as a complex function. -/
def minorG (A B : Finset (Fin n)) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ((minor (g : Matrix (Fin n) (Fin n) ℝ) A B : ℝ) : ℂ)

theorem contDiff_minor (A B : Finset (Fin n)) :
    ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => minor y A B) := by
  by_cases h : A.card = B.card
  · have he : (fun y : Matrix (Fin n) (Fin n) ℝ => minor y A B) = fun y =>
        (y.submatrix (A.orderEmbOfFin rfl) (B.orderEmbOfFin h.symm)).det :=
      funext fun y => minor_eq rfl h.symm
    rw [he]
    let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin A.card) (Fin A.card) ℝ :=
      { toFun := fun y => y.submatrix (A.orderEmbOfFin rfl) (B.orderEmbOfFin h.symm)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (RealPrincipalSeriesDuality.contDiff_det (n := A.card) ∞).comp
      (LinearMap.toContinuousLinearMap L).contDiff
  · have he : (fun y : Matrix (Fin n) (Fin n) ℝ => minor y A B) = fun _ => 0 :=
      funext fun y => minor_of_card_ne h
    rw [he]
    exact contDiff_const

theorem contMDiff_minorG (A B : Finset (Fin n)) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (minorG A B) :=
  contMDiff_of_contDiffOn (ψ := fun y => ((minor y A B : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_minor A B)).contDiffOn fun _ => rfl

/-- Cauchy–Binet for the minor functions. -/
theorem minorG_mul {A B : Finset (Fin n)} (hB : B.card = A.card)
    (g h : Langlands.GeneralLinear n ℝ) :
    minorG A B (g * h) = ∑ D ∈ powersetCard A.card univ, minorG A D g * minorG D B h := by
  unfold minorG
  rw [Units.val_mul, minor_mul _ _ rfl hB]
  push_cast
  rfl

theorem minorG_of_card_ne {A B : Finset (Fin n)} (h : A.card ≠ B.card) : minorG A B = 0 := by
  funext g
  simp [minorG, minor_of_card_ne h]

/-! ## Bottom segments and upper triangular matrices -/

/-- `R` is closed upwards: it is a bottom segment of positions. -/
def IsBottom (R : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, i ≤ j → i ∈ R → j ∈ R

theorem minor_upper_eq_zero {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    {R D : Finset (Fin n)} (hR : IsBottom R) (hD : D.card = R.card) (hne : D ≠ R) :
    minor b R D = 0 := by
  obtain ⟨j, hjD, hjR⟩ : ∃ j ∈ D, j ∉ R := by
    by_contra hcon
    push Not at hcon
    exact hne (Finset.eq_of_subset_of_card_le hcon hD.ge)
  rw [minor_eq rfl hD]
  have hr : j ∈ Set.range (D.orderEmbOfFin hD) := by
    rw [range_orderEmbOfFin]
    exact hjD
  obtain ⟨c, hc⟩ := hr
  apply Matrix.det_eq_zero_of_column_eq_zero c
  intro r
  rw [Matrix.submatrix_apply, hc]
  have hlt : j < R.orderEmbOfFin rfl r := by
    by_contra hle
    exact hjR (hR _ _ (not_lt.mp hle) (orderEmbOfFin_mem _ _ _))
  exact hb hlt

/-- For `b` upper triangular and `R` a bottom segment, `det (b g)_{R,C} = ∏_{i ∈ R} b_ii ·
det g_{R,C}`. -/
theorem minor_upper_mul {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    {R : Finset (Fin n)} (hR : IsBottom R) (g : Matrix (Fin n) (Fin n) ℝ) (C : Finset (Fin n)) :
    minor (b * g) R C = (∏ i ∈ R, b i i) * minor g R C := by
  by_cases hC : C.card = R.card
  · rw [minor_mul b g rfl hC, Finset.sum_eq_single R]
    · rw [minor_of_isUpperTriangular hb]
    · intro D hD hne
      rw [minor_upper_eq_zero hb hR (mem_powersetCard.mp hD).2 hne, zero_mul]
    · intro h
      exact absurd (mem_powersetCard.mpr ⟨subset_univ _, rfl⟩) h
  · rw [minor_of_card_ne (Ne.symm hC), minor_of_card_ne (Ne.symm hC), mul_zero]

theorem minorG_borel_mul {R : Finset (Fin n)} (hR : IsBottom R) (C : Finset (Fin n))
    (a : Fin n → ℝˣ) (u : upperUnipotent n ℝ) (g : Langlands.GeneralLinear n ℝ) :
    minorG R C ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * g) =
      (∏ i ∈ R, ((a i : ℝ) : ℂ)) * minorG R C g := by
  unfold minorG
  have hb : (Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)).IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).mul u.property.1
  rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val, minor_upper_mul hb hR]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.diagonal_mul, u.property.2 i, mul_one]

/-! ## `O(n)`-finiteness -/

theorem minorG_mem_kFiniteVectors (A B : Finset (Fin n)) :
    minorG A B ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) := by
  by_cases hB : B.card = A.card
  · rw [mem_kFiniteVectors_iff]
    have hfin : FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun D : Finset (Fin n) => minorG A D)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun D : Finset (Fin n) => minorG A D))
      (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    have heq : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (minorG A B) =
        ∑ D ∈ powersetCard A.card univ, minorG D B (k : Langlands.GeneralLinear n ℝ) •
          minorG A D := by
      funext g
      rw [Finset.sum_apply]
      change minorG A B (g * (k : Langlands.GeneralLinear n ℝ)) = _
      rw [minorG_mul hB]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [SetLike.mem_coe]
    beta_reduce
    rw [heq]
    exact Submodule.sum_mem _ fun D _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨D, rfl⟩)
  · rw [minorG_of_card_ne (Ne.symm hB)]
    exact Submodule.zero_mem _

/-- Products of `O(n)`-finite functions are `O(n)`-finite. -/
theorem mul_mem_kFiniteVectors {f h : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (hh : h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    f * h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) := by
  rw [mem_kFiniteVectors_iff] at hf hh ⊢
  set S₁ := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ) f)
  set S₂ := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ) h)
  have hfg : (S₁ * S₂).FG :=
    ((Submodule.fg_iff_finiteDimensional S₁).2 hf).mul
      ((Submodule.fg_iff_finiteDimensional S₂).2 hh)
  have : FiniteDimensional ℂ (S₁ * S₂) := (Submodule.fg_iff_finiteDimensional _).1 hfg
  refine Submodule.finiteDimensional_of_le (S₂ := S₁ * S₂) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)

/-- Products of functions on `O(n)` with finite-dimensional spans of right translates. -/
theorem finiteDimensional_translateSpan_mul {φ ψ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))))
    (hψ : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => ψ (x * k)))) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k) * ψ (x * k))) := by
  set S₁ := Submodule.span ℂ
    (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))
  set S₂ := Submodule.span ℂ
    (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => ψ (x * k))
  have hfg : (S₁ * S₂).FG :=
    ((Submodule.fg_iff_finiteDimensional S₁).2 hφ).mul
      ((Submodule.fg_iff_finiteDimensional S₂).2 hψ)
  have : FiniteDimensional ℂ (S₁ * S₂) := (Submodule.fg_iff_finiteDimensional _).1 hfg
  refine Submodule.finiteDimensional_of_le (S₂ := S₁ * S₂) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)

/-- The restriction to `O(n)` of an `O(n)`-finite function has a finite-dimensional span of
right translates. -/
theorem finiteDimensional_restrict {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
        fun x => f (Unitary.toUnits (x * k)))) := by
  rw [mem_kFiniteVectors_iff] at hfK
  let Φ : (Langlands.GeneralLinear n ℝ → ℂ) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun x => Unitary.toUnits x)
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => f (Unitary.toUnits (x * k))) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) f)).map Φ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩, ?_⟩
    funext x
    show f (Unitary.toUnits x * Unitary.toUnits k) = f (Unitary.toUnits (x * k))
    rw [map_mul]
  exact Submodule.finiteDimensional_of_le hle

/-! ## Right derivatives of minors -/

/-- Right derivatives of `Δ_{R,C}` are combinations of the `Δ_{R,D}` (Cauchy–Binet). -/
theorem rightDerivative_minorG {R C : Finset (Fin n)} (hC : C.card = R.card)
    (X : Matrix (Fin n) (Fin n) ℝ) (g : Langlands.GeneralLinear n ℝ) :
    rightDerivative (matrixModel ℝ n) X (minorG R C) g =
      ∑ D ∈ powersetCard R.card univ,
        rightDerivative (matrixModel ℝ n) X (minorG D C) 1 * minorG R D g := by
  have h1 := hasDerivAt_mul_matrixExpUnit_smul ((contMDiff_minorG R C).of_le (mod_cast le_top))
    g X
  have h2 : HasDerivAt (fun s : ℝ => ∑ D ∈ powersetCard R.card univ,
      minorG R D g * minorG D C (1 * matrixExpUnit n (s • X)))
      (∑ D ∈ powersetCard R.card univ,
        minorG R D g * rightDerivative (matrixModel ℝ n) X (minorG D C) 1) 0 :=
    HasDerivAt.fun_sum fun D _ => (hasDerivAt_mul_matrixExpUnit_smul
      ((contMDiff_minorG D C).of_le (mod_cast le_top)) 1 X).const_mul _
  have heq : (fun s : ℝ => minorG R C (g * matrixExpUnit n (s • X))) = fun s =>
      ∑ D ∈ powersetCard R.card univ, minorG R D g * minorG D C (1 * matrixExpUnit n (s • X)) := by
    funext s
    rw [one_mul, minorG_mul hC]
  rw [heq] at h1
  rw [h1.unique h2]
  exact Finset.sum_congr rfl fun D _ => mul_comm _ _

/-! ## The shifted spherical list -/

variable (n) (ds : List RealBlock)

/-- The shifted exponents `e_i - [i ∈ R]`. -/
def shiftExp (R : Finset (Fin n)) (i : Fin n) : ℂ :=
  realPositionExponent ds i - if i ∈ R then 1 else 0

/-- The list of even characters `|·|^(e_i - [i ∈ R])`. -/
def sphList (R : Finset (Fin n)) : List RealCharacterData :=
  List.ofFn fun i : Fin n => RealJacquetFrobenius.charData 0 (shiftExp n ds R i)

/-- The shifted spherical list as real blocks. -/
abbrev sphBlocks (R : Finset (Fin n)) : List RealBlock :=
  (sphList n ds R).map RealBlock.character

variable {n ds}

theorem sphList_length (R : Finset (Fin n)) : (sphList n ds R).length = n :=
  List.length_ofFn

theorem sphList_parity (R : Finset (Fin n)) : ∀ d ∈ sphList n ds R, d.parity = 0 := by
  intro d hd
  rw [sphList, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  rfl

theorem isPrincipal_map_character : ∀ cs : List RealCharacterData,
    IsPrincipal (cs.map RealBlock.character)
  | [] => fun p d hd => by simp [realInducedBlockAt] at hd
  | c :: cs => fun p d hd => by
      cases p with
      | zero => simp [realInducedBlockAt] at hd
      | succ p =>
          exact isPrincipal_map_character cs p d (by simpa [realInducedBlockAt] using hd)

theorem sphChar_apply (R : Finset (Fin n)) (i : Fin n) (x : ℝˣ) :
    realPositionCharacter (sphBlocks n ds R) i x =
      ((|(x : ℝ)| : ℝ) : ℂ) ^ shiftExp n ds R i := by
  rw [RealJacquetFrobenius.realPositionCharacter_map_character _ i
    (by rw [sphList_length]; exact i.2) x]
  simp [sphList, RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun]

theorem signReal_mul_abs (x : ℝ) : signReal x * |x| = x := by
  unfold signReal
  split_ifs with h
  · rw [one_mul, abs_of_pos h]
  · rw [abs_of_nonpos (not_lt.mp h)]
    ring

/-- The character of `ds` at position `i` is the shifted spherical character times the
coordinate character `x` on the odd positions. -/
theorem posChar_eq (i : Fin n) (x : ℝˣ) :
    realPositionCharacter ds i x =
      realPositionCharacter (sphBlocks n ds (signSet n ds)) i x *
        (if i ∈ signSet n ds then ((x : ℝ) : ℂ) else 1) := by
  rw [(isSignedPower ds).eq i x, char_signUnit (isSignedPower ds).one (sign_eq n ds) i x,
    sphChar_apply, shiftExp]
  have hx0 : ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr x.ne_zero)
  split_ifs with h
  · rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    have hx : ((x : ℝ) : ℂ) = ((signReal (x : ℝ) : ℝ) : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, signReal_mul_abs]
    rw [hx]
    field_simp
  · simp

theorem principalSeriesCharacter_eq_mul (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter ds) a =
      principalSeriesCharacter ℝ n (realPositionCharacter (sphBlocks n ds (signSet n ds))) a *
        ∏ i ∈ signSet n ds, ((a i : ℝ) : ℂ) := by
  have h : ∏ i ∈ signSet n ds, ((a i : ℝ) : ℂ) =
      ∏ i, if i ∈ signSet n ds then ((a i : ℝ) : ℂ) else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  unfold principalSeriesCharacter
  rw [h, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [posChar_eq]
  ring

theorem sphChar_sign (R : Finset (Fin n)) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter (sphBlocks n ds R))
      (fun i => signUnit (a i)) = 1 := by
  rw [JacquetKernel.principalSeriesCharacter_sign]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [sphChar_apply, abs_signUnit]
  simp

/-! ## Multiplication by `Δ_{R,C}` -/

theorem mem_KF_iff (hds : IsPrincipal ds) (f : Langlands.GeneralLinear n ℝ → ℂ) :
    f ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) ↔
      f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n) := by
  rw [realStandardModule_eq hds]

theorem mul_minorG_mem (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds)) (C : Finset (Fin n))
    {h : Langlands.GeneralLinear n ℝ → ℂ}
    (hh : h ∈ kFiniteFunctions (realStandardModule n (sphBlocks n ds (signSet n ds)))
      (unitaryCompact ℝ n)) :
    (fun g => h g * minorG (signSet n ds) C g) ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) := by
  rw [mem_KF_iff (isPrincipal_map_character _)] at hh
  rw [mem_KF_iff hds]
  refine ⟨⟨RealPrincipalSeriesDuality.contMDiff_mul_fun hh.1.1 (contMDiff_minorG _ _),
    fun a u g => ?_⟩, mul_mem_kFiniteVectors hh.2 (minorG_mem_kFiniteVectors _ _)⟩
  change h _ * minorG _ C _ = _ * (h g * minorG _ C g)
  rw [hh.1.2 a u g, minorG_borel_mul hR, principalSeriesCharacter_eq_mul (ds := ds) a]
  ring

/-- Multiplication by `Δ_{R,C}` from the shifted spherical module to the module of `ds`. -/
def mulMinor (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds)) (C : Finset (Fin n)) :
    KF n (sphBlocks n ds (signSet n ds)) →ₗ[ℂ] KF n ds where
  toFun h := ⟨fun g => h.1 g * minorG (signSet n ds) C g, mul_minorG_mem hds hR C h.2⟩
  map_add' h₁ h₂ := by
    apply Subtype.ext
    funext g
    change (h₁.1 g + h₂.1 g) * _ = h₁.1 g * _ + h₂.1 g * _
    ring
  map_smul' c h := by
    apply Subtype.ext
    funext g
    change (c * h.1 g) * _ = c * (h.1 g * _)
    ring

theorem mulMinor_coe (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds)) (C : Finset (Fin n))
    (h : KF n (sphBlocks n ds (signSet n ds))) (g : Langlands.GeneralLinear n ℝ) :
    ((mulMinor hds hR C h : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) g =
      (h : Langlands.GeneralLinear n ℝ → ℂ) g * minorG (signSet n ds) C g :=
  rfl

theorem mulMinor_of_card_ne (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds))
    {C : Finset (Fin n)} (hC : C.card ≠ (signSet n ds).card)
    (h : KF n (sphBlocks n ds (signSet n ds))) : mulMinor hds hR C h = 0 := by
  apply Subtype.ext
  funext g
  rw [mulMinor_coe, minorG_of_card_ne (Ne.symm hC)]
  simp

/-- The product rule: `Δ_C · R(X) h = R(X)(Δ_C h) - ∑_D c_D Δ_D h`. -/
theorem mulMinor_lie (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds)) {C : Finset (Fin n)}
    (hC : C.card = (signSet n ds).card) (X : Matrix (Fin n) (Fin n) ℝ)
    (h : KF n (sphBlocks n ds (signSet n ds))) :
    mulMinor hds hR C (realStandardLie n (sphBlocks n ds (signSet n ds)) (1 ⊗ₜ X) h) =
      realStandardLie n ds (1 ⊗ₜ X) (mulMinor hds hR C h) -
        ∑ D ∈ powersetCard (signSet n ds).card univ,
          rightDerivative (matrixModel ℝ n) X (minorG D C) 1 • mulMinor hds hR D h := by
  apply Subtype.ext
  funext g
  rw [mulMinor_coe, Submodule.coe_sub, Pi.sub_apply, realStandardLie_one_tmul_apply_coe,
    realStandardLie_one_tmul_apply_coe, Submodule.coe_sum, Finset.sum_apply]
  have hh : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (h : Langlands.GeneralLinear n ℝ → ℂ) :=
    contMDiff_of_mem_realStandardModule h.2.1
  change _ = rightDerivative (matrixModel ℝ n) X
    (fun g => (h : Langlands.GeneralLinear n ℝ → ℂ) g * minorG (signSet n ds) C g) g - _
  rw [RealPrincipalSeriesDuality.rightDerivative_mul_fun hh (contMDiff_minorG _ _),
    rightDerivative_minorG hC, Finset.mul_sum]
  have hs : ∀ D ∈ powersetCard (signSet n ds).card univ,
      ((rightDerivative (matrixModel ℝ n) X (minorG D C) 1 • mulMinor hds hR D h : KF n ds) :
        Langlands.GeneralLinear n ℝ → ℂ) g =
        (h : Langlands.GeneralLinear n ℝ → ℂ) g *
          (rightDerivative (matrixModel ℝ n) X (minorG D C) 1 * minorG (signSet n ds) D g) := by
    intro D _
    rw [Submodule.coe_smul, Pi.smul_apply, mulMinor_coe, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hs]
  ring

/-! ## The pulled-back subspace -/

/-- The functions `h` of the shifted spherical module with `Δ_C h ∈ W` for every `C`. -/
def pullback (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds))
    (W : Submodule ℂ (KF n ds)) : Submodule ℂ (KF n (sphBlocks n ds (signSet n ds))) :=
  ⨅ C : Finset (Fin n), W.comap (mulMinor hds hR C)

theorem mem_pullback (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds))
    {W : Submodule ℂ (KF n ds)} {h : KF n (sphBlocks n ds (signSet n ds))} :
    h ∈ pullback hds hR W ↔ ∀ C : Finset (Fin n), mulMinor hds hR C h ∈ W := by
  simp only [pullback, Submodule.mem_iInf, Submodule.mem_comap]

theorem pullback_lie (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds))
    {W : Submodule ℂ (KF n ds)}
    (hW : ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ W, realStandardLie n ds Z v ∈ W)
    (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) {h : KF n (sphBlocks n ds (signSet n ds))}
    (hh : h ∈ pullback hds hR W) :
    realStandardLie n (sphBlocks n ds (signSet n ds)) Z h ∈ pullback hds hR W := by
  induction Z with
  | tmul z X =>
      have h1 : realStandardLie n (sphBlocks n ds (signSet n ds)) (z ⊗ₜ X) =
          z • realStandardLie n (sphBlocks n ds (signSet n ds)) (1 ⊗ₜ X) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, LinearMap.smul_apply]
      refine Submodule.smul_mem _ z ?_
      rw [mem_pullback] at hh ⊢
      intro C
      by_cases hC : C.card = (signSet n ds).card
      · rw [mulMinor_lie hds hR hC]
        refine Submodule.sub_mem _ (hW _ _ (hh C)) (Submodule.sum_mem _ fun D _ => ?_)
        exact Submodule.smul_mem _ _ (hh D)
      · rw [mulMinor_of_card_ne hds hR hC]
        exact Submodule.zero_mem _
  | add Z₁ Z₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂

/-! ## The `O(n)`-fixed vector -/

theorem const_finiteDimensional :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
        fun x => (fun _ : Matrix.unitaryGroup (Fin n) ℝ => (1 : ℂ)) (x * k))) := by
  have : (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => (fun _ : Matrix.unitaryGroup (Fin n) ℝ => (1 : ℂ)) (x * k)) ⊆
      {fun _ => (1 : ℂ)} := by
    rintro _ ⟨k, rfl⟩
    rfl
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono this)

theorem const_signDiagonal (R : Finset (Fin n)) (a : Fin n → ℝˣ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    (fun _ : Matrix.unitaryGroup (Fin n) ℝ => (1 : ℂ)) (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n (realPositionCharacter (sphBlocks n ds R))
        (fun i => signUnit (a i)) * (fun _ : Matrix.unitaryGroup (Fin n) ℝ => (1 : ℂ)) κ := by
  rw [sphChar_sign, one_mul]

theorem sphVec_mem (R : Finset (Fin n)) :
    extension (shiftedExponent n (realPositionExponent (sphBlocks n ds R)))
        (fun _ : Matrix.unitaryGroup (Fin n) ℝ => (1 : ℂ)) ∈
      kFiniteFunctions (realStandardModule n (sphBlocks n ds R)) (unitaryCompact ℝ n) := by
  rw [mem_KF_iff (isPrincipal_map_character _)]
  exact extension_mem_kFiniteFunctions _ (isSignedPower _).eq continuous_const
    const_finiteDimensional (const_signDiagonal R)

/-- The `O(n)`-fixed vector of the shifted spherical module, equal to `1` on `O(n)`. -/
def sphVec (R : Finset (Fin n)) : KF n (sphBlocks n ds R) :=
  ⟨_, sphVec_mem R⟩

theorem sphVec_coe (R : Finset (Fin n)) :
    ((sphVec R : KF n (sphBlocks n ds R)) : Langlands.GeneralLinear n ℝ → ℂ) =
      extension (shiftedExponent n (realPositionExponent (sphBlocks n ds R)))
        (fun _ : Matrix.unitaryGroup (Fin n) ℝ => (1 : ℂ)) :=
  rfl

theorem sphVec_unitary (R : Finset (Fin n)) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    ((sphVec R : KF n (sphBlocks n ds R)) : Langlands.GeneralLinear n ℝ → ℂ)
      (Unitary.toUnits κ) = 1 := by
  rw [sphVec_coe]
  exact extension_unitary _ _ κ

theorem sphVec_fixed (R : Finset (Fin n)) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    realStandardRep n (sphBlocks n ds R) k (sphVec R) = sphVec R := by
  apply Subtype.ext
  rw [realStandardRep_apply_coe]
  exact rightTranslation_extension _ (isSignedPower _).eq continuous_const
    const_finiteDimensional (const_signDiagonal R) k

theorem sphVec_ne_zero (R : Finset (Fin n)) : sphVec (ds := ds) R ≠ 0 := by
  intro h
  have h1 := sphVec_unitary (ds := ds) R 1
  rw [h] at h1
  exact one_ne_zero h1.symm

theorem mulMinor_sphVec (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds))
    {C : Finset (Fin n)} (hC : C.card = (signSet n ds).card) :
    mulMinor hds hR C (sphVec (signSet n ds)) = vec hds C := by
  apply Subtype.ext
  have h₁ := (mem_KF_iff hds _).mp (mulMinor hds hR C (sphVec (signSet n ds))).2
  have h₂ := (mem_KF_iff hds _).mp (vec hds C).2
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries h₁.1 h₂.1 fun k hk => ?_
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  rw [mulMinor_coe, vec_coe hds hC, minorVector_of_mem hk, hku, sphVec_unitary, one_mul]
  rfl

/-! ## Spanning -/

theorem continuous_restrict {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f) :
    Continuous fun κ : Matrix.unitaryGroup (Fin n) ℝ => f (Unitary.toUnits κ) :=
  hf.comp continuous_unitary_toUnits

theorem psc_sign_sq (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) *
      principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) = 1 := by
  rw [JacquetKernel.principalSeriesCharacter_sign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [char_signUnit (isSignedPower ds).one (sign_eq n ds) i (a i)]
  split_ifs
  · unfold signReal
    split_ifs <;> norm_num
  · ring

/-- The function `κ ↦ f(κ) Δ_{R,C}(κ)` on `O(n)`. -/
def coef (f : Langlands.GeneralLinear n ℝ → ℂ) (R C : Finset (Fin n))
    (κ : Matrix.unitaryGroup (Fin n) ℝ) : ℂ :=
  f (Unitary.toUnits κ) * minorFun n R C κ

theorem coef_signDiagonal (f : KF n ds) (C : Finset (Fin n)) (a : Fin n → ℝˣ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    coef (f : Langlands.GeneralLinear n ℝ → ℂ) (signSet n ds) C
        (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n (realPositionCharacter (sphBlocks n ds (signSet n ds)))
        (fun i => signUnit (a i)) *
        coef (f : Langlands.GeneralLinear n ℝ → ℂ) (signSet n ds) C κ := by
  have hu : Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ) =
      (Iwasawa.diagonalUnits (fun i => signUnit (a i)) : Langlands.GeneralLinear n ℝ) *
        ((1 : upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) * Unitary.toUnits κ := by
    rw [map_mul, OneMemClass.coe_one, mul_one]
    congr 1
    apply Units.ext
    change (Matrix.diagonal fun i => signReal (a i : ℝ)) = _
    rw [Iwasawa.diagonalUnits_val]
    congr 1
    funext i
    rw [signUnit_val]
  unfold coef
  rw [hu, (realStandardModule_le_principalSeries n ds f.2.1).2,
    minorFun_signDiagonal (isSignedPower ds).one (sign_eq n ds), sphChar_sign]
  have := psc_sign_sq (ds := ds) a
  linear_combination ((f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits κ) *
    minorFun n (signSet n ds) C κ) * this

theorem minorFun_of_card_ne {R C : Finset (Fin n)} (hC : C.card ≠ R.card) :
    minorFun n R C = 0 := by
  funext κ
  simp [minorFun, minor_of_card_ne (Ne.symm hC)]

/-- The right translates of any minor function on `O(n)` span a finite-dimensional space. -/
theorem finiteDimensional_minorFun_any (R C : Finset (Fin n)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => minorFun n R C (x * k))) := by
  by_cases hC : C.card = R.card
  · exact finiteDimensional_minorFun hC
  · have hsub : (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
        fun x => minorFun n R C (x * k)) ⊆ {0} := by
      rintro _ ⟨k, rfl⟩
      rw [Set.mem_singleton_iff, minorFun_of_card_ne hC]
      rfl
    exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

theorem continuous_coef {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f)
    (R C : Finset (Fin n)) : Continuous (coef f R C) :=
  (continuous_restrict hf).mul (continuous_minorFun _ _)

theorem finiteDimensional_coef {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) (R C : Finset (Fin n)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => coef f R C (x * k))) :=
  finiteDimensional_translateSpan_mul (φ := fun y => f (Unitary.toUnits y))
    (ψ := minorFun n R C) (finiteDimensional_restrict hfK) (finiteDimensional_minorFun_any R C)

theorem coef_mem (f : KF n ds) (C : Finset (Fin n)) :
    extension (shiftedExponent n (realPositionExponent (sphBlocks n ds (signSet n ds))))
        (coef (f : Langlands.GeneralLinear n ℝ → ℂ) (signSet n ds) C) ∈
      kFiniteFunctions (realStandardModule n (sphBlocks n ds (signSet n ds)))
        (unitaryCompact ℝ n) := by
  rw [mem_KF_iff (isPrincipal_map_character _)]
  have hfc : Continuous (f : Langlands.GeneralLinear n ℝ → ℂ) :=
    (contMDiff_of_mem_realStandardModule f.2.1).continuous
  exact extension_mem_kFiniteFunctions _ (isSignedPower _).eq
    (continuous_coef hfc _ _) (finiteDimensional_coef f.2.2 _ _) (coef_signDiagonal f C)

/-- The coefficient of `Δ_{R,C}` in the expansion of `f`. -/
def coefVec (f : KF n ds) (C : Finset (Fin n)) :
    KF n (sphBlocks n ds (signSet n ds)) :=
  ⟨_, coef_mem f C⟩

theorem coefVec_coe (f : KF n ds) (C : Finset (Fin n)) :
    ((coefVec f C : KF n (sphBlocks n ds (signSet n ds))) :
      Langlands.GeneralLinear n ℝ → ℂ) =
      extension (shiftedExponent n (realPositionExponent (sphBlocks n ds (signSet n ds))))
        (coef (f : Langlands.GeneralLinear n ℝ → ℂ) (signSet n ds) C) :=
  rfl

theorem sum_minor_sq (κ : Matrix.unitaryGroup (Fin n) ℝ) (R : Finset (Fin n)) :
    ∑ C ∈ powersetCard R.card univ,
      minor (κ : Matrix (Fin n) (Fin n) ℝ) R C * minor (κ : Matrix (Fin n) (Fin n) ℝ) R C = 1 := by
  have hκ : (κ : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp κ.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h := minor_mul (κ : Matrix (Fin n) (Fin n) ℝ) (κ : Matrix (Fin n) (Fin n) ℝ)ᵀ
    (A := R) (B := R) rfl rfl
  rw [hκ, minor_one, ite_eq_left rfl] at h
  rw [h]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [minor_transpose]

/-- **Spanning.** Every `f` is `∑_C Δ_{R,C} h_C`. -/
theorem sum_mulMinor_coefVec (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds)) (f : KF n ds) :
    ∑ C ∈ powersetCard (signSet n ds).card univ, mulMinor hds hR C (coefVec f C) = f := by
  apply Subtype.ext
  have h₁ := (mem_KF_iff hds _).mp
    (∑ C ∈ powersetCard (signSet n ds).card univ, mulMinor hds hR C (coefVec f C)).2
  have h₂ := (mem_KF_iff hds _).mp f.2
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries h₁.1 h₂.1 fun k hk => ?_
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  rw [Submodule.coe_sum, Finset.sum_apply]
  have hs : ∀ C ∈ powersetCard (signSet n ds).card univ,
      ((mulMinor hds hR C (coefVec f C) : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) k =
        (f : Langlands.GeneralLinear n ℝ → ℂ) k *
          (((minor (k : Matrix (Fin n) (Fin n) ℝ) (signSet n ds) C *
            minor (k : Matrix (Fin n) (Fin n) ℝ) (signSet n ds) C : ℝ)) : ℂ) := by
    intro C _
    rw [mulMinor_coe]
    rw [coefVec_coe, hku, extension_unitary, coef]
    have e : ((Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) : Langlands.GeneralLinear n ℝ) :
          Matrix (Fin n) (Fin n) ℝ) = k := rfl
    unfold minorFun minorG
    rw [e]
    push_cast
    ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum]
  have h1 := sum_minor_sq (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ : Matrix.unitaryGroup (Fin n) ℝ)
    (signSet n ds)
  have h2 : ∑ C ∈ powersetCard (signSet n ds).card univ,
      (((minor (k : Matrix (Fin n) (Fin n) ℝ) (signSet n ds) C *
        minor (k : Matrix (Fin n) (Fin n) ℝ) (signSet n ds) C : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum]
    exact_mod_cast h1
  rw [h2, mul_one]

/-! ## The reduction -/

/-- **Product reduction (Wallach 1971, Theorem 3.2).** If the `O(n)`-fixed vector of the
shifted spherical module is cyclic under the Lie algebra, every Lie-stable subspace of `KF n ds`
containing all minor vectors `φ_{R,C}` is everything. -/
theorem eq_top_of_sphCyclic (hds : IsPrincipal ds) (hR : IsBottom (signSet n ds))
    (hcyc : ∀ W' : Submodule ℂ (KF n (sphBlocks n ds (signSet n ds))),
      sphVec (signSet n ds) ∈ W' →
      (∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ w ∈ W',
        realStandardLie n (sphBlocks n ds (signSet n ds)) Z w ∈ W') → W' = ⊤)
    (W : Submodule ℂ (KF n ds))
    (hWL : ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ W, realStandardLie n ds Z v ∈ W)
    (hvec : ∀ B : Finset (Fin n), B.card = (signSet n ds).card → vec hds B ∈ W) : W = ⊤ := by
  have htop : pullback hds hR W = ⊤ := by
    refine hcyc _ ?_ fun Z w hw => pullback_lie hds hR hWL Z hw
    rw [mem_pullback]
    intro C
    by_cases hC : C.card = (signSet n ds).card
    · rw [mulMinor_sphVec hds hR hC]
      exact hvec C hC
    · rw [mulMinor_of_card_ne hds hR hC]
      exact Submodule.zero_mem _
  rw [eq_top_iff]
  intro f _
  rw [← sum_mulMinor_coefVec hds hR f]
  refine Submodule.sum_mem _ fun C _ => ?_
  have hC : coefVec f C ∈ pullback hds hR W := htop ▸ Submodule.mem_top
  exact (mem_pullback hds hR).mp hC C

end RealTiedMinorProduct

end Langlands.Archimedean
