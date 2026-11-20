import Langlands.Representation.Archimedean.RealTiedMinorProduct

/-!
# Lie cyclicity through products of bottom minors

Let `ps` and `qs` be lists of real blocks without discrete-series blocks, and let
`R₀, …, R_{N-1}` be bottom segments of positions such that the principal-series character of
`qs` is that of `ps` times `a ↦ ∏_j ∏_{i ∈ R_j} a_i`. Multiplication by a product of minors
`g ↦ ∏_j det g_{R_j, C_j}` maps the `O(n)`-finite functions of `ps` to those of `qs`. If a vector
`T` generates the module of `ps` under the Lie algebra, then the products `T · ∏_j Δ_{R_j,C_j}`
generate the module of `qs` under the Lie algebra. This generalizes the single-minor argument of
`RealTiedMinorProduct.eq_top_of_sphCyclic` (after Wallach 1971, Theorem 3.2).
-/

noncomputable section

open Matrix Finset

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDiscreteMinorCyclic

open MatrixMinor JacquetMinor GramFormula PrincipalSeriesExtension
  RealTemperedCommutantReduction RealStrictCharacterLanglandsQuotient RealTiedMinorScalar
  RealTiedMinorProduct

variable {n N : ℕ}

/-! ## Products of minors -/

/-- The product `g ↦ ∏_j det g_{R_j, C_j}`. -/
def prodG (R C : Fin N → Finset (Fin n)) : Langlands.GeneralLinear n ℝ → ℂ :=
  ∏ j, minorG (R j) (C j)

theorem prodG_apply (R C : Fin N → Finset (Fin n)) (g : Langlands.GeneralLinear n ℝ) :
    prodG R C g = ∏ j, minorG (R j) (C j) g := by
  rw [prodG, Finset.prod_apply]

theorem contMDiff_prodG (R C : Fin N → Finset (Fin n)) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (prodG R C) := by
  unfold prodG
  exact Finset.prod_induction _ (fun f => ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (fun f h hf hh => RealPrincipalSeriesDuality.contMDiff_mul_fun hf hh) contMDiff_const
    fun j _ => contMDiff_minorG _ _

theorem one_mem_kFiniteVectors :
    (1 : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
        (unitaryCompact ℝ n) := by
  rw [mem_kFiniteVectors_iff]
  have hsub : (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
        (1 : Langlands.GeneralLinear n ℝ → ℂ)) ⊆ {1} := by
    rintro _ ⟨k, rfl⟩
    rfl
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

theorem prodG_mem_kFiniteVectors (R C : Fin N → Finset (Fin n)) :
    prodG R C ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) := by
  unfold prodG
  refine Finset.prod_induction _ (fun f => f ∈ kFiniteVectors
    (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)) (unitaryCompact ℝ n))
    (fun f h hf hh => mul_mem_kFiniteVectors hf hh) one_mem_kFiniteVectors
    fun j _ => minorG_mem_kFiniteVectors _ _

/-- The weight `a ↦ ∏_j ∏_{i ∈ R_j} a_i` of a product of bottom minors. -/
def rowWeight (R : Fin N → Finset (Fin n)) (a : Fin n → ℝˣ) : ℂ :=
  ∏ j, ∏ i ∈ R j, ((a i : ℝ) : ℂ)

theorem prodG_borel_mul {R : Fin N → Finset (Fin n)} (hR : ∀ j, IsBottom (R j))
    (C : Fin N → Finset (Fin n)) (a : Fin n → ℝˣ) (u : upperUnipotent n ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    prodG R C ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * g) = rowWeight R a * prodG R C g := by
  rw [prodG_apply, prodG_apply, rowWeight, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => minorG_borel_mul (hR j) (C j) a u g

theorem signUnit_sq (x : ℝˣ) :
    ((signUnit x : ℝ) : ℂ) * ((signUnit x : ℝ) : ℂ) = 1 := by
  rw [signUnit_val]
  unfold signReal
  split_ifs <;> norm_num

theorem rowWeight_sign_sq (R : Fin N → Finset (Fin n)) (a : Fin n → ℝˣ) :
    rowWeight R (fun i => signUnit (a i)) * rowWeight R (fun i => signUnit (a i)) = 1 := by
  unfold rowWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => signUnit_sq (a i)

/-! ## Right derivatives of products of minors -/

theorem rightDerivative_const (c : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    rightDerivative (matrixModel ℝ n) X (fun _ : Langlands.GeneralLinear n ℝ => c) = 0 := by
  funext g
  simp [rightDerivative, mfderiv_const]

theorem rightDerivative_minorG_mem (R C : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) :
    rightDerivative (matrixModel ℝ n) X (minorG R C) ∈
      Submodule.span ℂ (Set.range (minorG (n := n) R)) := by
  by_cases hC : C.card = R.card
  · have h : rightDerivative (matrixModel ℝ n) X (minorG R C) =
        ∑ D ∈ powersetCard R.card univ,
          rightDerivative (matrixModel ℝ n) X (minorG D C) 1 • minorG R D := by
      funext g
      rw [rightDerivative_minorG hC, Finset.sum_apply]
      rfl
    rw [h]
    exact Submodule.sum_mem _ fun D _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨D, rfl⟩)
  · rw [minorG_of_card_ne (Ne.symm hC)]
    have : (0 : Langlands.GeneralLinear n ℝ → ℂ) = fun _ => 0 := rfl
    rw [this, rightDerivative_const]
    exact Submodule.zero_mem _

/-- Right derivatives of products of minors are combinations of products of minors with the
same rows. -/
theorem rightDerivative_prodG_mem (X : Matrix (Fin n) (Fin n) ℝ) :
    ∀ {N : ℕ} (R C : Fin N → Finset (Fin n)),
      rightDerivative (matrixModel ℝ n) X (prodG R C) ∈
        Submodule.span ℂ (Set.range (prodG R))
  | 0, R, C => by
    have h : prodG R C = fun _ => 1 := by
      funext g
      rw [prodG_apply]
      simp
    rw [h, rightDerivative_const]
    exact Submodule.zero_mem _
  | N + 1, R, C => by
    have hsplit : ∀ C' : Fin (N + 1) → Finset (Fin n),
        prodG R C' = fun g => minorG (R 0) (C' 0) g *
          prodG (fun j => R j.succ) (fun j => C' j.succ) g := by
      intro C'
      funext g
      rw [prodG_apply, prodG_apply, Fin.prod_univ_succ]
    have hle : Submodule.span ℂ (Set.range (minorG (n := n) (R 0))) *
        Submodule.span ℂ (Set.range (prodG (fun j => R j.succ))) ≤
          Submodule.span ℂ (Set.range (prodG R)) := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨D, rfl⟩, _, ⟨C', rfl⟩, rfl⟩
      refine ⟨Fin.cons D C', ?_⟩
      rw [hsplit]
      funext g
      simp only [Fin.cons_zero, Fin.cons_succ, Pi.mul_apply]
    have hm := contMDiff_minorG (R 0) (C 0)
    have hp := contMDiff_prodG (fun j => R j.succ) (fun j => C j.succ)
    have hd : rightDerivative (matrixModel ℝ n) X (prodG R C) =
        rightDerivative (matrixModel ℝ n) X (minorG (R 0) (C 0)) *
            prodG (fun j => R j.succ) (fun j => C j.succ) +
          minorG (R 0) (C 0) *
            rightDerivative (matrixModel ℝ n) X (prodG (fun j => R j.succ) (fun j => C j.succ)) := by
      funext g
      rw [hsplit C, RealPrincipalSeriesDuality.rightDerivative_mul_fun hm hp]
      rfl
    rw [hd]
    refine Submodule.add_mem _ (hle (Submodule.mul_mem_mul (rightDerivative_minorG_mem _ _ X)
      (Submodule.subset_span ⟨_, rfl⟩))) (hle (Submodule.mul_mem_mul
        (Submodule.subset_span ⟨_, rfl⟩) (rightDerivative_prodG_mem X _ _)))

/-! ## The shift hypothesis -/

/-- `qs` is `ps` twisted by the product of the bottom minors with rows `R_j`: both lists have
no discrete-series block, the `R_j` are bottom segments, and the principal-series character of
`qs` is that of `ps` times `a ↦ ∏_j ∏_{i ∈ R_j} a_i`. -/
structure IsMinorShift (n : ℕ) (ps qs : List RealBlock) {N : ℕ} (R : Fin N → Finset (Fin n)) :
    Prop where
  principal_left : IsPrincipal ps
  principal_right : IsPrincipal qs
  bottom : ∀ j, IsBottom (R j)
  char : ∀ a : Fin n → ℝˣ, principalSeriesCharacter ℝ n (realPositionCharacter qs) a =
    principalSeriesCharacter ℝ n (realPositionCharacter ps) a * rowWeight R a

variable {ps qs : List RealBlock} {R : Fin N → Finset (Fin n)}

theorem mul_prodG_mem (hsh : IsMinorShift n ps qs R) (C : Fin N → Finset (Fin n))
    {h : Langlands.GeneralLinear n ℝ → ℂ}
    (hh : h ∈ kFiniteFunctions (realStandardModule n ps) (unitaryCompact ℝ n)) :
    (fun g => h g * prodG R C g) ∈
      kFiniteFunctions (realStandardModule n qs) (unitaryCompact ℝ n) := by
  rw [mem_KF_iff hsh.principal_left] at hh
  rw [mem_KF_iff hsh.principal_right]
  refine ⟨⟨RealPrincipalSeriesDuality.contMDiff_mul_fun hh.1.1 (contMDiff_prodG _ _),
    fun a u g => ?_⟩, mul_mem_kFiniteVectors hh.2 (prodG_mem_kFiniteVectors _ _)⟩
  change h _ * prodG R C _ = _ * (h g * prodG R C g)
  rw [hh.1.2 a u g, prodG_borel_mul hsh.bottom, hsh.char a]
  ring

/-- Multiplication by `∏_j Δ_{R_j, C_j}` from the module of `ps` to the module of `qs`. -/
def mulProd (hsh : IsMinorShift n ps qs R) (C : Fin N → Finset (Fin n)) :
    KF n ps →ₗ[ℂ] KF n qs where
  toFun h := ⟨fun g => h.1 g * prodG R C g, mul_prodG_mem hsh C h.2⟩
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

theorem mulProd_coe (hsh : IsMinorShift n ps qs R) (C : Fin N → Finset (Fin n)) (h : KF n ps)
    (g : Langlands.GeneralLinear n ℝ) :
    ((mulProd hsh C h : KF n qs) : Langlands.GeneralLinear n ℝ → ℂ) g =
      (h : Langlands.GeneralLinear n ℝ → ℂ) g * prodG R C g :=
  rfl

/-- The product rule: `Π_C · R(X) h = R(X)(Π_C h) - h · R(X) Π_C`, and `h · R(X) Π_C` is a
combination of the `Π_D h`. -/
theorem mulProd_lie_mem (hsh : IsMinorShift n ps qs R) (C : Fin N → Finset (Fin n))
    (X : Matrix (Fin n) (Fin n) ℝ) (h : KF n ps) (W : Submodule ℂ (KF n qs))
    (hW : ∀ D, mulProd hsh D h ∈ W)
    (hWL : realStandardLie n qs (1 ⊗ₜ X) (mulProd hsh C h) ∈ W) :
    mulProd hsh C (realStandardLie n ps (1 ⊗ₜ X) h) ∈ W := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (rightDerivative_prodG_mem X R C)
  have hh : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (h : Langlands.GeneralLinear n ℝ → ℂ) :=
    contMDiff_of_mem_realStandardModule h.2.1
  have heq : mulProd hsh C (realStandardLie n ps (1 ⊗ₜ X) h) =
      realStandardLie n qs (1 ⊗ₜ X) (mulProd hsh C h) - ∑ D, c D • mulProd hsh D h := by
    apply Subtype.ext
    funext g
    rw [mulProd_coe, Submodule.coe_sub, Pi.sub_apply, realStandardLie_one_tmul_apply_coe,
      realStandardLie_one_tmul_apply_coe, Submodule.coe_sum, Finset.sum_apply]
    change _ = rightDerivative (matrixModel ℝ n) X
      (fun g => (h : Langlands.GeneralLinear n ℝ → ℂ) g * prodG R C g) g - _
    rw [RealPrincipalSeriesDuality.rightDerivative_mul_fun hh (contMDiff_prodG _ _), ← hc,
      Finset.sum_apply, Finset.mul_sum]
    have hs : ∀ D ∈ (univ : Finset (Fin N → Finset (Fin n))),
        ((c D • mulProd hsh D h : KF n qs) : Langlands.GeneralLinear n ℝ → ℂ) g =
          (h : Langlands.GeneralLinear n ℝ → ℂ) g * (c D • prodG R D) g := by
      intro D _
      rw [Submodule.coe_smul, Pi.smul_apply, mulProd_coe, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hs]
    ring
  rw [heq]
  exact Submodule.sub_mem _ hWL (Submodule.sum_mem _ fun D _ => Submodule.smul_mem _ _ (hW D))

/-! ## The pulled-back subspace -/

/-- The functions `h` of the module of `ps` with `Π_C h ∈ W` for every `C`. -/
def pullback (hsh : IsMinorShift n ps qs R) (W : Submodule ℂ (KF n qs)) :
    Submodule ℂ (KF n ps) :=
  ⨅ C : Fin N → Finset (Fin n), W.comap (mulProd hsh C)

theorem mem_pullback (hsh : IsMinorShift n ps qs R) {W : Submodule ℂ (KF n qs)} {h : KF n ps} :
    h ∈ pullback hsh W ↔ ∀ C, mulProd hsh C h ∈ W := by
  simp only [pullback, Submodule.mem_iInf, Submodule.mem_comap]

theorem pullback_lie (hsh : IsMinorShift n ps qs R) {W : Submodule ℂ (KF n qs)}
    (hW : ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ W, realStandardLie n qs Z v ∈ W)
    (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) {h : KF n ps} (hh : h ∈ pullback hsh W) :
    realStandardLie n ps Z h ∈ pullback hsh W := by
  induction Z with
  | tmul z X =>
      have h1 : realStandardLie n ps (z ⊗ₜ X) = z • realStandardLie n ps (1 ⊗ₜ X) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, LinearMap.smul_apply]
      refine Submodule.smul_mem _ z ?_
      rw [mem_pullback] at hh ⊢
      intro C
      exact mulProd_lie_mem hsh C X h W hh (hW _ _ (hh C))
  | add Z₁ Z₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂

/-! ## Spanning -/

/-- The function `κ ↦ f(κ) ∏_j Δ_{R_j,C_j}(κ)` on `O(n)`. -/
def coefP (R : Fin N → Finset (Fin n)) (f : Langlands.GeneralLinear n ℝ → ℂ)
    (C : Fin N → Finset (Fin n)) (κ : Matrix.unitaryGroup (Fin n) ℝ) : ℂ :=
  f (Unitary.toUnits κ) * prodG R C (Unitary.toUnits κ)

theorem coefP_signDiagonal (hsh : IsMinorShift n ps qs R) (f : KF n qs)
    (C : Fin N → Finset (Fin n)) (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    coefP R (f : Langlands.GeneralLinear n ℝ → ℂ) C (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n (realPositionCharacter ps) (fun i => signUnit (a i)) *
        coefP R (f : Langlands.GeneralLinear n ℝ → ℂ) C κ := by
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
  unfold coefP
  rw [hu, (realStandardModule_le_principalSeries n qs f.2.1).2, prodG_borel_mul hsh.bottom,
    hsh.char]
  have := rowWeight_sign_sq R a
  linear_combination (principalSeriesCharacter ℝ n (realPositionCharacter ps)
    (fun i => signUnit (a i)) * (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits κ) *
      prodG R C (Unitary.toUnits κ)) * this

theorem continuous_coefP (R : Fin N → Finset (Fin n)) {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : Continuous f) (C : Fin N → Finset (Fin n)) : Continuous (coefP R f C) :=
  (continuous_restrict hf).mul (continuous_restrict (contMDiff_prodG R C).continuous)

theorem finiteDimensional_coefP (R : Fin N → Finset (Fin n)) {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) (C : Fin N → Finset (Fin n)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => coefP R f C (x * k))) :=
  finiteDimensional_translateSpan_mul (φ := fun y => f (Unitary.toUnits y))
    (ψ := fun y => prodG R C (Unitary.toUnits y)) (finiteDimensional_restrict hfK)
    (finiteDimensional_restrict (prodG_mem_kFiniteVectors R C))

theorem coefP_mem (hsh : IsMinorShift n ps qs R) (f : KF n qs) (C : Fin N → Finset (Fin n)) :
    extension (shiftedExponent n (realPositionExponent ps))
        (coefP R (f : Langlands.GeneralLinear n ℝ → ℂ) C) ∈
      kFiniteFunctions (realStandardModule n ps) (unitaryCompact ℝ n) := by
  rw [mem_KF_iff hsh.principal_left]
  have hfc : Continuous (f : Langlands.GeneralLinear n ℝ → ℂ) :=
    (contMDiff_of_mem_realStandardModule f.2.1).continuous
  exact extension_mem_kFiniteFunctions _ (isSignedPower ps).eq
    (continuous_coefP R hfc C) (finiteDimensional_coefP R f.2.2 C) (coefP_signDiagonal hsh f C)

/-- The coefficient of `Π_C` in the expansion of `f`. -/
def coefVecP (hsh : IsMinorShift n ps qs R) (f : KF n qs) (C : Fin N → Finset (Fin n)) :
    KF n ps :=
  ⟨_, coefP_mem hsh f C⟩

theorem coefVecP_coe (hsh : IsMinorShift n ps qs R) (f : KF n qs) (C : Fin N → Finset (Fin n)) :
    ((coefVecP hsh f C : KF n ps) : Langlands.GeneralLinear n ℝ → ℂ) =
      extension (shiftedExponent n (realPositionExponent ps))
        (coefP R (f : Langlands.GeneralLinear n ℝ → ℂ) C) :=
  rfl

theorem sum_minorG_sq (κ : Matrix.unitaryGroup (Fin n) ℝ) (A : Finset (Fin n)) :
    ∑ D : Finset (Fin n), minorG A D (Unitary.toUnits κ) * minorG A D (Unitary.toUnits κ) = 1 := by
  have h1 := sum_minor_sq κ A
  rw [← Finset.sum_subset (subset_univ (powersetCard A.card (univ : Finset (Fin n))))]
  · have e : ∀ D ∈ powersetCard A.card (univ : Finset (Fin n)),
        minorG A D (Unitary.toUnits κ) * minorG A D (Unitary.toUnits κ) =
          ((minor (κ : Matrix (Fin n) (Fin n) ℝ) A D *
            minor (κ : Matrix (Fin n) (Fin n) ℝ) A D : ℝ) : ℂ) := by
      intro D _
      unfold minorG
      push_cast
      rfl
    rw [Finset.sum_congr rfl e, ← Complex.ofReal_sum, h1, Complex.ofReal_one]
  · intro D _ hD
    have hc : A.card ≠ D.card := by
      intro h
      exact hD (mem_powersetCard.mpr ⟨subset_univ _, h.symm⟩)
    rw [minorG_of_card_ne hc, Pi.zero_apply, zero_mul]

theorem sum_prodG_sq (R : Fin N → Finset (Fin n)) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    ∑ C : Fin N → Finset (Fin n),
      prodG R C (Unitary.toUnits κ) * prodG R C (Unitary.toUnits κ) = 1 := by
  have e : ∀ C : Fin N → Finset (Fin n),
      prodG R C (Unitary.toUnits κ) * prodG R C (Unitary.toUnits κ) =
        ∏ j, (minorG (R j) (C j) (Unitary.toUnits κ) * minorG (R j) (C j) (Unitary.toUnits κ)) := by
    intro C
    rw [prodG_apply, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun C _ => e C]
  rw [← Fintype.prod_sum (fun j (D : Finset (Fin n)) =>
    minorG (R j) D (Unitary.toUnits κ) * minorG (R j) D (Unitary.toUnits κ))]
  exact Finset.prod_eq_one fun j _ => sum_minorG_sq κ (R j)

/-- **Spanning.** Every `f` is `∑_C Π_C h_C`. -/
theorem sum_mulProd_coefVecP (hsh : IsMinorShift n ps qs R) (f : KF n qs) :
    ∑ C, mulProd hsh C (coefVecP hsh f C) = f := by
  apply Subtype.ext
  have h₁ := (mem_KF_iff hsh.principal_right _).mp (∑ C, mulProd hsh C (coefVecP hsh f C)).2
  have h₂ := (mem_KF_iff hsh.principal_right _).mp f.2
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries h₁.1 h₂.1 fun k hk => ?_
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  rw [Submodule.coe_sum, Finset.sum_apply, hku]
  have hs : ∀ C ∈ (univ : Finset (Fin N → Finset (Fin n))),
      ((mulProd hsh C (coefVecP hsh f C) : KF n qs) : Langlands.GeneralLinear n ℝ → ℂ)
          (Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
            Matrix.unitaryGroup (Fin n) ℝ)) =
        (f : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩) *
          (prodG R C (Unitary.toUnits ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩) *
            prodG R C (Unitary.toUnits ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩)) := by
    intro C _
    rw [mulProd_coe, coefVecP_coe, extension_unitary, coefP]
    ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, sum_prodG_sq, mul_one]

/-! ## The reduction -/

/-- **Product reduction.** If `T` generates the module of `ps` under the Lie algebra, every
Lie-stable subspace of the module of `qs` containing all products `Π_C T` is everything. -/
theorem eq_top_of_cyclic (hsh : IsMinorShift n ps qs R) (T : KF n ps)
    (hcyc : ∀ W' : Submodule ℂ (KF n ps), T ∈ W' →
      (∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ w ∈ W', realStandardLie n ps Z w ∈ W') → W' = ⊤)
    (W : Submodule ℂ (KF n qs))
    (hWL : ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ W, realStandardLie n qs Z v ∈ W)
    (hvec : ∀ C, mulProd hsh C T ∈ W) : W = ⊤ := by
  have htop : pullback hsh W = ⊤ :=
    hcyc _ ((mem_pullback hsh).mpr hvec) fun Z w hw => pullback_lie hsh hWL Z hw
  rw [eq_top_iff]
  intro f _
  rw [← sum_mulProd_coefVecP hsh f]
  refine Submodule.sum_mem _ fun C _ => ?_
  have hC : coefVecP hsh f C ∈ pullback hsh W := htop ▸ Submodule.mem_top
  exact (mem_pullback hsh).mp hC C

end RealDiscreteMinorCyclic

end Langlands.Archimedean
