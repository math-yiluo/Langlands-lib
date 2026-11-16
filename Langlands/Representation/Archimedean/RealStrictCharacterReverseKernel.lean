import Langlands.Representation.Archimedean.JacquetMinorNonvanishing
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-!
# Intertwiners to the reversed standard module of a strictly ordered character list
-/

noncomputable section

open MeasureTheory Matrix Finset

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealStrictCharacterReverseKernel

open MatrixMinor JacquetMinor JacquetDual JacquetKernel PartialJacquet RealPrincipalSeriesDuality
  RealStrictCharacterLanglandsQuotient Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
  GramFormula

attribute [local instance] measurableSpaceK

/-- Borel structure on `O(n)` (its measurable space is the Borel one). -/
local instance borelSpaceK_rk (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-! ## Interpolation on finite-dimensional spaces of functions -/

/-- A finite-dimensional space `S` of functions has an interpolation family: points `p i` and
functions `u i ∈ S` with `s = ∑ s(p i) • u i` for every `s ∈ S`. -/
theorem exists_interpolation {X : Type*} (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → X) (u : ι → X → ℂ), (∀ i, u i ∈ S) ∧
      ∀ s ∈ S, s = ∑ i, s (p i) • u i := by
  classical
  let b := Module.finBasis ℂ S
  have hsep : ∀ s ∈ S, (∀ x : X, (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) s = 0) → s = 0 :=
    fun s _ hs => funext fun x => hs x
  have hcoord : ∀ j, ∃ (m : ℕ) (p : Fin m → X) (c : Fin m → ℂ), ∀ s (hs : s ∈ S),
      b.coord j ⟨s, hs⟩ = ∑ i, c i * s (p i) := by
    intro j
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend (b.coord j)
    obtain ⟨m, p, c, h⟩ := exists_sum_of_separating
      (fun x : X => (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)) S hsep ℓ
    refine ⟨m, p, c, fun s hs => ?_⟩
    rw [← hℓ, LinearMap.comp_apply, Submodule.subtype_apply]
    exact h s hs
  choose m p c hc using hcoord
  refine ⟨Σ j, Fin (m j), inferInstance, fun q => p q.1 q.2, fun q => c q.1 q.2 • (b q.1 : X → ℂ),
    fun q => S.smul_mem _ (b q.1).2, fun s hs => ?_⟩
  calc s = ((⟨s, hs⟩ : S) : X → ℂ) := rfl
    _ = ∑ j, b.repr ⟨s, hs⟩ j • (b j : X → ℂ) := by
        conv_lhs => rw [← b.sum_repr ⟨s, hs⟩]
        rw [Submodule.coe_sum]
        rfl
    _ = ∑ j, ∑ i, s (p j i) • (c j i • (b j : X → ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← b.coord_apply, hc j s hs, Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]
    _ = _ := (Fintype.sum_sigma (fun q : Σ j, Fin (m j) =>
          s (p q.1 q.2) • (c q.1 q.2 • (b q.1 : X → ℂ)))).symm

/-! ## Projections onto minors -/

variable {n : ℕ}

/-- The minor `κ ↦ det κ_{A,B}` on `O(n) ⊆ GL_n(ℝ)`, as a complex function. -/
def minorK (n : ℕ) (A B : Finset (Fin n)) (κ : unitaryCompact ℝ n) : ℂ :=
  ((minor ((κ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) A B : ℝ) : ℂ)

theorem continuous_minorK (A B : Finset (Fin n)) : Continuous (minorK n A B) :=
  Complex.continuous_ofReal.comp
    ((continuous_minor A B).comp (Units.continuous_val.comp continuous_subtype_val))

/-- The projection `P_{A,B} f(g) = ∫_{O(n)} det κ_{A,B} · f(g κ) dκ`. -/
def proj (n : ℕ) (A B : Finset (Fin n)) (f : Langlands.GeneralLinear n ℝ → ℂ)
    (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ∫ κ, minorK n A B κ * f (g * κ) ∂haarK n

theorem integrable_minorK_mul {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f)
    (A B : Finset (Fin n)) (g : Langlands.GeneralLinear n ℝ) :
    Integrable (fun κ : unitaryCompact ℝ n => minorK n A B κ * f (g * κ)) (haarK n) :=
  RealPrincipalSeriesDuality.integrable_of_continuous
    ((continuous_minorK A B).mul (hf.comp (continuous_const.mul continuous_subtype_val)))

/-- **Projections stay in finite-dimensional translation-stable spaces and commute with linear
functionals.** If all right translates `R(κ) f`, `κ ∈ O(n)`, lie in a finite-dimensional space
`V`, then `P_{A,B} f ∈ V`, and every linear functional `Λ` on `V` satisfies
`Λ(P_{A,B} f) = ∫ det κ_{A,B} · Λ(R(κ) f) dκ`. -/
theorem exists_proj_mem {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f)
    (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ κ : unitaryCompact ℝ n,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (κ : Langlands.GeneralLinear n ℝ)
        f ∈ V)
    (Λ : V →ₗ[ℂ] ℂ) (A B : Finset (Fin n)) :
    ∃ hP : proj n A B f ∈ V,
      Λ ⟨proj n A B f, hP⟩ = ∫ κ, minorK n A B κ * Λ ⟨_, hV κ⟩ ∂haarK n := by
  obtain ⟨ι, _, p, u, hu, hs⟩ := exists_interpolation V
  let v : ι → V := fun i => ⟨u i, hu i⟩
  have hR : ∀ κ : unitaryCompact ℝ n, (⟨_, hV κ⟩ : V) = ∑ i, f (p i * κ) • v i := by
    intro κ
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hs _ (hV κ)
  have hg : ∀ (g : Langlands.GeneralLinear n ℝ) (κ : unitaryCompact ℝ n),
      f (g * κ) = ∑ i, f (p i * κ) * u i g := by
    intro g κ
    have h := congrFun (hs _ (hV κ)) g
    rw [Finset.sum_apply] at h
    exact h
  have hPe : proj n A B f = ∑ i, proj n A B f (p i) • u i := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 : (fun κ : unitaryCompact ℝ n => minorK n A B κ * f (g * κ)) =
        fun κ => ∑ i, minorK n A B κ * f (p i * κ) * u i g := by
      funext κ
      rw [hg g κ, Finset.mul_sum]
      simp only [mul_assoc]
    change ∫ κ, minorK n A B κ * f (g * κ) ∂haarK n = _
    rw [h1, integral_finsetSum _ fun i _ => (integrable_minorK_mul hf A B (p i)).mul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const]
    rfl
  have hPV : proj n A B f ∈ V := by
    rw [hPe]
    exact V.sum_mem fun i _ => V.smul_mem _ (hu i)
  refine ⟨hPV, ?_⟩
  have h2 : (⟨proj n A B f, hPV⟩ : V) = ∑ i, proj n A B f (p i) • v i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hPe
  have h3 : (fun κ : unitaryCompact ℝ n => minorK n A B κ * Λ ⟨_, hV κ⟩) =
      fun κ => ∑ i, minorK n A B κ * f (p i * κ) * Λ (v i) := by
    funext κ
    rw [hR κ, map_sum, Finset.mul_sum]
    simp only [map_smul, smul_eq_mul, mul_assoc]
  rw [h2, map_sum, h3, integral_finsetSum _ fun i _ =>
    (integrable_minorK_mul hf A B (p i)).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, integral_mul_const]
  rfl

/-- The inverse of an orthogonal matrix is its transpose. -/
theorem val_inv_eq_transpose (κ : unitaryCompact ℝ n) :
    (((κ⁻¹ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      ((κ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  rw [Subgroup.coe_inv]
  refine Units.inv_eq_of_mul_eq_one_right ?_
  have h := Matrix.mem_unitaryGroup_iff.mp (κ.2 : ((κ : Langlands.GeneralLinear n ℝ) :
    Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.unitaryGroup (Fin n) ℝ)
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **Values of a projection on `O(n)`** (left invariance and Cauchy–Binet):
`P_{A,B} f(k) = ∑_{|C| = |A|} det k_{C,A} · P_{C,B} f(1)`. -/
theorem proj_apply_of_mem {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f)
    {A B : Finset (Fin n)} (hB : B.card = A.card) {k : Langlands.GeneralLinear n ℝ}
    (hk : k ∈ unitaryCompact ℝ n) :
    proj n A B f k = ∑ C ∈ powersetCard A.card univ, minorK n C A ⟨k, hk⟩ * proj n C B f 1 := by
  have hleft : ∫ κ, minorK n A B ((⟨k, hk⟩ : unitaryCompact ℝ n)⁻¹ * (⟨k, hk⟩ * κ)) *
      f ((⟨k, hk⟩ * κ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ) ∂haarK n =
      ∫ κ, minorK n A B ((⟨k, hk⟩ : unitaryCompact ℝ n)⁻¹ * κ) *
        f (κ : Langlands.GeneralLinear n ℝ) ∂haarK n :=
    integral_mul_left_eq_self (fun κ : unitaryCompact ℝ n =>
      minorK n A B ((⟨k, hk⟩ : unitaryCompact ℝ n)⁻¹ * κ) * f (κ : Langlands.GeneralLinear n ℝ))
      ⟨k, hk⟩
  simp only [inv_mul_cancel_left] at hleft
  have hexp : ∀ κ : unitaryCompact ℝ n, minorK n A B ((⟨k, hk⟩ : unitaryCompact ℝ n)⁻¹ * κ) =
      ∑ C ∈ powersetCard A.card univ, minorK n C A ⟨k, hk⟩ * minorK n C B κ := by
    intro κ
    unfold minorK
    rw [Subgroup.coe_mul, Units.val_mul, val_inv_eq_transpose, minor_mul _ _ rfl hB]
    push_cast
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [minor_transpose]
  change ∫ κ, minorK n A B κ * f ((⟨k, hk⟩ * κ : unitaryCompact ℝ n) :
    Langlands.GeneralLinear n ℝ) ∂haarK n = _
  rw [hleft]
  simp_rw [hexp, Finset.sum_mul]
  rw [integral_finsetSum _ fun C _ => ?_]
  · refine Finset.sum_congr rfl fun C _ => ?_
    unfold proj
    simp_rw [one_mul, mul_assoc]
    rw [integral_const_mul]
  · have h := (integrable_minorK_mul hf C B 1).const_mul (minorK n C A ⟨k, hk⟩)
    simp_rw [one_mul, ← mul_assoc] at h
    exact h

/-- **`M`-orthogonality.** If `f` lies in the principal series of characters whose values at
`-1` are `-1` exactly on `I`, then `P_{C,B} f(1) = 0` for `C ≠ I`: left translation by the sign
matrix with a single `-1` at a position of `C Δ I` multiplies the integral by `-1`. -/
theorem proj_one_eq_zero {χ : ℕ → ℝˣ → ℂ} (hone : ∀ l, χ l 1 = 1) {I : Finset (Fin n)}
    (hsign : ∀ l : Fin n, χ l (-1) = if l ∈ I then -1 else 1)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n χ)
    {C : Finset (Fin n)} (hC : C ≠ I) (B : Finset (Fin n)) : proj n C B f 1 = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, (j ∈ C ↔ j ∉ I) := by
    by_contra h
    exact hC (Finset.ext fun j => by_contra fun hj => h ⟨j, by tauto⟩)
  set t : Fin n → ℝˣ := fun l => if l = j then -1 else 1 with ht
  have hk₀ : (Iwasawa.diagonalUnits t : Langlands.GeneralLinear n ℝ) ∈ unitaryCompact ℝ n := by
    change ((Iwasawa.diagonalUnits t : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) ∈
      Matrix.unitaryGroup (Fin n) ℝ
    rw [Matrix.mem_unitaryGroup_iff, Iwasawa.diagonalUnits_val, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [ht, Pi.star_apply, star_trivial]
    split_ifs <;> simp
  have hleft : ∫ κ, minorK n C B (⟨_, hk₀⟩ * κ) *
      f (1 * ((⟨_, hk₀⟩ * κ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ)) ∂haarK n =
      ∫ κ, minorK n C B κ * f (1 * (κ : Langlands.GeneralLinear n ℝ)) ∂haarK n :=
    integral_mul_left_eq_self (fun κ : unitaryCompact ℝ n =>
      minorK n C B κ * f (1 * (κ : Langlands.GeneralLinear n ℝ))) ⟨_, hk₀⟩
  have h1 : ∀ κ : unitaryCompact ℝ n, minorK n C B (⟨_, hk₀⟩ * κ) =
      (if j ∈ C then -1 else 1) * minorK n C B κ := by
    intro κ
    unfold minorK
    rw [Subgroup.coe_mul, Units.val_mul]
    change ((minor (Matrix.diagonal (fun i => ((t i : ℝˣ) : ℝ)) *
      ((κ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) C B : ℝ) : ℂ) = _
    rw [minor_diagonal_mul, prod_single_sign]
    split_ifs <;> simp
  have h2 : ∀ κ : unitaryCompact ℝ n,
      f (1 * ((⟨_, hk₀⟩ * κ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ)) =
        (if j ∈ I then -1 else 1) * f (1 * (κ : Langlands.GeneralLinear n ℝ)) := by
    intro κ
    rw [one_mul, one_mul, Subgroup.coe_mul]
    have h := hf.2 t 1 (κ : Langlands.GeneralLinear n ℝ)
    rw [OneMemClass.coe_one, mul_one, principalSeriesCharacter_single hone hsign] at h
    exact h
  have hprod : (if j ∈ C then (-1 : ℂ) else 1) * (if j ∈ I then -1 else 1) = -1 := by
    by_cases hjC : j ∈ C
    · simp [hjC, hj.mp hjC]
    · have hjI : j ∈ I := by
        by_contra h
        exact hjC (hj.mpr h)
      simp [hjC, hjI]
  have h3 : ∀ κ : unitaryCompact ℝ n, minorK n C B (⟨_, hk₀⟩ * κ) *
      f (1 * ((⟨_, hk₀⟩ * κ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ)) =
        -(minorK n C B κ * f (1 * (κ : Langlands.GeneralLinear n ℝ))) := by
    intro κ
    rw [h1, h2]
    linear_combination (minorK n C B κ * f (1 * (κ : Langlands.GeneralLinear n ℝ))) * hprod
  simp only [h3, integral_neg] at hleft
  unfold proj
  linear_combination (-1 / 2 : ℂ) * hleft

/-! ## Characters of strictly ordered character lists -/

/-- The exponents of a strictly increasing character list, negated, are strictly dominant. -/
theorem isStrictlyDominant_neg : ∀ {ds : List RealBlock}, IsCharacterList ds →
    ds.Pairwise (fun x y => realBlockExponent x < realBlockExponent y) →
    IsStrictlyDominant (fun l => -realPositionExponent ds l) (realRank ds - 1)
  | [], _, _ => fun l hl => by simp [realRank] at hl
  | .induced d :: _, h, _ => by
      obtain ⟨c, hc⟩ := h _ (List.mem_cons_self ..)
      cases hc
  | .character d :: ds, h, hs => by
      have h' : IsCharacterList ds := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hs' := (List.pairwise_cons.mp hs).2
      have ih := isStrictlyDominant_neg h' hs'
      intro l hl
      rw [realRank_cons] at hl
      simp only [RealBlock.rank] at hl
      cases l with
      | zero =>
          cases ds with
          | nil => simp [realRank] at hl
          | cons b ds'' =>
              obtain ⟨c, rfl⟩ := h' b (List.mem_cons_self ..)
              have hrel := (List.pairwise_cons.mp hs).1 _ (List.mem_cons_self ..)
              simpa [realPositionExponent, realBlockExponent] using hrel
      | succ l =>
          simp only [realPositionExponent]
          exact ih l (by omega)

/-- Characters with values `±1` at `-1` take the value `-1` exactly on the set where they do. -/
theorem sign_filter {N : ℕ} {χ : ℕ → ℝˣ → ℂ} (h : ∀ l, χ l (-1) = 1 ∨ χ l (-1) = -1)
    (l : Fin N) :
    χ l (-1) = if l ∈ univ.filter (fun l : Fin N => χ l (-1) = -1) then -1 else 1 := by
  rcases h l with h | h
  · have h1 : (1 : ℂ) ≠ -1 := by norm_num
    simp [h, h1]
  · simp [h]

theorem dualChar_neg_one {χ : ℕ → ℝˣ → ℂ} {l : ℕ} (h : χ l (-1) = 1 ∨ χ l (-1) = -1) :
    dualChar χ l (-1) = 1 ∨ dualChar χ l (-1) = -1 := by
  rcases h with h | h
  · left
    simp [dualChar, h]
  · right
    simp [dualChar, h]

/-! ## The main theorem -/

/-- **Statement (intertwiners to the reversed module, strictly ordered characters).** Let `ds`
be a list of real character blocks of total rank `n` whose exponents have strictly decreasing
real parts. Every `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module
of `ds` to those of the standard module of `ds.reverse` vanishes on every proper
`(𝔤, K)`-submodule. -/
def RealStrictCharacterReverseKernelStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n))
    (W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))),
    realRank ds = n → IsCharacterList ds → IsStrictlyOrdered ds →
      IsRealStandardIntertwiner n (realStandardRep n ds.reverse) (realStandardLie n ds.reverse)
        ds T →
        IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W → W ≠ ⊤ →
          W ≤ LinearMap.ker T

theorem realStrictCharacterReverseKernel : RealStrictCharacterReverseKernelStatement := by
  intro n ds T W hn hchar hord hT hW hWtop
  have hχ := isSignedPower ds
  have he : IsStrictlyDominant (realPositionExponent ds) (n - 1) :=
    hn ▸ isStrictlyDominant hchar hord
  have hcharr : IsCharacterList ds.reverse := fun b hb => hchar b (List.mem_reverse.mp hb)
  have hrank : realRank ds.reverse = n := (realRank_perm (List.reverse_perm ds)).trans hn
  have hχ' := (isSignedPower ds.reverse).dual
  have he' : IsStrictlyDominant (fun l => -realPositionExponent ds.reverse l) (n - 1) := by
    rw [← hrank]
    exact isStrictlyDominant_neg hcharr (List.pairwise_reverse.mpr hord)
  have hdd : dualChar (dualChar (realPositionCharacter ds.reverse)) =
      realPositionCharacter ds.reverse := by
    funext l x
    simp [dualChar]
  have hS : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =
      kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n) := by
    rw [realStandardModule_eq hchar]
  have hSr : kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n) =
      kFiniteFunctions (principalSeries ℝ n
        (dualChar (dualChar (realPositionCharacter ds.reverse)))) (unitaryCompact ℝ n) := by
    rw [realStandardModule_eq hcharr, hdd]
  set χ := realPositionCharacter ds with hχdef
  set χ' := dualChar (realPositionCharacter ds.reverse) with hχ'def
  set e' : ℕ → ℂ := fun l => -realPositionExponent ds.reverse l with he'def
  set I : Finset (Fin n) := univ.filter fun l : Fin n => χ l (-1) = -1 with hI
  set I' : Finset (Fin n) := univ.filter fun l : Fin n => χ' l (-1) = -1 with hI'
  have hsign : ∀ l : Fin n, χ l (-1) = if l ∈ I then -1 else 1 :=
    sign_filter (realPositionCharacter_neg_one ds)
  have hsign' : ∀ l : Fin n, χ' l (-1) = if l ∈ I' then -1 else 1 :=
    sign_filter fun l => dualChar_neg_one (realPositionCharacter_neg_one ds.reverse l)
  let S := kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
  let Sr := kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n)
  -- the proper submodule `W`, as a space of functions, lies in the kernel of the Jacquet integral
  set W' : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) := W.map S.subtype with hW'def
  have hWX : W' ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
    rintro _ ⟨w, -, rfl⟩
    exact hS ▸ w.2
  have hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W',
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W' := by
    rintro k hk _ ⟨w, hwW, rfl⟩
    refine ⟨realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w, hW.1 _ w hwW, ?_⟩
    change ((realStandardRep n ds _ w : S) : Langlands.GeneralLinear n ℝ → ℂ) = _
    rw [realStandardRep_apply_coe]
    have hku : Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) = k := Units.ext rfl
    rw [hku]
    rfl
  have hWD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W',
      rightDerivative (matrixModel ℝ n) X w ∈ W' := by
    rintro X _ ⟨w, hwW, rfl⟩
    exact ⟨realStandardLie n ds (1 ⊗ₜ X) w, hW.2 _ w hwW,
      realStandardLie_one_tmul_apply_coe n ds X w⟩
  obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : S, g ∉ W := by
    by_contra hcon
    exact hWtop (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
  have hgW' : g ∉ W' := by
    rintro ⟨w, hwW, hw⟩
    apply hgW
    have : w = ⟨g, hgS⟩ := Subtype.ext hw
    rw [← this]
    exact hwW
  have hker : W' ≤ jacquetKernel n hχ he :=
    jacquet_eq_zero_of_proper hχ he W' hWX hWK hWD (hS ▸ hgS) hgW'
  have hJ := jacquet_minorVector_ne_zero n hχ he hsign
  -- suppose `T` does not vanish on `W`
  by_contra hle
  obtain ⟨w₀, hw₀W, hw₀T⟩ := SetLike.not_le_iff_exists.mp hle
  -- the image `T(W)`, as a space of functions
  set U : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) := (W.map T).map Sr.subtype with hUdef
  have hU : U ≤ kFiniteFunctions (principalSeries ℝ n (dualChar χ')) (unitaryCompact ℝ n) := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact hSr ▸ (T w).2
  have hUK : ∀ k ∈ unitaryCompact ℝ n, ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k u ∈ U := by
    rintro k hk _ ⟨_, ⟨w, hwW, rfl⟩, rfl⟩
    refine ⟨T (realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w),
      ⟨_, hW.1 _ w hwW, rfl⟩, ?_⟩
    rw [hT.map_realStandardRep]
    change ((realStandardRep n ds.reverse _ (T w) : Sr) : Langlands.GeneralLinear n ℝ → ℂ) = _
    rw [realStandardRep_apply_coe]
    have hku : Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) = k := Units.ext rfl
    rw [hku]
    rfl
  have hUD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ u ∈ U,
      rightDerivative (matrixModel ℝ n) X u ∈ U := by
    rintro X _ ⟨_, ⟨w, hwW, rfl⟩, rfl⟩
    refine ⟨T (realStandardLie n ds (1 ⊗ₜ X) w), ⟨_, hW.2 _ w hwW, rfl⟩, ?_⟩
    rw [hT.map_realStandardLie]
    exact realStandardLie_one_tmul_apply_coe n ds.reverse X (T w)
  have hU0 : U ≠ ⊥ := by
    intro hbot
    apply hw₀T
    have hmem : ((T w₀ : Sr) : Langlands.GeneralLinear n ℝ → ℂ) ∈ U :=
      ⟨T w₀, ⟨w₀, hw₀W, rfl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    rw [LinearMap.mem_ker]
    exact Subtype.ext hmem
  -- the dual statement `D(n)` and the nonvanishing for the dual characters give `w ∈ W`
  -- with `∫ det κ_{I',I'} (T w)(κ) dκ ≠ 0`
  have hφ' := minorVector_mem (e := e') hχ' hsign' (rfl : I'.card = I'.card)
  have hJ' := jacquet_minorVector_ne_zero n hχ' he' hsign'
  have hex : ∃ u ∈ U, ∫ k, u (k : Langlands.GeneralLinear n ℝ) *
      minorVector n e' I' I' k ∂haarK n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hJ' (jacquet_eq_zero n hχ' he' hU hUK hUD hU0 hφ' hcon)
  obtain ⟨_, ⟨_, ⟨w, hwW, rfl⟩, rfl⟩, hw⟩ := hex
  have hw' : ∫ κ, minorK n I' I' κ *
      ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n ≠ 0 := by
    have heq : (fun κ : unitaryCompact ℝ n => minorK n I' I' κ *
        ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ) κ) =
        fun κ : unitaryCompact ℝ n => (Sr.subtype (T w)) (κ : Langlands.GeneralLinear n ℝ) *
          minorVector n e' I' I' (κ : Langlands.GeneralLinear n ℝ) := by
      funext κ
      rw [minorVector_of_mem κ.2, mul_comm]
      rfl
    rw [heq]
    exact hw
  -- the finite-dimensional span `V` of the right translates of `w`
  have hwX : (w : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := hS ▸ w.2
  have hwc : Continuous (w : Langlands.GeneralLinear n ℝ → ℂ) := continuous_of_mem hwX
  set V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) := Submodule.span ℂ
    (Set.range fun k : unitaryCompact ℝ n => Whittaker.rightTranslation ℂ
      (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
      (w : Langlands.GeneralLinear n ℝ → ℂ)) with hVdef
  have : FiniteDimensional ℂ V := w.2.2
  have hV : ∀ κ : unitaryCompact ℝ n, Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (κ : Langlands.GeneralLinear n ℝ) (w : Langlands.GeneralLinear n ℝ → ℂ) ∈ V :=
    fun κ => Submodule.subset_span ⟨κ, rfl⟩
  have hVW : V ≤ W' := Submodule.span_le.mpr (by
    rintro _ ⟨κ, rfl⟩
    exact hWK _ κ.2 _ ⟨w, hwW, rfl⟩)
  have hVS : V ≤ S := fun v hv => by
    obtain ⟨v', -, rfl⟩ := hVW hv
    exact v'.2
  -- the functional `v ↦ (T v)(1)` on `V`
  let Λ : V →ₗ[ℂ] ℂ := (LinearMap.proj (1 : Langlands.GeneralLinear n ℝ)) ∘ₗ Sr.subtype ∘ₗ T ∘ₗ
    Submodule.inclusion hVS
  have hΛκ : ∀ κ : unitaryCompact ℝ n, Λ ⟨_, hV κ⟩ =
      ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ) κ := by
    intro κ
    obtain ⟨hf, hTf⟩ := hT.1 κ w
    change ((T ⟨_, hf⟩ : Sr) : Langlands.GeneralLinear n ℝ → ℂ) 1 = _
    have hku : Unitary.toUnits (⟨((κ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ),
        κ.2⟩ : Matrix.unitaryGroup (Fin n) ℝ) = (κ : Langlands.GeneralLinear n ℝ) := Units.ext rfl
    rw [hTf, realStandardRep_apply_coe, hku, TranslateFinite.rightTranslation_apply, one_mul]
  -- `P_{I',I'} w ≠ 0`
  obtain ⟨hPV, hΛ⟩ := exists_proj_mem hwc V hV Λ I' I'
  have hPne : proj n I' I' (w : Langlands.GeneralLinear n ℝ → ℂ) ≠ 0 := by
    intro h0
    have h1 : Λ ⟨proj n I' I' (w : Langlands.GeneralLinear n ℝ → ℂ), hPV⟩ = 0 := by
      have : (⟨proj n I' I' (w : Langlands.GeneralLinear n ℝ → ℂ), hPV⟩ : V) = 0 :=
        Subtype.ext h0
      rw [this, map_zero]
    have h2 : (fun κ : unitaryCompact ℝ n => minorK n I' I' κ * Λ ⟨_, hV κ⟩) =
        fun κ => minorK n I' I' κ * ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ) κ :=
      funext fun κ => by rw [hΛκ]
    rw [hΛ, h2] at h1
    exact hw' h1
  -- hence `P_{I,I'} w(1) ≠ 0`, by `M`-orthogonality
  have hzero : ∀ C, C ≠ I → ∀ B, proj n C B (w : Langlands.GeneralLinear n ℝ → ℂ) 1 = 0 :=
    fun C hC B => proj_one_eq_zero hχ.one hsign hwX.1 hC B
  have hPX : proj n I' I' (w : Langlands.GeneralLinear n ℝ → ℂ) ∈ principalSeries ℝ n χ :=
    (hWX (hVW hPV)).1
  obtain ⟨k, hk, hPk⟩ : ∃ k ∈ unitaryCompact ℝ n,
      proj n I' I' (w : Langlands.GeneralLinear n ℝ → ℂ) k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPne (eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact hPX hcon)
  rw [proj_apply_of_mem hwc rfl hk] at hPk
  have hII' : I ∈ powersetCard I'.card univ := by
    by_contra hnot
    apply hPk
    refine Finset.sum_eq_zero fun C hC => ?_
    rw [hzero C (fun h => hnot (h ▸ hC)) I', mul_zero]
  have hc : proj n I I' (w : Langlands.GeneralLinear n ℝ → ℂ) 1 ≠ 0 := by
    rw [Finset.sum_eq_single I (fun C _ hC => by rw [hzero C hC I', mul_zero])
      (fun h => absurd hII' h)] at hPk
    exact right_ne_zero_of_mul hPk
  have hcard : I'.card = I.card := ((mem_powersetCard.mp hII').2).symm
  -- `P_{I,I'} w` is a nonzero multiple of `φ_{I,I}`, so `φ_{I,I} ∈ W`
  obtain ⟨hPV₂, -⟩ := exists_proj_mem hwc V hV 0 I I'
  have hφ := minorVector_mem hχ hsign (rfl : I.card = I.card)
  have hφeq : minorVector n (realPositionExponent ds) I I =
      (proj n I I' (w : Langlands.GeneralLinear n ℝ → ℂ) 1)⁻¹ •
        proj n I I' (w : Langlands.GeneralLinear n ℝ → ℂ) := by
    refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries hφ.1
      (Submodule.smul_mem _ _ (hWX (hVW hPV₂)).1) fun k hk => ?_
    rw [Pi.smul_apply, smul_eq_mul, proj_apply_of_mem hwc hcard hk, Finset.sum_eq_single I,
      minorVector_of_mem hk, mul_left_comm, inv_mul_cancel₀ hc, mul_one]
    · rfl
    · intro C _ hC
      rw [hzero C hC I', mul_zero]
    · intro h
      exact absurd (mem_powersetCard.mpr ⟨subset_univ _, rfl⟩) h
  have hφW : minorVector n (realPositionExponent ds) I I ∈ W' := by
    rw [hφeq]
    exact W'.smul_mem _ (hVW hPV₂)
  exact hJ (hker hφW).2

end RealStrictCharacterReverseKernel

end Langlands.Archimedean
