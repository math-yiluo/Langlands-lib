import Langlands.Global.RankinSelberg.EqualAnalyticLattice
import Langlands.Global.RankinSelberg.EqualAnalyticFourierDominated

/-! # Poisson summation on `𝔸^n`

For a standard additive character `ψ` and `Φ ∈ S(𝔸^n)`,
`Σ_{ξ ∈ F^n} Φ(ξ) = Σ_{η ∈ F^n} Φ̂(η)`, both series converging absolutely, where `Φ̂` is the
Library's Fourier transform for the covolume-one measure. The proof expands the periodization
`Σ_ξ Φ(x + ξ)`, a continuous function on the compact group `(𝔸 / F)^n`, in the characters
`x ↦ ψ(Σ_j x_j η_j)`, `η ∈ F^n`, whose Fourier coefficients are the values `Φ̂(-η)`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped Classical Langlands.Automorphic.CuspidalWhittaker
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

local instance poissonMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance poissonBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance poissonQuotientMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (AdeleQuotient F)) := borel _

local instance poissonQuotientBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (AdeleQuotient F)) := ⟨rfl⟩

local instance poissonQuotientT2 (k m : ℕ) :
    T2Space (Matrix (Fin k) (Fin m) (AdeleQuotient F)) :=
  inferInstanceAs (T2Space (Fin k → Fin m → AdeleQuotient F))

/-- Rational row vectors `F^n`, as `1 × n` matrices. -/
abbrev RatRow (n : ℕ) := Matrix (Fin 1) (Fin n) F

/-- The compact quotient `(𝔸 / F)^n`. -/
abbrev RowQuotient (n : ℕ) := Matrix (Fin 1) (Fin n) (AdeleQuotient F)

/-- The adelic row vector of a rational one. -/
def ratRow (n : ℕ) (C : RatRow F n) : RowVector F n := C.map (algebraMap F (Adeles F))

theorem ratRow_add (n : ℕ) (C C' : RatRow F n) : ratRow F n (C + C') = ratRow F n C + ratRow F n C' := by
  ext i j
  simp [ratRow]

theorem ratRow_neg (n : ℕ) (C : RatRow F n) : ratRow F n (-C) = -ratRow F n C := by
  ext i j
  simp [ratRow]

theorem ratRow_zero (n : ℕ) : ratRow F n 0 = 0 := by
  ext i j
  simp [ratRow]

theorem algebraMap_adeles_injective : Function.Injective (algebraMap F (Adeles F)) := by
  intro x y h
  have h1 := congrArg (fun z : Adeles F => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1) h
  simp only [adeles_algebraMap_fst,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at h1
  exact mixedEmbedding_injective F h1

theorem ratRow_injective (n : ℕ) : Function.Injective (ratRow F n) := by
  intro C C' h
  ext i j
  have := congrFun (congrFun h i) j
  exact algebraMap_adeles_injective F this

/-- The entries `(C_{0j})_j` of a rational row vector. -/
def ratRowVec (n : ℕ) (C : RatRow F n) : Fin n → F := fun j => C 0 j

omit [Field F] [NumberField F] in
theorem ratRowVec_injective (n : ℕ) : Function.Injective (ratRowVec F n) := by
  intro C C' h
  ext i j
  rw [Subsingleton.elim i 0]
  exact congrFun h j

theorem matrixQuotientMap_ratRow_add (n : ℕ) (C : RatRow F n) (X : RowVector F n) :
    matrixQuotientMap (ratRow F n C + X) = matrixQuotientMap X :=
  GeneralLinearBlockUnipotent.matrixQuotientMap_rational_add F C X

/-- The pairing character `x ↦ ψ(Σ_j x_j η_j)` of `𝔸^n`. -/
def pairingCharacter (ψ : AddChar (Adeles F) ℂ) (n : ℕ) (η : RatRow F n)
    (X : RowVector F n) : ℂ :=
  ψ (∑ j, X 0 j * algebraMap F (Adeles F) (η 0 j))

theorem pairingCharacter_add (ψ : AddChar (Adeles F) ℂ) (n : ℕ) (η : RatRow F n)
    (X Y : RowVector F n) :
    pairingCharacter F ψ n η (X + Y) = pairingCharacter F ψ n η X * pairingCharacter F ψ n η Y := by
  unfold pairingCharacter
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, add_mul]

theorem pairingCharacter_ratRow (ψ : AddChar (Adeles F) ℂ)
    (htriv : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (n : ℕ) (η C : RatRow F n) :
    pairingCharacter F ψ n η (ratRow F n C) = 1 := by
  unfold pairingCharacter
  have : ∑ j, ratRow F n C 0 j * algebraMap F (Adeles F) (η 0 j) =
      algebraMap F (Adeles F) (∑ j, C 0 j * η 0 j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rfl
  rw [this, htriv]

theorem pairingCharacter_ratRow_add (ψ : AddChar (Adeles F) ℂ)
    (htriv : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (n : ℕ) (η C : RatRow F n)
    (X : RowVector F n) :
    pairingCharacter F ψ n η (ratRow F n C + X) = pairingCharacter F ψ n η X := by
  rw [pairingCharacter_add, pairingCharacter_ratRow F ψ htriv, one_mul]

theorem continuous_pairingCharacter (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ) (n : ℕ)
    (η : RatRow F n) : Continuous (pairingCharacter F ψ n η) :=
  hψ.comp (continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem 0 j).mul continuous_const)

theorem pairingCharacter_mul_eq (ψ : AddChar (Adeles F) ℂ) (n : ℕ) (η η' : RatRow F n)
    (X : RowVector F n) :
    pairingCharacter F ψ n (η + η') X = pairingCharacter F ψ n η X * pairingCharacter F ψ n η' X := by
  unfold pairingCharacter
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, map_add, mul_add]

theorem pairingCharacter_neg_eq (ψ : AddChar (Adeles F) ℂ) (n : ℕ) (η : RatRow F n)
    (X : RowVector F n) : pairingCharacter F ψ n (-η) X = (pairingCharacter F ψ n η X)⁻¹ := by
  unfold pairingCharacter
  rw [← AddChar.map_neg_eq_inv, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.neg_apply, map_neg, mul_neg]

/-- The descended pairing character on `(𝔸 / F)^n`. -/
def quotientCharacter (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (n : ℕ) (η : RatRow F n) : C(RowQuotient F n, ℂ) where
  toFun x := pairingCharacter F ψ n η (matrixLift x)
  continuous_toFun := by
    rw [(isOpenQuotientMap_matrixQuotientMap (K := F) 1 n).isQuotientMap.continuous_iff]
    convert continuous_pairingCharacter F ψ hψ.1 n η using 1
    funext X
    change pairingCharacter F ψ n η (matrixLift (matrixQuotientMap X)) =
      pairingCharacter F ψ n η X
    obtain ⟨C, hC⟩ := exists_rational_of_matrixQuotientMap_eq
      (matrixQuotientMap_matrixLift (matrixQuotientMap X)).symm
    rw [hC]
    exact pairingCharacter_ratRow_add F ψ hψ.2.2.1 n η C _

theorem quotientCharacter_mk (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (n : ℕ) (η : RatRow F n) (X : RowVector F n) :
    quotientCharacter F ψ hψ n η (matrixQuotientMap X) = pairingCharacter F ψ n η X := by
  change pairingCharacter F ψ n η (matrixLift (matrixQuotientMap X)) = _
  obtain ⟨C, hC⟩ := exists_rational_of_matrixQuotientMap_eq
    (matrixQuotientMap_matrixLift (matrixQuotientMap X)).symm
  rw [hC]
  exact pairingCharacter_ratRow_add F ψ hψ.2.2.1 n η C _

theorem norm_pairingCharacter (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (n : ℕ) (η : RatRow F n) (X : RowVector F n) : ‖pairingCharacter F ψ n η X‖ = 1 :=
  hψ.2.2.2 _

theorem isCharacterFamily_quotientCharacter (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (n : ℕ) :
    IsCharacterFamily (quotientCharacter F ψ hψ n) where
  zero := by
    ext x
    change pairingCharacter F ψ n 0 (matrixLift x) = 1
    simp [pairingCharacter]
  add η η' := by
    ext x
    exact pairingCharacter_mul_eq F ψ n η η' (matrixLift x)
  neg η := by
    ext x
    change pairingCharacter F ψ n (-η) (matrixLift x) = star (pairingCharacter F ψ n η (matrixLift x))
    rw [pairingCharacter_neg_eq]
    have h1 := norm_pairingCharacter F ψ hψ n η (matrixLift x)
    rw [RCLike.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
    simp
  norm_apply η x := norm_pairingCharacter F ψ hψ n η (matrixLift x)

/-- The rational row vector with entry `a` at `j` and zero elsewhere. -/
def singleRow (n : ℕ) (j : Fin n) (a : F) : RatRow F n := Matrix.of fun _ l => if l = j then a else 0

theorem pairingCharacter_singleRow (ψ : AddChar (Adeles F) ℂ) (n : ℕ) (j : Fin n) (a : F)
    (X : RowVector F n) :
    pairingCharacter F ψ n (singleRow F n j a) X = ψ (X 0 j * algebraMap F (Adeles F) a) := by
  unfold pairingCharacter
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [singleRow]
  · intro l _ hl
    simp [singleRow, hl]
  · simp

theorem mk_matrixLift (n : ℕ) (x : RowQuotient F n) (i : Fin 1) (j : Fin n) :
    adeleQuotientMap F (matrixLift x i j) = x i j := by
  have := matrixQuotientMap_matrixLift x
  exact congrFun (congrFun this i) j

/-- The characters `x ↦ ψ(Σ_j x_j η_j)` separate the points of `(𝔸 / F)^n`. -/
theorem quotientCharacter_separates [CompactSpace (AdeleQuotient F)] (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (n : ℕ) (x y : RowQuotient F n) (h : x ≠ y) :
    ∃ η, quotientCharacter F ψ hψ n η x ≠ quotientCharacter F ψ hψ n η y := by
  by_contra hcon
  push Not at hcon
  apply h
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  obtain ⟨δ, hδ⟩ := exists_eq_algebraMap_of_forall_eq_one F ψ hψ
    (matrixLift y 0 j - matrixLift x 0 j) fun a => by
      have h1 := hcon (singleRow F n j a)
      change pairingCharacter F ψ n _ (matrixLift x) = pairingCharacter F ψ n _ (matrixLift y)
        at h1
      rw [pairingCharacter_singleRow, pairingCharacter_singleRow] at h1
      rw [mul_comm, sub_mul, AddChar.map_sub_eq_div, h1, div_self]
      intro h0
      have := hψ.2.2.2 (matrixLift y 0 j * algebraMap F (Adeles F) a)
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  rw [← mk_matrixLift F n x, ← mk_matrixLift F n y,
    show matrixLift y 0 j = matrixLift x 0 j + algebraMap F (Adeles F) δ by rw [← hδ]; abel,
    map_add]
  have hz : adeleQuotientMap F (algebraMap F (Adeles F) δ) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨δ, rfl⟩
  rw [hz, add_zero]

theorem quotientCharacter_add_apply (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (n : ℕ) (η : RatRow F n) (x y : RowQuotient F n) :
    quotientCharacter F ψ hψ n η (x + y) =
      quotientCharacter F ψ hψ n η x * quotientCharacter F ψ hψ n η y := by
  have hxy : x + y = matrixQuotientMap (matrixLift x + matrixLift y) := by
    rw [GeneralLinearBlockUnipotent.matrixQuotientMap_add, matrixQuotientMap_matrixLift,
      matrixQuotientMap_matrixLift]
  rw [hxy, quotientCharacter_mk, pairingCharacter_add]
  rfl

/-- Nontrivial characters of `(𝔸 / F)^n` have integral zero. -/
theorem integral_quotientCharacter [CompactSpace (AdeleQuotient F)] (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (n : ℕ) (η : RatRow F n) (hη : η ≠ 0) :
    ∫ x, quotientCharacter F ψ hψ n η x ∂matrixQuotientHaar F 1 n = 0 := by
  have := matrixQuotientHaar_isAddHaarMeasure F 1 n
  obtain ⟨j, hj⟩ : ∃ j, η 0 j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hη
    ext i l
    rw [Subsingleton.elim i 0]
    exact hall l
  obtain ⟨z, hz⟩ : ∃ z, ψ z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hψ.2.1 (by ext w; simp [hall w])
  let X₀ : RowVector F n := Matrix.of fun _ l =>
    if l = j then algebraMap F (Adeles F) (η 0 j)⁻¹ * z else 0
  apply integral_eq_zero_of_mul_apply (matrixQuotientHaar F 1 n) _
    (quotientCharacter_add_apply F ψ hψ n η) (y := matrixQuotientMap X₀)
  rw [quotientCharacter_mk]
  have hsum : ∑ l, X₀ 0 l * algebraMap F (Adeles F) (η 0 l) = z := by
    rw [Finset.sum_eq_single j]
    · show (if j = j then algebraMap F (Adeles F) (η 0 j)⁻¹ * z else 0) *
        algebraMap F (Adeles F) (η 0 j) = z
      rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), mul_right_comm, ← map_mul,
        inv_mul_cancel₀ hj, map_one, one_mul]
    · intro l _ hl
      show (if l = j then algebraMap F (Adeles F) (η 0 j)⁻¹ * z else 0) *
        algebraMap F (Adeles F) (η 0 l) = 0
      rw [ite_eq_right_iff.mpr (fun h => absurd h hl), zero_mul]
    · simp
  unfold pairingCharacter
  rw [hsum]
  exact hz

theorem archimedeanCoordinates_add (n : ℕ) (X Y : RowVector F n) :
    archimedeanCoordinates F n (X + Y) =
      archimedeanCoordinates F n X + archimedeanCoordinates F n Y := by
  have := congrArg Prod.fst (map_add (rowSplit F n) X Y)
  exact this

theorem finiteCoordinates_add (n : ℕ) (X Y : RowVector F n) :
    finiteCoordinates F n (X + Y) = finiteCoordinates F n X + finiteCoordinates F n Y := rfl

theorem archimedeanCoordinates_ratRow (n : ℕ) (C : RatRow F n) :
    archimedeanCoordinates F n (ratRow F n C) = rowEmbedding F n (ratRowVec F n C) := by
  funext j
  change InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Adeles F) (C 0 j)).1 =
    mixedEmbedding F (C 0 j)
  rw [adeles_algebraMap_fst, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

theorem finiteCoordinates_ratRow (n : ℕ) (C : RatRow F n) (j : Fin n) :
    finiteCoordinates F n (ratRow F n C) j = algebraMap F (FiniteAdeles F) (C 0 j) := rfl

/-- A dominated function is bounded by an inverse power. -/
theorem IsRowDominated.norm_le_rpow {n : ℕ} {Φ : RowVector F n → ℂ} {N : ℕ} {K : ℝ}
    (hK : ∀ x, (1 + ‖archimedeanCoordinates F n x‖) ^ N * ‖Φ x‖ ≤ K) (x : RowVector F n) :
    ‖Φ x‖ ≤ K * (1 + ‖archimedeanCoordinates F n x‖) ^ (-(N : ℝ)) := by
  have hpos : 0 < (1 + ‖archimedeanCoordinates F n x‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ hpos, mul_comm]
  exact hK x

/-- Local uniform summability of translates of a dominated function. -/
theorem exists_local_periodization_bound (n : ℕ) {Φ : RowVector F n → ℂ}
    (hΦ : IsRowDominated F n Φ) (X₀ : RowVector F n) :
    ∃ U ∈ nhds X₀, ∃ u : RatRow F n → ℝ, Summable u ∧ (∀ C, 0 ≤ u C) ∧
      ∀ C, ∀ X ∈ U, ‖Φ (ratRow F n C + X)‖ ≤ u C := by
  obtain ⟨d, hd, hsupp, hdec⟩ := hΦ
  obtain ⟨e, he, hes⟩ := exists_integer_mul_mem_of_isCompact F
    (Set.finite_range (finiteCoordinates F n X₀)).isCompact
  set N : ℕ := n * Module.finrank ℚ F + 1
  obtain ⟨K, hK⟩ := hdec N
  set R := ‖archimedeanCoordinates F n X₀‖
  let U : Set (RowVector F n) :=
    {X | ‖archimedeanCoordinates F n X - archimedeanCoordinates F n X₀‖ < 1} ∩
      {X | ∀ j, finiteCoordinates F n X j - finiteCoordinates F n X₀ j ∈ integralFiniteAdeles F}
  have hUopen : IsOpen U := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (((continuous_archimedeanCoordinates F n).sub continuous_const).norm)
        continuous_const
    · have : {X : RowVector F n | ∀ j, finiteCoordinates F n X j - finiteCoordinates F n X₀ j ∈
          integralFiniteAdeles F} = ⋂ j, {X | finiteCoordinates F n X j -
            finiteCoordinates F n X₀ j ∈ integralFiniteAdeles F} := by
        ext X
        simp
      rw [this]
      exact isOpen_iInter_of_finite fun j => (isOpen_integralFiniteAdeles F).preimage
        (((continuous_apply j).comp (continuous_finiteCoordinates F n)).sub continuous_const)
  have hX₀ : X₀ ∈ U := by
    refine ⟨?_, fun j => ?_⟩
    · simp
    · rw [sub_self]
      exact zero_mem _
  let S := IntegralRows F n (d * e)
  let g : (Fin n → F) → ℝ := S.indicator fun ξ => (1 + ‖rowEmbedding F n ξ‖) ^ (-(N : ℝ))
  have hN : ((n * Module.finrank ℚ F : ℕ) : ℝ) < (N : ℝ) := by
    simp only [N]
    push_cast
    linarith
  have hg : Summable g := (summable_subtype_iff_indicator).mp
    (summable_integralRows F n (d * e) (mul_ne_zero hd he) hN)
  refine ⟨U, hUopen.mem_nhds hX₀, fun C => max K 0 * (2 + R) ^ N * g (ratRowVec F n C),
    (hg.comp_injective (ratRowVec_injective F n)).mul_left _, fun C => ?_, fun C X hX => ?_⟩
  · have : 0 ≤ g (ratRowVec F n C) := Set.indicator_nonneg (fun ξ _ => by positivity) _
    positivity
  show ‖Φ (ratRow F n C + X)‖ ≤ max K 0 * (2 + R) ^ N * g (ratRowVec F n C)
  by_cases hzero : Φ (ratRow F n C + X) = 0
  · rw [hzero, norm_zero]
    have : 0 ≤ g (ratRowVec F n C) := Set.indicator_nonneg (fun ξ _ => by positivity) _
    positivity
  have hmem : ratRowVec F n C ∈ S := by
    intro j
    have h1 := hsupp _ hzero j
    rw [finiteCoordinates_add, Pi.add_apply, finiteCoordinates_ratRow] at h1
    have h2 := hX.2 j
    have h3 := hes _ (Set.mem_range_self j)
    obtain ⟨c, hc⟩ : ∃ c, C 0 j = c := ⟨_, rfl⟩
    rw [hc] at h1
    have hint : algebraMap F (FiniteAdeles F)
        (algebraMap (𝓞 F) F (d * e) * c) ∈ integralFiniteAdeles F := by
      have : algebraMap F (FiniteAdeles F) (algebraMap (𝓞 F) F (d * e) * c) =
          algebraMap (𝓞 F) (FiniteAdeles F) e *
              (algebraMap (𝓞 F) (FiniteAdeles F) d *
                (algebraMap F (FiniteAdeles F) c + finiteCoordinates F n X j)) -
            algebraMap (𝓞 F) (FiniteAdeles F) d *
              (algebraMap (𝓞 F) (FiniteAdeles F) e *
                (finiteCoordinates F n X j - finiteCoordinates F n X₀ j)) -
            algebraMap (𝓞 F) (FiniteAdeles F) d *
              (algebraMap (𝓞 F) (FiniteAdeles F) e * finiteCoordinates F n X₀ j) := by
        simp only [map_mul, ← IsScalarTower.algebraMap_apply]
        ring
      rw [this]
      refine sub_mem (sub_mem (mul_mem (algebraMap_ringOfIntegers_mem F e) h1)
        (mul_mem (algebraMap_ringOfIntegers_mem F d)
          (mul_mem (algebraMap_ringOfIntegers_mem F e) h2)))
        (mul_mem (algebraMap_ringOfIntegers_mem F d) h3)
    obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_integral F _ hint
    refine ⟨a, ?_⟩
    change algebraMap (𝓞 F) F (d * e) * C 0 j = _
    rw [hc, ha]
  have hgC : g (ratRowVec F n C) = (1 + ‖rowEmbedding F n (ratRowVec F n C)‖) ^ (-(N : ℝ)) :=
    Set.indicator_of_mem hmem _
  rw [hgC]
  have hbound := IsRowDominated.norm_le_rpow F hK (ratRow F n C + X)
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK (ratRow F n C + X))
  have hcomp : 1 + ‖rowEmbedding F n (ratRowVec F n C)‖ ≤
      (2 + R) * (1 + ‖archimedeanCoordinates F n (ratRow F n C + X)‖) := by
    have e1 : rowEmbedding F n (ratRowVec F n C) =
        archimedeanCoordinates F n (ratRow F n C + X) -
          (archimedeanCoordinates F n X - archimedeanCoordinates F n X₀) -
            archimedeanCoordinates F n X₀ := by
      rw [archimedeanCoordinates_add, archimedeanCoordinates_ratRow]
      abel
    have hXn : ‖archimedeanCoordinates F n X - archimedeanCoordinates F n X₀‖ < 1 := hX.1
    rw [e1]
    have := norm_sub_le (archimedeanCoordinates F n (ratRow F n C + X) -
      (archimedeanCoordinates F n X - archimedeanCoordinates F n X₀))
      (archimedeanCoordinates F n X₀)
    have := norm_sub_le (archimedeanCoordinates F n (ratRow F n C + X))
      (archimedeanCoordinates F n X - archimedeanCoordinates F n X₀)
    have h0 : 0 ≤ ‖archimedeanCoordinates F n (ratRow F n C + X)‖ := norm_nonneg _
    have hR0 : 0 ≤ R := norm_nonneg _
    nlinarith
  have hrp := Hecke.rpow_neg_le_of_le_mul (by positivity) (by positivity) (Nat.cast_nonneg N) hcomp
  rw [Real.rpow_natCast] at hrp
  calc ‖Φ (ratRow F n C + X)‖ ≤
        K * (1 + ‖archimedeanCoordinates F n (ratRow F n C + X)‖) ^ (-(N : ℝ)) := hbound
    _ ≤ max K 0 * ((2 + R) ^ N * (1 + ‖rowEmbedding F n (ratRowVec F n C)‖) ^ (-(N : ℝ))) :=
        mul_le_mul (le_max_left _ _) hrp (by positivity) (le_max_right _ _)
    _ = _ := by ring

/-- The periodization `X ↦ Σ_{ξ ∈ F^n} Φ(ξ + X)`. -/
def periodization (n : ℕ) (Φ : RowVector F n → ℂ) (X : RowVector F n) : ℂ :=
  ∑' C : RatRow F n, Φ (ratRow F n C + X)

theorem summable_periodization (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : IsRowDominated F n Φ)
    (X : RowVector F n) : Summable fun C : RatRow F n => Φ (ratRow F n C + X) := by
  obtain ⟨U, hU, u, hu, -, hbound⟩ := exists_local_periodization_bound F n hΦ X
  exact Summable.of_norm_bounded hu fun C => hbound C X (mem_of_mem_nhds hU)

theorem summable_norm_periodization (n : ℕ) {Φ : RowVector F n → ℂ}
    (hΦ : IsRowDominated F n Φ) (X : RowVector F n) :
    Summable fun C : RatRow F n => ‖Φ (ratRow F n C + X)‖ := by
  obtain ⟨U, hU, u, hu, -, hbound⟩ := exists_local_periodization_bound F n hΦ X
  exact Summable.of_nonneg_of_le (fun C => norm_nonneg _) (fun C => hbound C X (mem_of_mem_nhds hU)) hu

theorem continuous_periodization (n : ℕ) {Φ : RowVector F n → ℂ} (hc : Continuous Φ)
    (hΦ : IsRowDominated F n Φ) : Continuous (periodization F n Φ) := by
  rw [continuous_iff_continuousAt]
  intro X₀
  obtain ⟨U, hU, u, hu, -, hbound⟩ := exists_local_periodization_bound F n hΦ X₀
  have hon : ContinuousOn (periodization F n Φ) U :=
    continuousOn_tsum (fun C => (hc.comp (continuous_const.add continuous_id)).continuousOn) hu
      fun C X hX => hbound C X hX
  exact hon.continuousAt hU

theorem periodization_ratRow_add (n : ℕ) (Φ : RowVector F n → ℂ) (C₀ : RatRow F n)
    (X : RowVector F n) : periodization F n Φ (ratRow F n C₀ + X) = periodization F n Φ X := by
  unfold periodization
  rw [← (Equiv.addRight C₀).tsum_eq (fun C => Φ (ratRow F n C + X))]
  refine tsum_congr fun C => ?_
  simp only [Equiv.coe_addRight, ratRow_add, add_assoc]

theorem periodization_matrixLift (n : ℕ) (Φ : RowVector F n → ℂ) (X : RowVector F n) :
    periodization F n Φ (matrixLift (matrixQuotientMap X)) = periodization F n Φ X := by
  obtain ⟨C, hC⟩ := exists_rational_of_matrixQuotientMap_eq
    (matrixQuotientMap_matrixLift (matrixQuotientMap X)).symm
  rw [hC]
  exact periodization_ratRow_add F n Φ C X

/-- The periodization as a continuous function on `(𝔸 / F)^n`. -/
def quotientPeriodization (n : ℕ) (Φ : RowVector F n → ℂ) (hc : Continuous Φ)
    (hΦ : IsRowDominated F n Φ) : C(RowQuotient F n, ℂ) where
  toFun x := periodization F n Φ (matrixLift x)
  continuous_toFun := by
    rw [(isOpenQuotientMap_matrixQuotientMap (K := F) 1 n).isQuotientMap.continuous_iff]
    convert continuous_periodization F n hc hΦ using 1
    funext X
    exact periodization_matrixLift F n Φ X

theorem quotientPeriodization_mk (n : ℕ) (Φ : RowVector F n → ℂ) (hc : Continuous Φ)
    (hΦ : IsRowDominated F n Φ) (X : RowVector F n) :
    quotientPeriodization F n Φ hc hΦ (matrixQuotientMap X) = periodization F n Φ X :=
  periodization_matrixLift F n Φ X

/-- The rational row vectors, as the subgroup `rowLattice`. -/
def ratRowEquiv (n : ℕ) : RatRow F n ≃ rowLattice F n :=
  Equiv.ofBijective (fun C => ⟨ratRow F n C, ⟨C, rfl⟩⟩)
    ⟨fun _ _ h => ratRow_injective F n (congrArg Subtype.val h),
      fun ⟨_, C, hC⟩ => ⟨C, Subtype.ext hC⟩⟩

theorem star_addChar (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (z : Adeles F) : star (ψ z) = ψ (-z) := by
  rw [AddChar.map_neg_eq_inv]
  have h1 := hψ.2.2.2 z
  rw [RCLike.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  simp

/-- The Fourier coefficients of the periodization are values of the Fourier transform. -/
theorem fourierCoeff_quotientPeriodization [CompactSpace (AdeleQuotient F)] (n : ℕ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hc : Continuous Φ) (hint : Integrable Φ (rectangleMeasure F 1 n))
    (hΦ : IsRowDominated F n Φ) (η : RatRow F n) :
    fourierCoeff (matrixQuotientHaar F 1 n) (quotientCharacter F ψ hψ n)
        (quotientPeriodization F n Φ hc hΦ) η =
      fourierTransform F n ψ Φ (ratRow F n (-η)) := by
  unfold fourierCoeff fourierTransform
  have hf : Integrable (fun X => Φ X * star (pairingCharacter F ψ n η X))
      (rectangleMeasure F 1 n) := by
    refine hint.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun X => ?_)
    · exact (continuous_star.comp (continuous_pairingCharacter F ψ hψ.1 n η)).aestronglyMeasurable
    · rw [norm_star, norm_pairingCharacter F ψ hψ]
  have hP : ∀ v : RowVector F n, HasSum
      (fun c : rowLattice F n => Φ (c + v) * star (pairingCharacter F ψ n η (c + v)))
      (quotientPeriodization F n Φ hc hΦ (matrixQuotientMap v) *
        star (quotientCharacter F ψ hψ n η (matrixQuotientMap v))) := by
    intro v
    rw [quotientPeriodization_mk, quotientCharacter_mk]
    rw [← (ratRowEquiv F n).hasSum_iff]
    have : (fun C : RatRow F n => Φ ((ratRowEquiv F n C : RowVector F n) + v) *
        star (pairingCharacter F ψ n η ((ratRowEquiv F n C : RowVector F n) + v))) =
        fun C => Φ (ratRow F n C + v) * star (pairingCharacter F ψ n η v) := by
      funext C
      change Φ (ratRow F n C + v) * star (pairingCharacter F ψ n η (ratRow F n C + v)) = _
      rw [pairingCharacter_ratRow_add F ψ hψ.2.2.1]
    rw [Function.comp_def, this]
    exact (summable_periodization F n hΦ v).hasSum.mul_right _
  have hPm : AEStronglyMeasurable (fun x => quotientPeriodization F n Φ hc hΦ x *
      star (quotientCharacter F ψ hψ n η x)) (matrixQuotientHaar F 1 n) :=
    ((quotientPeriodization F n Φ hc hΦ).continuous.mul
      (continuous_star.comp (quotientCharacter F ψ hψ n η).continuous)).aestronglyMeasurable
  rw [← integral_eq_integral_periodization F n _ hf _ hP hPm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  change Φ X * star (pairingCharacter F ψ n η X) = Φ X * ψ (∑ j, X 0 j * ratRow F n (-η) 0 j)
  unfold pairingCharacter
  rw [star_addChar F ψ hψ]
  congr 2
  simp only [ratRow, Matrix.map_apply, Matrix.neg_apply, map_neg, mul_neg,
    Finset.sum_neg_distrib]

/-- **Poisson summation** for continuous integrable dominated functions with dominated Fourier
transform: `Σ_{η ∈ F^n} Φ̂(η) = Σ_{ξ ∈ F^n} Φ(ξ)`, the first series converging absolutely. -/
theorem hasSum_fourierTransform_ratRow [CompactSpace (AdeleQuotient F)] (n : ℕ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hc : Continuous Φ) (hint : Integrable Φ (rectangleMeasure F 1 n))
    (hΦ : IsRowDominated F n Φ) (hΦhat : IsRowDominated F n (fourierTransform F n ψ Φ)) :
    HasSum (fun η : RatRow F n => fourierTransform F n ψ Φ (ratRow F n η))
      (∑' C : RatRow F n, Φ (ratRow F n C)) := by
  have := matrixQuotientHaar_isAddHaarMeasure F 1 n
  have hcoeff := fourierCoeff_quotientPeriodization F n ψ hψ hc hint hΦ
  have hsum : Summable fun η => ‖fourierCoeff (matrixQuotientHaar F 1 n)
      (quotientCharacter F ψ hψ n) (quotientPeriodization F n Φ hc hΦ) η‖ := by
    simp_rw [hcoeff]
    have h0 := summable_norm_periodization F n hΦhat 0
    simp only [add_zero] at h0
    exact (Equiv.neg (RatRow F n)).summable_iff.mpr h0 |>.congr fun η => by simp
  have h := hasSum_fourierCoeff (matrixQuotientHaar F 1 n)
    (isCharacterFamily_quotientCharacter F ψ hψ n) (quotientCharacter_separates F ψ hψ n)
    (integral_quotientCharacter F ψ hψ n) (quotientPeriodization F n Φ hc hΦ) hsum
    (matrixQuotientMap 0)
  have he : ∀ η, quotientCharacter F ψ hψ n η (matrixQuotientMap 0) = 1 := by
    intro η
    rw [quotientCharacter_mk]
    simp [pairingCharacter]
  simp only [he, mul_one, hcoeff, quotientPeriodization_mk] at h
  have hP : periodization F n Φ 0 = ∑' C : RatRow F n, Φ (ratRow F n C) := by
    simp [periodization]
  rw [hP] at h
  rw [← (Equiv.neg (RatRow F n)).hasSum_iff]
  exact h

/-- **Poisson summation on `𝔸^n`** for Schwartz–Bruhat functions. -/
theorem hasSum_poisson [CompactSpace (AdeleQuotient F)] (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) :
    HasSum (fun η : RatRow F n => fourierTransform F n ψ Φ (ratRow F n η))
      (∑' C : RatRow F n, Φ (ratRow F n C)) := by
  obtain ⟨hc, hint, hdom⟩ := schwartzBruhat_properties F n hΦ
  exact hasSum_fourierTransform_ratRow F n ψ hψ hc hint hdom
    (fourierTransform_properties F n ψ hψ hΦ).2

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
