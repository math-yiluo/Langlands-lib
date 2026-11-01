import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusNormalFormStatement
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.PolynomialApproximation

/-! # Proof of the Laurent coefficient normal form for the relative unit annulus -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus

open GeneralizedTateAlgebra Filter
open scoped ZeroAtInfty Topology

namespace NormalForm

/-! ### Coefficients of unit-radius series -/

section Series

variable {σ : Type v} {B : Type w} [NormedCommRing B] [IsUltrametricDist B]

/-- Series are determined by their coefficients. -/
theorem ext_coeff {r : PositivePolyradius σ} {f g : GeneralizedTateAlgebra r B}
    (h : ∀ d, MvPowerSeries.coeff d (series r B f) = MvPowerSeries.coeff d (series r B g)) :
    f = g :=
  Subtype.ext (MvPowerSeries.ext h)

/-- Monomials multiply by adding exponents. -/
theorem monomial_mul_monomial (r : PositivePolyradius σ) (d d' : σ →₀ ℕ) (a b : B) :
    monomial r B d a * monomial r B d' b = monomial r B (d + d') (a * b) :=
  Subtype.ext (MvPowerSeries.monomial_mul_monomial d d' a b)

/-- Two continuous additive maps agreeing on all coefficient monomials agree. -/
theorem eq_of_monomial {r : PositivePolyradius σ} {M : Type*} [AddCommGroup M]
    [TopologicalSpace M] [T2Space M]
    (F G : GeneralizedTateAlgebra r B → M)
    (hFa : ∀ f g, F (f + g) = F f + F g) (hGa : ∀ f g, G (f + g) = G f + G g)
    (hFc : Continuous F) (hGc : Continuous G)
    (h : ∀ d b, F (monomial r B d b) = G (monomial r B d b))
    (f : GeneralizedTateAlgebra r B) : F f = G f := by
  have hs := hasSum_monomials r B f
  have hF := hs.map (AddMonoidHom.mk' F hFa) hFc
  have hG := hs.map (AddMonoidHom.mk' G hGa) hGc
  have key : (⇑(AddMonoidHom.mk' F hFa) ∘
      fun d => monomial r B d (MvPowerSeries.coeff d (series r B f))) =
      ⇑(AddMonoidHom.mk' G hGa) ∘
        fun d => monomial r B d (MvPowerSeries.coeff d (series r B f)) :=
    funext fun d => h d _
  rw [key] at hF
  exact hF.unique hG

/-- A unit-radius coefficient is bounded by the Gauss norm. -/
theorem norm_coeff_le_unit (f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) B)
    (d : σ →₀ ℕ) : ‖MvPowerSeries.coeff d (series _ B f)‖ ≤ ‖f‖ := by
  simpa using weighted_norm_coeff_le (PositivePolyradius.unit σ) B f d

/-- Unit-radius coefficients tend to zero along the cofinite filter. -/
theorem tendsto_coeff_unit (f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) B) :
    Tendsto (fun d => MvPowerSeries.coeff d (series _ B f)) cofinite (𝓝 0) := by
  have h : Tendsto (fun d => ‖MvPowerSeries.coeff d (series _ B f)‖ *
      (PositivePolyradius.unit σ).weight d) cofinite (𝓝 0) := f.property
  simp only [PositivePolyradius.unit_weight, mul_one] at h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h

/-- A single coefficient as an additive map. -/
def coeffHom (r : PositivePolyradius σ) (d : σ →₀ ℕ) : GeneralizedTateAlgebra r B →+ B where
  toFun f := MvPowerSeries.coeff d (series r B f)
  map_zero' := map_zero (MvPowerSeries.coeff d)
  map_add' f g := map_add (MvPowerSeries.coeff d) (series r B f) (series r B g)

theorem continuous_coeff (d : σ →₀ ℕ) :
    Continuous fun f : GeneralizedTateAlgebra (PositivePolyradius.unit σ) B =>
      MvPowerSeries.coeff d (series _ B f) :=
  AddMonoidHomClass.continuous_of_bound (coeffHom (PositivePolyradius.unit σ) d) 1
    fun f => by rw [one_mul]; exact norm_coeff_le_unit f d

end Series

/-! ### Zero-at-infinity coefficient functions on the integers -/

section CZero

variable {E : Type w} [NormedAddCommGroup E]

theorem norm_apply_le (φ : C₀(ℤ, E)) (n : ℤ) : ‖φ n‖ ≤ ‖φ‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact φ.toBCF.norm_coe_le_norm n

theorem norm_le_of_forall (φ : C₀(ℤ, E)) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, ‖φ n‖ ≤ C) :
    ‖φ‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).mpr h

/-- Evaluation at an integer as an additive map. -/
def evalHom (n : ℤ) : C₀(ℤ, E) →+ E where
  toFun φ := φ n
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_eval (n : ℤ) : Continuous fun φ : C₀(ℤ, E) => φ n :=
  AddMonoidHomClass.continuous_of_bound (evalHom (E := E) n) 1
    fun φ => by rw [one_mul]; exact norm_apply_le φ n

theorem tendsto_cofinite (φ : C₀(ℤ, E)) : Tendsto φ cofinite (𝓝 0) := by
  have h := φ.zero_at_infty'
  rwa [cocompact_eq_cofinite] at h

/-- The coefficient function with one nonzero value. -/
def single (m : ℤ) (a : E) : C₀(ℤ, E) where
  toFun n := if n = m then a else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite]
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_cofinite_ne m] with n hn
    simp [hn]

@[simp] theorem single_apply (m n : ℤ) (a : E) : single m a n = if n = m then a else 0 := rfl

end CZero

/-! ### Degrees and exponents -/

/-- The integer degree `i - j` of the monomial `X^i Y^j`. -/
def degree (d : Fin 2 →₀ ℕ) : ℤ := (d 0 : ℤ) - (d 1 : ℤ)

/-- The exponent `X^m` for `0 ≤ m` and `Y^(-m)` for `m < 0`. -/
def exponent (m : ℤ) : Fin 2 →₀ ℕ := Finsupp.single 0 m.toNat + Finsupp.single 1 (-m).toNat

@[simp] theorem exponent_apply_zero (m : ℤ) : exponent m 0 = m.toNat := by
  simp [exponent]

@[simp] theorem exponent_apply_one (m : ℤ) : exponent m 1 = (-m).toNat := by
  simp [exponent]

@[simp] theorem degree_exponent (m : ℤ) : degree (exponent m) = m := by
  simp only [degree, exponent_apply_zero, exponent_apply_one]
  omega

theorem exponent_injective : Function.Injective exponent := fun m m' h => by
  rw [← degree_exponent m, ← degree_exponent m', h]

/-! ### The diagonal coefficient functionals -/

variable (K : Type u) [NormedField K] [IsUltrametricDist K] (A : PresentedAffinoidAlgebra K)

local notation "𝕋" => GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A

section Diagonal

variable [CompleteSpace K]

/-- The sum of the coefficients of `X^i Y^j` with `i - j = n`. -/
def diagonal (n : ℤ) (f : 𝕋) : A :=
  ∑' d, if degree d = n then MvPowerSeries.coeff d (series _ A f) else 0

theorem summable_diagonal (n : ℤ) (f : 𝕋) :
    Summable fun d => if degree d = n then MvPowerSeries.coeff d (series _ A f) else 0 := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_)
    (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_coeff_unit f))
  split_ifs <;> simp

omit [CompleteSpace K] in
theorem norm_diagonal_le (n : ℤ) (f : 𝕋) : ‖diagonal K A n f‖ ≤ ‖f‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg f) fun d => by
    split_ifs
    · exact norm_coeff_le_unit f d
    · simp

theorem diagonal_add (n : ℤ) (f g : 𝕋) :
    diagonal K A n (f + g) = diagonal K A n f + diagonal K A n g := by
  unfold diagonal
  rw [← (summable_diagonal K A n f).tsum_add (summable_diagonal K A n g)]
  apply tsum_congr
  intro d
  change (if degree d = n then MvPowerSeries.coeff d (series _ A f + series _ A g) else 0) = _
  rw [map_add]
  split_ifs <;> simp

/-- The diagonal functional as an additive map. -/
def diagonalHom (n : ℤ) : 𝕋 →+ A := AddMonoidHom.mk' (diagonal K A n) (diagonal_add K A n)

theorem diagonal_sub (n : ℤ) (f g : 𝕋) :
    diagonal K A n (f - g) = diagonal K A n f - diagonal K A n g :=
  map_sub (diagonalHom K A n) f g

theorem continuous_diagonal (n : ℤ) : Continuous (diagonal K A n) :=
  AddMonoidHomClass.continuous_of_bound (diagonalHom K A n) 1
    fun f => by rw [one_mul]; exact norm_diagonal_le K A n f

omit [CompleteSpace K] in
theorem diagonal_monomial (n : ℤ) (d : Fin 2 →₀ ℕ) (a : A) :
    diagonal K A n (monomial _ A d a) = if degree d = n then a else 0 := by
  unfold diagonal
  rw [tsum_eq_single d]
  · simp
  · intro t ht
    simp [coeff_monomial, Ne.symm ht]

/-- Each diagonal functional kills the multiples of `XY - 1`. -/
theorem diagonal_mul_equation (n : ℤ) (h : 𝕋) :
    diagonal K A n (h * (X (PositivePolyradius.unit (Fin 2)) A 0 *
      X (PositivePolyradius.unit (Fin 2)) A 1 - 1)) = 0 := by
  refine eq_of_monomial
    (fun h : 𝕋 => diagonal K A n (h * (X (PositivePolyradius.unit (Fin 2)) A 0 *
      X (PositivePolyradius.unit (Fin 2)) A 1 - 1)))
    (fun _ => (0 : A)) (fun f g => by rw [add_mul, diagonal_add])
    (fun _ _ => (add_zero 0).symm)
    ((continuous_diagonal K A n).comp (continuous_id.mul continuous_const))
    continuous_const (fun d a => ?_) h
  rw [mul_sub, mul_one, X, X, monomial_mul_monomial, monomial_mul_monomial, mul_one,
    mul_one, diagonal_sub, diagonal_monomial, diagonal_monomial]
  have hdeg : degree (d + (Finsupp.single 0 1 + Finsupp.single 1 1)) = degree d := by
    simp [degree]
  rw [hdeg, sub_self]

/-- Each diagonal functional kills the closed ideal generated by `XY - 1`. -/
theorem diagonal_closure (n : ℤ) {f : 𝕋} (hf : f ∈ (Ideal.span (equations K A)).closure) :
    diagonal K A n f = 0 := by
  have hclosed : IsClosed {f : 𝕋 | diagonal K A n f = 0} :=
    isClosed_eq (continuous_diagonal K A n) continuous_const
  have hspan : (Ideal.span (equations K A) : Set 𝕋) ⊆ {f : 𝕋 | diagonal K A n f = 0} := by
    intro f hf
    rw [SetLike.mem_coe, equations, Ideal.mem_span_singleton'] at hf
    obtain ⟨h, rfl⟩ := hf
    exact diagonal_mul_equation K A n h
  exact closure_minimal hspan hclosed hf

end Diagonal

/-! ### The axis section -/

section Section

/-- Place the degree `m` coefficient at the exponent `exponent m`. -/
def sectionCoeff (φ : C₀(ℤ, A)) : (Fin 2 →₀ ℕ) → A := Function.extend exponent φ 0

theorem sectionCoeff_exponent (φ : C₀(ℤ, A)) (m : ℤ) :
    sectionCoeff K A φ (exponent m) = φ m :=
  exponent_injective.extend_apply _ _ m

theorem sectionCoeff_of_not_mem (φ : C₀(ℤ, A)) (d : Fin 2 →₀ ℕ)
    (hd : ¬∃ m, exponent m = d) : sectionCoeff K A φ d = 0 :=
  Function.extend_apply' _ _ d hd

theorem tendsto_sectionCoeff (φ : C₀(ℤ, A)) :
    Tendsto (sectionCoeff K A φ) cofinite (𝓝 0) := by
  intro V hV
  have h := tendsto_cofinite φ hV
  rw [mem_map, mem_cofinite] at h ⊢
  refine (h.image exponent).subset ?_
  intro d hd
  by_cases he : ∃ m, exponent m = d
  · obtain ⟨m, rfl⟩ := he
    refine ⟨m, ?_, rfl⟩
    simpa [sectionCoeff_exponent] using hd
  · refine (hd ?_).elim
    rw [Set.mem_preimage, sectionCoeff_of_not_mem K A φ d he]
    exact mem_of_mem_nhds hV

/-- The section: nonnegative degrees on the `X`-axis, negative degrees on the `Y`-axis. -/
def sectionSeries (φ : C₀(ℤ, A)) : 𝕋 :=
  ⟨sectionCoeff K A φ, by
    show Tendsto (fun d => ‖MvPowerSeries.coeff d (sectionCoeff K A φ)‖ *
      (PositivePolyradius.unit (Fin 2)).weight d) cofinite (𝓝 0)
    simp only [PositivePolyradius.unit_weight, mul_one]
    exact tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_sectionCoeff K A φ)⟩

theorem coeff_sectionSeries (φ : C₀(ℤ, A)) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (series _ A (sectionSeries K A φ)) = sectionCoeff K A φ d := rfl

theorem sectionSeries_add (φ ψ : C₀(ℤ, A)) :
    sectionSeries K A (φ + ψ) = sectionSeries K A φ + sectionSeries K A ψ := by
  refine ext_coeff fun d => ?_
  change sectionCoeff K A (φ + ψ) d = sectionCoeff K A φ d + sectionCoeff K A ψ d
  by_cases he : ∃ m, exponent m = d
  · obtain ⟨m, rfl⟩ := he
    simp [sectionCoeff_exponent]
  · simp [sectionCoeff_of_not_mem K A _ d he]

theorem sectionSeries_smul (c : K) (φ : C₀(ℤ, A)) :
    sectionSeries K A (c • φ) = c • sectionSeries K A φ := by
  refine ext_coeff fun d => ?_
  change sectionCoeff K A (c • φ) d = c • sectionCoeff K A φ d
  by_cases he : ∃ m, exponent m = d
  · obtain ⟨m, rfl⟩ := he
    simp [sectionCoeff_exponent]
  · simp [sectionCoeff_of_not_mem K A _ d he]

theorem norm_sectionSeries_le (φ : C₀(ℤ, A)) : ‖sectionSeries K A φ‖ ≤ ‖φ‖ := by
  refine (norm_le_iff (PositivePolyradius.unit (Fin 2)) A _ (norm_nonneg φ)).mpr fun d => ?_
  rw [PositivePolyradius.unit_weight, mul_one, coeff_sectionSeries]
  by_cases he : ∃ m, exponent m = d
  · obtain ⟨m, rfl⟩ := he
    rw [sectionCoeff_exponent]
    exact norm_apply_le φ m
  · rw [sectionCoeff_of_not_mem K A φ d he, norm_zero]
    exact norm_nonneg φ

theorem sectionSeries_single (m : ℤ) (a : A) :
    sectionSeries K A (single m a) = monomial _ A (exponent m) a := by
  refine ext_coeff fun d => ?_
  rw [coeff_sectionSeries, coeff_monomial]
  by_cases he : ∃ k, exponent k = d
  · obtain ⟨k, rfl⟩ := he
    rw [sectionCoeff_exponent, single_apply]
    simp only [exponent_injective.eq_iff, eq_comm]
  · rw [sectionCoeff_of_not_mem K A _ d he, ite_eq_right (fun h : exponent m = d => he ⟨m, h⟩)]

variable [CompleteSpace K]

omit [CompleteSpace K] in
theorem diagonal_sectionSeries (n : ℤ) (φ : C₀(ℤ, A)) :
    diagonal K A n (sectionSeries K A φ) = φ n := by
  unfold diagonal
  simp only [coeff_sectionSeries]
  have hsupp : Function.support
      (fun d => if degree d = n then sectionCoeff K A φ d else 0) ⊆ Set.range exponent := by
    intro d hd
    by_contra he
    apply hd
    simp only [sectionCoeff_of_not_mem K A φ d he, ite_self]
  rw [← exponent_injective.tsum_eq hsupp]
  simp [sectionCoeff_exponent]

end Section

/-! ### Monomials in the annulus -/

theorem quotientMap_monomial (d : Fin 2 →₀ ℕ) (a : A) :
    quotientMap K A (monomial _ A d a) =
      baseMap K A a * annulusX K A ^ d 0 * annulusY K A ^ d 1 := by
  rw [relative_monomial_eq (K := K)]
  rw [map_mul]
  unfold StrictTateAlgebra.monomialValue
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, map_mul, map_pow,
    map_pow, mul_assoc]
  rfl

theorem baseMap_mul_pow_pow (a : A) (i j : ℕ) :
    baseMap K A a * annulusX K A ^ i * annulusY K A ^ j =
      baseMap K A a * annulusX K A ^ exponent ((i : ℤ) - j) 0 *
        annulusY K A ^ exponent ((i : ℤ) - j) 1 := by
  have key : ∀ p q k : ℕ, baseMap K A a * annulusX K A ^ (p + k) * annulusY K A ^ (q + k) =
      baseMap K A a * annulusX K A ^ p * annulusY K A ^ q := by
    intro p q k
    calc baseMap K A a * annulusX K A ^ (p + k) * annulusY K A ^ (q + k)
        = baseMap K A a * annulusX K A ^ p * annulusY K A ^ q *
            (annulusX K A * annulusY K A) ^ k := by ring
      _ = baseMap K A a * annulusX K A ^ p * annulusY K A ^ q := by
        rw [annulusX_mul_annulusY, one_pow, mul_one]
  rw [exponent_apply_zero, exponent_apply_one]
  have hi : i = ((i : ℤ) - j).toNat + min i j := by omega
  have hj : j = (-((i : ℤ) - j)).toNat + min i j := by omega
  calc baseMap K A a * annulusX K A ^ i * annulusY K A ^ j
      = baseMap K A a * annulusX K A ^ (((i : ℤ) - j).toNat + min i j) *
          annulusY K A ^ ((-((i : ℤ) - j)).toNat + min i j) := by rw [← hi, ← hj]
    _ = _ := key _ _ _

/-! ### The isometric equivalence -/

variable [CompleteSpace K]

/-- The inverse equivalence: the axis section followed by the quotient projection. -/
def toAnnulus : C₀(ℤ, A) →ₗ[K] Algebra K A where
  toFun φ := quotientMap K A (sectionSeries K A φ)
  map_add' φ ψ := by
    rw [sectionSeries_add]
    exact map_add (quotientMap K A).toAlgHom _ _
  map_smul' c φ := by
    rw [sectionSeries_smul, RingHom.id_apply]
    exact map_smul (quotientMap K A).toAlgHom c _

omit [CompleteSpace K] in
theorem toAnnulus_apply (φ : C₀(ℤ, A)) :
    toAnnulus K A φ = quotientMap K A (sectionSeries K A φ) := rfl

theorem norm_toAnnulus (φ : C₀(ℤ, A)) : ‖toAnnulus K A φ‖ = ‖φ‖ := by
  apply le_antisymm
  · exact (norm_quotientMap_le K A _).trans (norm_sectionSeries_le K A φ)
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨g, hg, hgn⟩ := exists_representative_norm_lt K A (toAnnulus K A φ) hε
    have hcoeff : ∀ n, φ n = diagonal K A n g := by
      intro n
      have hmem : g - sectionSeries K A φ ∈ (Ideal.span (equations K A)).closure := by
        rw [← quotientMap_eq_zero_iff]
        rw [map_sub, sub_eq_zero]
        exact hg
      have h0 := diagonal_closure K A n hmem
      rw [diagonal_sub, sub_eq_zero, diagonal_sectionSeries] at h0
      exact h0.symm
    calc ‖φ‖ ≤ ‖g‖ := norm_le_of_forall φ (norm_nonneg g) fun n => by
          rw [hcoeff n]
          exact norm_diagonal_le K A n g
      _ < ‖toAnnulus K A φ‖ + ε := hgn

/-- The section followed by the projection as a linear isometry. -/
def toAnnulusIsometry : C₀(ℤ, A) →ₗᵢ[K] Algebra K A :=
  { toAnnulus K A with norm_map' := norm_toAnnulus K A }

omit [CompleteSpace K] in
theorem toAnnulus_single (m : ℤ) (a : A) :
    toAnnulus K A (single m a) = quotientMap K A (monomial _ A (exponent m) a) := by
  rw [toAnnulus_apply, sectionSeries_single]

omit [CompleteSpace K] in
theorem quotientMap_monomial_mem_range (d : Fin 2 →₀ ℕ) (a : A) :
    quotientMap K A (monomial _ A d a) ∈ LinearMap.range (toAnnulus K A) := by
  refine ⟨single (degree d) a, ?_⟩
  rw [toAnnulus_single, quotientMap_monomial, quotientMap_monomial]
  exact (baseMap_mul_pow_pow K A a (d 0) (d 1)).symm

theorem toAnnulus_surjective : Function.Surjective (toAnnulus K A) := by
  have hclosed : IsClosed (Set.range (toAnnulus K A)) :=
    (toAnnulusIsometry K A).isometry.isClosedEmbedding.isClosed_range
  intro z
  obtain ⟨f, rfl⟩ := quotientMap_surjective K A z
  have hlim := ((BoundedAlgHom.continuous (quotientMap K A)).tendsto f).comp
    (tendsto_truncation (PositivePolyradius.unit (Fin 2)) A f)
  refine hclosed.mem_of_tendsto hlim (Eventually.of_forall fun s => ?_)
  change (quotientMap K A).toAlgHom (truncation _ A s f) ∈ Set.range (toAnnulus K A)
  rw [truncation, map_sum]
  exact LinearMap.mem_range.mp
    (Submodule.sum_mem _ fun d _ => quotientMap_monomial_mem_range K A d _)

/-- The linear isometric equivalence of the normal form. -/
def equiv : Algebra K A ≃ₗᵢ[K] C₀(ℤ, A) :=
  (LinearIsometryEquiv.ofSurjective (toAnnulusIsometry K A) (toAnnulus_surjective K A)).symm

theorem equiv_toAnnulus (φ : C₀(ℤ, A)) : equiv K A (toAnnulus K A φ) = φ := by
  rw [equiv, LinearIsometryEquiv.symm_apply_eq]
  rfl

theorem equiv_monomial (a : A) (i j : ℕ) :
    equiv K A (baseMap K A a * annulusX K A ^ i * annulusY K A ^ j) =
      single ((i : ℤ) - (j : ℤ)) a := by
  rw [baseMap_mul_pow_pow K A a i j, ← quotientMap_monomial, ← toAnnulus_single,
    equiv_toAnnulus]

theorem equiv_quotientMap_monomial (d : Fin 2 →₀ ℕ) (a : A) :
    equiv K A (quotientMap K A (monomial _ A d a)) = single ((d 0 : ℤ) - (d 1 : ℤ)) a := by
  rw [quotientMap_monomial, equiv_monomial]

theorem continuous_equiv_apply (n : ℤ) : Continuous fun z : Algebra K A => equiv K A z n :=
  (continuous_eval n).comp (equiv K A).continuous

theorem positive_monomial (d : Fin 1 →₀ ℕ) (a : A) :
    positive K A (monomial _ A d a) = baseMap K A a * annulusX K A ^ d 0 := by
  rw [positive_apply, evaluateCoefficients_monomial]
  unfold StrictTateAlgebra.monomialValue
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_one]

theorem negative_monomial (d : Fin 1 →₀ ℕ) (a : A) :
    negative K A (monomial _ A d a) = baseMap K A a * annulusY K A ^ d 0 := by
  rw [negative_apply, evaluateCoefficients_monomial]
  unfold StrictTateAlgebra.monomialValue
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_one]

theorem exists_single_eq (d : Fin 1 →₀ ℕ) : ∃ k, d = Finsupp.single 0 k :=
  ⟨d 0, Finsupp.ext fun i => by fin_cases i; simp⟩

end NormalForm

open NormalForm in
/-- The Laurent coefficient normal form of the actual relative unit annulus. -/
theorem normal_form : NormalFormStatement.{u} := by
  intro K _ _ _ A
  refine ⟨equiv K A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a i j n
    rw [equiv_monomial, single_apply]
  · intro z n
    obtain ⟨g, rfl⟩ := quotientMap_surjective K A z
    refine eq_of_monomial
      (fun g => equiv K A (annulusX K A * quotientMap K A g) n)
      (fun g => equiv K A (quotientMap K A g) (n - 1)) ?_ ?_ ?_ ?_ ?_ g
    · intro f g
      rw [map_add, mul_add, map_add]
      rfl
    · intro f g
      rw [map_add (quotientMap K A).toAlgHom f g, map_add (equiv K A)]
      rfl
    · exact (continuous_equiv_apply K A n).comp
        (continuous_const.mul (BoundedAlgHom.continuous (quotientMap K A)))
    · exact (continuous_equiv_apply K A (n - 1)).comp
        (BoundedAlgHom.continuous (quotientMap K A))
    · intro d a
      rw [quotientMap_monomial,
        show annulusX K A * (baseMap K A a * annulusX K A ^ d 0 * annulusY K A ^ d 1) =
          baseMap K A a * annulusX K A ^ (d 0 + 1) * annulusY K A ^ d 1 by ring,
        equiv_monomial, equiv_monomial, single_apply, single_apply]
      exact if_congr (by push_cast; omega) rfl rfl
  · intro z n
    obtain ⟨g, rfl⟩ := quotientMap_surjective K A z
    refine eq_of_monomial
      (fun g => equiv K A (annulusY K A * quotientMap K A g) n)
      (fun g => equiv K A (quotientMap K A g) (n + 1)) ?_ ?_ ?_ ?_ ?_ g
    · intro f g
      rw [map_add, mul_add, map_add]
      rfl
    · intro f g
      rw [map_add (quotientMap K A).toAlgHom f g, map_add (equiv K A)]
      rfl
    · exact (continuous_equiv_apply K A n).comp
        (continuous_const.mul (BoundedAlgHom.continuous (quotientMap K A)))
    · exact (continuous_equiv_apply K A (n + 1)).comp
        (BoundedAlgHom.continuous (quotientMap K A))
    · intro d a
      rw [quotientMap_monomial,
        show annulusY K A * (baseMap K A a * annulusX K A ^ d 0 * annulusY K A ^ d 1) =
          baseMap K A a * annulusX K A ^ d 0 * annulusY K A ^ (d 1 + 1) by ring,
        equiv_monomial, equiv_monomial, single_apply, single_apply]
      exact if_congr (by push_cast; omega) rfl rfl
  · intro b z n
    obtain ⟨g, rfl⟩ := quotientMap_surjective K A z
    refine eq_of_monomial
      (fun g => equiv K A (baseMap K A b * quotientMap K A g) n)
      (fun g => b * equiv K A (quotientMap K A g) n) ?_ ?_ ?_ ?_ ?_ g
    · intro f g
      rw [map_add, mul_add, map_add]
      rfl
    · intro f g
      rw [map_add, map_add, ZeroAtInftyContinuousMap.add_apply, mul_add]
    · exact (continuous_equiv_apply K A n).comp
        (continuous_const.mul (BoundedAlgHom.continuous (quotientMap K A)))
    · exact continuous_const.mul ((continuous_equiv_apply K A n).comp
        (BoundedAlgHom.continuous (quotientMap K A)))
    · intro d a
      rw [quotientMap_monomial,
        show baseMap K A b * (baseMap K A a * annulusX K A ^ d 0 * annulusY K A ^ d 1) =
          baseMap K A (b * a) * annulusX K A ^ d 0 * annulusY K A ^ d 1 by
            rw [show baseMap K A (b * a) = baseMap K A b * baseMap K A a from
              map_mul (baseMap K A).toAlgHom b a]
            ring,
        equiv_monomial, equiv_monomial, single_apply, single_apply, mul_ite, mul_zero]
  · intro h n
    refine eq_of_monomial
      (fun h => equiv K A (positive K A h) n)
      (fun h => if 0 ≤ n then MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n.toNat)
        (series (PositivePolyradius.unit (Fin 1)) A h) else 0) ?_ ?_ ?_ ?_ ?_ h
    · intro f g
      rw [map_add, map_add]
      rfl
    · intro f g
      split_ifs
      · exact map_add (MvPowerSeries.coeff _) _ _
      · exact (add_zero 0).symm
    · exact (continuous_equiv_apply K A n).comp (BoundedAlgHom.continuous (positive K A))
    · by_cases hn : 0 ≤ n
      · simp only [hn, ite_true]
        exact continuous_coeff _
      · simp only [hn, ite_false]
        exact continuous_const
    · intro d a
      obtain ⟨k, rfl⟩ := exists_single_eq d
      rw [positive_monomial, coeff_monomial, Finsupp.single_eq_same,
        show baseMap K A a * annulusX K A ^ k =
          baseMap K A a * annulusX K A ^ k * annulusY K A ^ 0 by rw [pow_zero, mul_one],
        equiv_monomial, single_apply]
      by_cases h0 : 0 ≤ n
      · rw [ite_eq_left h0]
        exact if_congr (by rw [(Finsupp.single_injective _).eq_iff]; omega) rfl rfl
      · rw [ite_eq_right h0]
        exact ite_eq_right (by omega)
  · intro h n
    refine eq_of_monomial
      (fun h => equiv K A (negative K A h) n)
      (fun h => if n ≤ 0 then MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) (-n).toNat)
        (series (PositivePolyradius.unit (Fin 1)) A h) else 0) ?_ ?_ ?_ ?_ ?_ h
    · intro f g
      rw [map_add, map_add]
      rfl
    · intro f g
      split_ifs
      · exact map_add (MvPowerSeries.coeff _) _ _
      · exact (add_zero 0).symm
    · exact (continuous_equiv_apply K A n).comp (BoundedAlgHom.continuous (negative K A))
    · by_cases hn : n ≤ 0
      · simp only [hn, ite_true]
        exact continuous_coeff _
      · simp only [hn, ite_false]
        exact continuous_const
    · intro d a
      obtain ⟨k, rfl⟩ := exists_single_eq d
      rw [negative_monomial, coeff_monomial, Finsupp.single_eq_same,
        show baseMap K A a * annulusY K A ^ k =
          baseMap K A a * annulusX K A ^ 0 * annulusY K A ^ k by rw [pow_zero, mul_one],
        equiv_monomial, single_apply]
      by_cases h0 : n ≤ 0
      · rw [ite_eq_left h0]
        exact if_congr (by rw [(Finsupp.single_injective _).eq_iff]; omega) rfl rfl
      · rw [ite_eq_right h0]
        exact ite_eq_right (by omega)

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus
