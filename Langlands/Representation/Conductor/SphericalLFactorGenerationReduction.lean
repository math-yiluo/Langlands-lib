import Langlands.Representation.Conductor.SphericalCorankOneConvergenceStatement
import Langlands.Representation.Conductor.UnramifiedCorankOneLaurentStatement
import Langlands.Representation.Conductor.OrderedUnramifiedCorankOneGenerationStatement
import Langlands.Representation.Conductor.OrderedUnramifiedWhittakerStatement
import Langlands.Representation.Conductor.SphericalPolynomial
import Langlands.Representation.Conductor.SphericalDegree
import Langlands.Representation.Conductor.EssentialScaledUniqueness
import Langlands.Representation.CyclicSpan
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.Representation.RankinSelberg.UnramifiedTwistIntegrals
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Reduction of the spherical L-factor generation facts

Jacquet 2012, section 1 (printed pages 517-519), derives his Lemma 4 from three facts:
the cyclicity of the spherical section of `I(x)` for norm-ordered `x` (his Lemma 1), the
realization of that section by `W(x; ψ̄)` in the Whittaker model of `I(x)` (his Lemma 2),
and the generation of `∏ i, P(x_i q^(-s))⁻¹` by finite sums of corank-one integrals of
`π × I(x)` for norm-ordered `x` (his Lemma 3, quoted from JPSS 1983). Translating the
second argument by `g` multiplies the integral by `|det g|^(-(s - 1/2))` and translates
the first argument, so Lemma 3 becomes a statement about `W(x; ψ̄)` alone. The
symmetry of `W(x; ψ̄)` in `x` removes the ordering.

This module proves `SphericalLFactorGenerationStatement` from the convergence input
`SphericalCorankOneConvergenceStatement` (JPSS Theorem (2.7)), the Laurent input
`UnramifiedCorankOneLaurentStatement` (JPSS Theorem (3.1)(ii)), the generation input
`OrderedUnramifiedCorankOneGenerationStatement` (Jacquet's Lemma 3), and the two published
ordered-unramified statements (`sphericalLFactorGeneration_of_ordered`).
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial QuotientIntegration
open Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF uV uΓ

/-! ### Symmetry of the spherical Whittaker function -/

section Symmetry

/-- The Schur value is symmetric in the Satake parameters. -/
theorem satakeSchur_comp_perm {n : ℕ} (x : Fin (n + 1) → ℂˣ) (σ : Equiv.Perm (Fin (n + 1)))
    (lam : Fin (n + 1) → ℤ) : satakeSchur (x ∘ σ) lam = satakeSchur x lam := by
  unfold satakeSchur
  congr 1
  · congr 1
    exact Equiv.prod_comp σ (fun i => (x i : ℂ))
  · have hs := jacobiTrudi_isSymmetric ℂ (fun i => lam i - lam (Fin.last n)) σ
    conv_rhs => rw [← hs]
    rw [MvPolynomial.eval_rename]
    rfl

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ}

/-- The spherical Whittaker function is symmetric in the Satake parameters. -/
theorem sphericalWhittaker_comp_perm (hϖ : IsUniformizingElement v ϖ)
    (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ) (x : Fin (n + 1) → ℂˣ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    sphericalWhittaker hϖ θ q (x ∘ σ) = sphericalWhittaker hϖ θ q x := by
  unfold sphericalWhittaker
  simp only [satakeSchur_comp_perm]

end Symmetry

theorem inverseSphericalWhittaker_comp_perm {F : Type uF} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {ψ : UnitaryAdditiveCharacter F} {n : ℕ}
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (q : ℕ)
    (x : Fin (n + 1) → ℂˣ) (σ : Equiv.Perm (Fin (n + 1))) :
    inverseSphericalWhittaker hψ hϖ q (x ∘ σ) = inverseSphericalWhittaker hψ hϖ q x :=
  Subtype.ext (sphericalWhittaker_comp_perm hϖ _ q x σ)

/-! ### Finite combinations of right translates in the second argument -/

section Translation

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- Pointwise form: if `W'(h) = ∑_g c_g X₀(h g)` and `W_g` is the right translate of `W`
by `diag(g⁻¹, 1)`, the corank-one integrand of `(W, W')` is the sum of the translated
integrands of `(W_g, X₀)`, weighted by `c_g |det g|^(-(s - 1/2))`. -/
theorem corankOneIntegrand_eq_sum_translate (W : WhittakerFunctions ψ (n + 1))
    (W' X₀ : InverseWhittakerFunctions ψ n) (T : Finset (Langlands.GeneralLinear (n + 1) F))
    (c : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hW' : ∀ g, W'.val g = ∑ t ∈ T, c t * X₀.val (g * t))
    (Wt : Langlands.GeneralLinear (n + 1) F → WhittakerFunctions ψ (n + 1))
    (hWt : ∀ t g, (Wt t).val (rankInclusion 1 g) = W.val (rankInclusion 1 (g * t⁻¹)))
    (s : ℂ) :
    corankOneIntegrand ψ abv W W' s = fun y => ∑ t ∈ T,
      (c t * determinantWeight abv t⁻¹ (s - 1 / 2)) *
        corankOneIntegrand ψ abv (Wt t) X₀ s
          (rightTranslate (upperUnipotent (n + 1) F) t y) := by
  funext y
  induction y using Quotient.inductionOn with
  | h g =>
    rw [corankOneIntegrand_mk, hW', Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [rightTranslate_mk, corankOneIntegrand_mk, hWt, mul_inv_cancel_right]
    have hd : determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv (g * t) (s - 1 / 2) * determinantWeight abv t⁻¹ (s - 1 / 2) := by
      rw [← determinantWeight_mul, mul_inv_cancel_right]
    rw [hd]
    ring

/-- The corank-one integral of a finite combination of right translates of `X₀`, when
each translated first argument converges against `X₀`. -/
theorem corankOneIntegral_eq_sum_translate
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
    {μ : Measure (LeftUnipotentQuotient n F)}
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (W : WhittakerFunctions ψ (n + 1))
    (W' X₀ : InverseWhittakerFunctions ψ n) (T : Finset (Langlands.GeneralLinear (n + 1) F))
    (c : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hW' : ∀ g, W'.val g = ∑ t ∈ T, c t * X₀.val (g * t))
    (Wt : Langlands.GeneralLinear (n + 1) F → WhittakerFunctions ψ (n + 1))
    (hWt : ∀ t g, (Wt t).val (rankInclusion 1 g) = W.val (rankInclusion 1 (g * t⁻¹)))
    (s : ℂ) (hconv : ∀ t ∈ T, CorankOneConverges ψ abv μ (Wt t) X₀ s) :
    corankOneIntegral ψ abv μ W W' s = ∑ t ∈ T,
      (c t * determinantWeight abv t⁻¹ (s - 1 / 2)) *
        corankOneIntegral ψ abv μ (Wt t) X₀ s := by
  have he := corankOneIntegrand_eq_sum_translate ψ abv W W' X₀ T c hW' Wt hWt s
  unfold corankOneIntegral
  rw [he, integral_finsetSum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_const_mul,
      (hμ.right_invariant t).integral_comp
        (rightTranslate (upperUnipotent (n + 1) F) t).measurableEmbedding]
  · intro t ht
    exact (((hμ.right_invariant t).integrable_comp_emb
      (rightTranslate (upperUnipotent (n + 1) F) t).measurableEmbedding).mpr
        (hconv t ht)).const_mul _

end Translation

/-! ### Cyclic vectors and coefficient models -/

section Cyclic

variable {G : Type*} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If `v₀` generates `ρ`, every function in the coefficient model of `ℓ` is a finite
combination of right translates of the coefficient of `v₀`. -/
theorem exists_finset_translate_of_cyclic (ρ : Representation ℂ G V)
    (ℓ : functionals N θ ρ) (v₀ : V)
    (hcyc : ∀ S : Subrepresentation ρ, v₀ ∈ S → S = ⊤)
    (f : (coefficientModel ρ ℓ).toSubmodule) :
    ∃ (T : Finset G) (c : G → ℂ), ∀ g,
      f.val.val g = ∑ t ∈ T, c t * (coefficientMap ρ ℓ v₀).val (g * t) := by
  classical
  obtain ⟨v, hv⟩ := f.property
  have htop := hcyc (Cyclic.orbitSpan ρ v₀) (Cyclic.mem_orbitSpan ρ v₀)
  have hmem : v ∈ (Cyclic.orbitSpan ρ v₀).toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  refine ⟨c.support, c, fun g => ?_⟩
  have hfg : f.val.val g = ℓ.val (ρ g v) := by
    rw [← hv]
    rfl
  rw [hfg, ← hc, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, map_smul, smul_eq_mul]
  congr 1
  change ℓ.val (ρ g (ρ t v₀)) = ℓ.val (ρ (g * t) v₀)
  rw [map_mul, Module.End.mul_apply]

end Cyclic

/-! ### Spans of spherical integrals -/

section Span

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient n F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
  (ℓ : glFunctionals ψ (n + 1) π) (X₀ : InverseWhittakerFunctions ψ n)

/-- `R` agrees on a right half-plane with a finite sum `∑_j q^(-e_j s) Ψ(s, W_j, X₀)`
with `W_j` in the model of `ℓ`. -/
def IsSphericalIntegralSpan (R : ℂ → ℂ) : Prop :=
  ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule) (e : Fin k → ℤ) (a : ℝ),
    ∀ s : ℂ, a < s.re →
      R s = ∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val X₀ s

variable {q ψ abv μ π ℓ X₀}

theorem IsSphericalIntegralSpan.zero :
    IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ (fun _ => 0) :=
  ⟨0, Fin.elim0, Fin.elim0, 0, fun _ _ => by simp⟩

theorem IsSphericalIntegralSpan.single (w : (coefficientModel π ℓ).toSubmodule) :
    IsSphericalIntegralSpan q ψ abv μ π ℓ X₀
      (fun s => corankOneIntegral ψ abv μ w.val X₀ s) :=
  ⟨1, fun _ => w, fun _ => 0, 0, fun _ _ => by simp⟩

theorem IsSphericalIntegralSpan.add {R R' : ℂ → ℂ}
    (hR : IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ R)
    (hR' : IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ R') :
    IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ (fun s => R s + R' s) := by
  obtain ⟨k, W, e, a, h⟩ := hR
  obtain ⟨k', W', e', a', h'⟩ := hR'
  refine ⟨k + k', Fin.append W W', Fin.append e e', max a a', fun s hs => ?_⟩
  show R s + R' s = _
  rw [h s (lt_of_le_of_lt (le_max_left _ _) hs), h' s (lt_of_le_of_lt (le_max_right _ _) hs),
    Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem IsSphericalIntegralSpan.finset_sum {ι : Type*} (T : Finset ι) {R : ι → ℂ → ℂ}
    (hR : ∀ i ∈ T, IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ (R i)) :
    IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ (fun s => ∑ i ∈ T, R i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using IsSphericalIntegralSpan.zero
  | @insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hR i (Finset.mem_insert_self i T)).add
      (ih fun j hj => hR j (Finset.mem_insert_of_mem hj))

theorem IsSphericalIntegralSpan.congr {R R' : ℂ → ℂ}
    (hR : IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ R) {b : ℝ}
    (hRR' : ∀ s : ℂ, b < s.re → R' s = R s) :
    IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ R' := by
  obtain ⟨k, W, e, a, h⟩ := hR
  refine ⟨k, W, e, max a b, fun s hs => ?_⟩
  rw [hRR' s (lt_of_le_of_lt (le_max_right _ _) hs), h s (lt_of_le_of_lt (le_max_left _ _) hs)]

theorem IsSphericalIntegralSpan.monomial_smul (κ : ℂ) (m : ℤ)
    (w : (coefficientModel π ℓ).toSubmodule) :
    IsSphericalIntegralSpan q ψ abv μ π ℓ X₀
      (fun s => (κ * spectralPoint q s ^ m) * corankOneIntegral ψ abv μ w.val X₀ s) := by
  refine ⟨1, fun _ => κ • w, fun _ => m, 0, fun s _ => ?_⟩
  simp only [Finset.univ_unique, Finset.sum_singleton, SetLike.val_smul,
    corankOneIntegral_smul]
  ring

end Span

/-! ### Clause 3 for ordered parameters -/

section Ordered

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V}
  {ℓ : glFunctionals ψ (n + 1) π}

omit [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)] in
/-- The determinant weight at `s - 1/2` is a constant times an integral power of
`q^(-s)`. -/
theorem exists_determinantWeight_eq_monomial (h : IsJacquetNormalization q ψ abv ϖ μ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    ∃ (κ : ℂ) (m : ℤ), ∀ s : ℂ,
      determinantWeight abv g (s - 1 / 2) = κ * spectralPoint q s ^ m := by
  have hq : 0 < q := residueCardinality_pos h.residueCardinality
  refine ⟨determinantWeight abv g (-(1 / 2)), ∑ i, exponent h.uniformizer g i, fun s => ?_⟩
  have habs : abv (Matrix.det g.val) = (q : ℝ) ^ (-(∑ i, exponent h.uniformizer g i)) := by
    rw [abv_det_eq_zpow_exponent abv h.uniformizer h.abv_unit g, h.abv_uniformizer, inv_zpow,
      zpow_neg]
  rw [sub_eq_add_neg, determinantWeight_add,
    determinantWeight_eq_spectralPoint_zpow q hq abv g _ habs s, mul_comm]

omit [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)] in
/-- Every integral of `π × I(x)` against the Whittaker model of the realizing functional
lies in the span of the integrals against `W(x; ψ̄)`. -/
theorem isSphericalIntegralSpan_of_model (h : IsJacquetNormalization q ψ abv ϖ μ)
    (x : Fin (n + 1) → ℂˣ)
    (hconv : ∀ (w : (coefficientModel π ℓ).toSubmodule), ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    (ℓ' : glInverseFunctionals ψ n (principalSeries h.uniformizer n h.residueCardinality x))
    (hcyc : ∀ S : Subrepresentation (principalSeries h.uniformizer n h.residueCardinality x),
      sphericalSection h.uniformizer n h.residueCardinality x ∈ S → S = ⊤)
    (hsph : ∀ g : Langlands.GeneralLinear (n + 1) F,
      (coefficientMap (principalSeries h.uniformizer n h.residueCardinality x) ℓ'
        (sphericalSection h.uniformizer n h.residueCardinality x)).val g =
          sphericalWhittaker h.uniformizer (inverseStandardCharacter ψ n) q x g)
    (w : (coefficientModel π ℓ).toSubmodule)
    (w' : (coefficientModel (principalSeries h.uniformizer n h.residueCardinality x)
      ℓ').toSubmodule) :
    IsSphericalIntegralSpan q ψ abv μ π ℓ
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)
      (fun s => corankOneIntegral ψ abv μ w.val w'.val s) := by
  classical
  have := h.borel
  set X₀ := inverseSphericalWhittaker h.conductor.1 h.uniformizer q x
  obtain ⟨T, c, hc⟩ := exists_finset_translate_of_cyclic _ ℓ' _ hcyc w'
  have hW' : ∀ g, w'.val.val g = ∑ t ∈ T, c t * X₀.val (g * t) := by
    intro g
    rw [hc g]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hsph]
    rfl
  let Wt : Langlands.GeneralLinear (n + 1) F → (coefficientModel π ℓ).toSubmodule :=
    fun t => modelRepresentation π ℓ (rankInclusion 1 t⁻¹) w
  have hWt : ∀ t g, (Wt t).val.val (rankInclusion 1 g) =
      w.val.val (rankInclusion 1 (g * t⁻¹)) := by
    intro t g
    change w.val.val (rankInclusion 1 g * rankInclusion 1 t⁻¹) = _
    rw [map_mul]
  choose a ha using fun t => hconv (Wt t)
  choose κ m hκm using fun t => exists_determinantWeight_eq_monomial h (t⁻¹)
  have hsum : IsSphericalIntegralSpan q ψ abv μ π ℓ X₀ (fun s => ∑ t ∈ T,
      ((c t * κ t) * spectralPoint q s ^ m t) *
        corankOneIntegral ψ abv μ (Wt t).val X₀ s) := by
    refine IsSphericalIntegralSpan.finset_sum T fun t _ => ?_
    exact IsSphericalIntegralSpan.monomial_smul (c t * κ t) (m t) (Wt t)
  refine hsum.congr (b := ∑ t ∈ T, |a t|) fun s hs => ?_
  have hconvT : ∀ t ∈ T, CorankOneConverges ψ abv μ (Wt t).val X₀ s := by
    intro t ht
    refine ha t s (lt_of_le_of_lt ?_ hs)
    exact (le_abs_self (a t)).trans
      (Finset.single_le_sum (f := fun t => |a t|) (fun t _ => abs_nonneg (a t)) ht)
  rw [corankOneIntegral_eq_sum_translate ψ abv h.measure w.val w'.val X₀ T c hW'
    (fun t => (Wt t).val) hWt s hconvT]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hκm t s]
  ring


omit [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)] in
/-- The spherical Whittaker function `W(x; ψ̄)`, as an element of the model of a
realizing functional `ℓ'` of `I(x)`. -/
theorem exists_model_eq_inverseSphericalWhittaker (h : IsJacquetNormalization q ψ abv ϖ μ)
    (x : Fin (n + 1) → ℂˣ)
    (ℓ' : glInverseFunctionals ψ n (principalSeries h.uniformizer n h.residueCardinality x))
    (hsph : ∀ g : Langlands.GeneralLinear (n + 1) F,
      (coefficientMap (principalSeries h.uniformizer n h.residueCardinality x) ℓ'
        (sphericalSection h.uniformizer n h.residueCardinality x)).val g =
          sphericalWhittaker h.uniformizer (inverseStandardCharacter ψ n) q x g) :
    ∃ w' : (coefficientModel (principalSeries h.uniformizer n h.residueCardinality x)
        ℓ').toSubmodule,
      w'.val = inverseSphericalWhittaker h.conductor.1 h.uniformizer q x :=
  ⟨⟨_, sphericalSection h.uniformizer n h.residueCardinality x, rfl⟩,
    Subtype.ext (funext hsph)⟩

/-- Clause 2 of the target for norm-ordered parameters. -/
theorem laurent_of_ordered (h : IsJacquetNormalization q ψ abv ϖ μ)
    (hπ : IsGeneric ψ (n + 1) π) (hℓ : ℓ.val ≠ 0) {P : ℂ[X]}
    (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P)
    (hlau : UnramifiedCorankOneLaurentStatement.{uF, uV})
    (hreal : OrderedUnramifiedWhittakerRealizationStatement.{uF})
    (x : Fin (n + 1) → ℂˣ) (hx : Monotone (fun i => ‖(x i : ℂ)‖))
    (w : (coefficientModel π ℓ).toSubmodule)
    (hconv : ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) :
    ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
      corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s *
        (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
      spectralPoint q s ^ N * Q.eval (spectralPoint q s) := by
  obtain ⟨ℓ', hℓ'0, -, hsph⟩ :=
    hreal F ϖ h.uniformizer n q h.residueCardinality x hx ψ h.conductor
  obtain ⟨w', hw'⟩ := exists_model_eq_inverseSphericalWhittaker h x ℓ' hsph
  rw [← hw'] at hconv ⊢
  exact hlau F n q ψ abv ϖ μ h π hπ ℓ hℓ P hP x ℓ' hℓ'0 w w' hconv

/-- Clause 3 of the target for norm-ordered parameters. -/
theorem generation_of_ordered (h : IsJacquetNormalization q ψ abv ϖ μ)
    (hπ : IsGeneric ψ (n + 1) π) (hℓ : ℓ.val ≠ 0) {P : ℂ[X]}
    (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P)
    (hgen : OrderedUnramifiedCorankOneGenerationStatement.{uF, uV})
    (hcyc : OrderedUnramifiedSphericalCyclicityStatement.{uF})
    (hreal : OrderedUnramifiedWhittakerRealizationStatement.{uF})
    (x : Fin (n + 1) → ℂˣ) (hx : Monotone (fun i => ‖(x i : ℂ)‖))
    (hconv : ∀ (w : (coefficientModel π ℓ).toSubmodule), ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) :
    ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule) (e : Fin k → ℤ) (a : ℝ),
      ∀ s : ℂ, a < s.re →
        (∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) *
          (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1 := by
  obtain ⟨ℓ', hℓ'0, -, hsph⟩ :=
    hreal F ϖ h.uniformizer n q h.residueCardinality x hx ψ h.conductor
  have hcyc' := hcyc F ϖ h.uniformizer n q h.residueCardinality x hx
  obtain ⟨k, W, W', a, hsum⟩ := hgen F n q ψ abv ϖ μ h π hπ ℓ hℓ P hP x hx ℓ' hℓ'0
  have hspan := IsSphericalIntegralSpan.finset_sum (q := q) (X₀ :=
      inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) Finset.univ
    (R := fun j s => corankOneIntegral ψ abv μ (W j).val (W' j).val s)
    fun j _ => isSphericalIntegralSpan_of_model h x hconv ℓ' hcyc' hsph (W j) (W' j)
  obtain ⟨k₂, W₂, e₂, a₂, h₂⟩ := hspan
  refine ⟨k₂, W₂, e₂, max a a₂, fun s hs => ?_⟩
  rw [← h₂ s (lt_of_le_of_lt (le_max_right _ _) hs)]
  exact hsum s (lt_of_le_of_lt (le_max_left _ _) hs)

end Ordered

/-! ### Removing the ordering -/

/-- A permutation sorting the Satake parameters by norm. -/
theorem exists_perm_monotone_norm {n : ℕ} (x : Fin (n + 1) → ℂˣ) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), Monotone (fun i => ‖((x ∘ σ) i : ℂ)‖) :=
  ⟨Tuple.sort (fun i => ‖(x i : ℂ)‖), Tuple.monotone_sort (fun i => ‖(x i : ℂ)‖)⟩

theorem prod_comp_perm (P : ℂ[X]) {n : ℕ} (x : Fin (n + 1) → ℂˣ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    ∏ i, P.comp (C (((x ∘ σ) i : ℂˣ) : ℂ) * X) = ∏ i, P.comp (C (x i : ℂ) * X) :=
  Equiv.prod_comp σ (fun i => P.comp (C (x i : ℂ) * X))

/-- The spherical L-factor generation facts of Jacquet 2012, section 1, from the
convergence statement, the Laurent statement, the ordered generation statement, and
Jacquet's Lemmas 1 and 2. -/
theorem sphericalLFactorGeneration_of_ordered
    (hconv : SphericalCorankOneConvergenceStatement.{uF, uV})
    (hlau : UnramifiedCorankOneLaurentStatement.{uF, uV})
    (hgen : OrderedUnramifiedCorankOneGenerationStatement.{uF, uV})
    (hcyc : OrderedUnramifiedSphericalCyclicityStatement.{uF})
    (hreal : OrderedUnramifiedWhittakerRealizationStatement.{uF}) :
    SphericalLFactorGenerationStatement.{uF, uV} := by
  intro F _ _ _ _ n _ _ _ _ _ _ _ _ q ψ abv ϖ μ h V _ _ π hπ ℓ hℓ
  obtain ⟨P, hP, hc⟩ := hconv F n q ψ abv ϖ μ h π hπ ℓ hℓ
  refine ⟨P, hP, hc, fun w x => ?_, fun x => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_perm_monotone_norm x
    obtain ⟨a, N, Q, hQ⟩ := laurent_of_ordered h hπ hℓ hP hlau hreal (x ∘ σ) hσ w (by
      rw [inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ]
      exact hc w x)
    refine ⟨a, N, Q, fun s hs => ?_⟩
    rw [← inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ,
      ← prod_comp_perm P x σ]
    exact hQ s hs
  · obtain ⟨σ, hσ⟩ := exists_perm_monotone_norm x
    obtain ⟨k, W, e, a, hW⟩ := generation_of_ordered h hπ hℓ hP hgen hcyc hreal (x ∘ σ) hσ
      (fun w => by
        rw [inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ]
        exact hc w x)
    refine ⟨k, W, e, a, fun s hs => ?_⟩
    rw [← inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ,
      ← prod_comp_perm P x σ]
    exact hW s hs

end Langlands.Conductor
