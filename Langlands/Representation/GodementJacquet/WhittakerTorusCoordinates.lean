import Langlands.Representation.RankinSelberg.Measures
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Tail-product coordinates on the diagonal torus

The coordinates `x ↦ τ(x)`, `τ(x)_j = ∏_{k ≥ j} x_k`, on `(n + 1)`-tuples
turn the adjacent ratios `a_j / a_(j+1)` of `a = τ(x)` into the first `n`
coordinates of `x`, and the determinant `∏_j a_j` into `∏_k x_k^(k+1)`.
On the units of a nonarchimedean local field they preserve the product of the
normalized multiplicative Haar measures. See the paired Markdown.
-/

noncomputable section

namespace Langlands.GodementJacquet.WhittakerTorus

open MeasureTheory HarmonicAnalysis RankinSelberg
open scoped BigOperators

section Algebra

variable {M : Type*} [CommMonoid M] {n : ℕ}

/-- Tail products `τ(x)_j = ∏_{k ≥ j} x_k` of an `(n + 1)`-tuple. -/
def tailProd (x : Fin (n + 1) → M) (j : Fin (n + 1)) : M :=
  ∏ k ∈ Finset.univ.filter (fun k => j ≤ k), x k

theorem tailProd_last (x : Fin (n + 1) → M) : tailProd x (Fin.last n) = x (Fin.last n) := by
  have h : Finset.univ.filter (fun k : Fin (n + 1) => Fin.last n ≤ k) = {Fin.last n} := by
    ext k
    simp [Fin.last_le_iff]
  rw [tailProd, h, Finset.prod_singleton]

theorem tailProd_castSucc (x : Fin (n + 1) → M) (i : Fin n) :
    tailProd x i.castSucc = x i.castSucc * tailProd x i.succ := by
  have h : Finset.univ.filter (fun k : Fin (n + 1) => i.castSucc ≤ k) =
      insert i.castSucc (Finset.univ.filter (fun k : Fin (n + 1) => i.succ ≤ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def,
      Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  rw [tailProd, h, Finset.prod_insert (by simp [Fin.le_def]), tailProd]

theorem tailProd_mul (x y : Fin (n + 1) → M) :
    tailProd (x * y) = tailProd x * tailProd y := by
  funext j
  simp [tailProd, Finset.prod_mul_distrib]

theorem tailProd_one : tailProd (1 : Fin (n + 1) → M) = 1 := by
  funext j
  simp [tailProd]

/-- Monoid homomorphisms commute with tail products. -/
theorem map_tailProd {N : Type*} [CommMonoid N] {H : Type*} [FunLike H M N]
    [MonoidHomClass H M N] (f : H) (x : Fin (n + 1) → M) (j : Fin (n + 1)) :
    f (tailProd x j) = tailProd (fun k => f (x k)) j :=
  map_prod f _ _

/-- The product of all tail products is `∏_k x_k^(k+1)`. -/
theorem prod_tailProd (x : Fin (n + 1) → M) :
    ∏ j, tailProd x j = ∏ k, x k ^ ((k : ℕ) + 1) := by
  unfold tailProd
  rw [Finset.prod_comm' (t' := Finset.univ)
    (s' := fun k => Finset.univ.filter (fun j : Fin (n + 1) => j ≤ k)) (by intro j k; simp)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_const, Finset.filter_ge_eq_Iic, Fin.card_Iic]

end Algebra

section Group

variable {G : Type*} [CommGroup G] {n : ℕ}

/-- Adjacent ratios `a_j / a_(j+1)` for `j < n`, followed by the last coordinate. -/
def adjRatio (a : Fin (n + 1) → G) : Fin (n + 1) → G :=
  Fin.snoc (α := fun _ => G) (fun i : Fin n => a i.castSucc / a i.succ) (a (Fin.last n))

@[simp] theorem adjRatio_castSucc (a : Fin (n + 1) → G) (i : Fin n) :
    adjRatio a i.castSucc = a i.castSucc / a i.succ := by
  simp [adjRatio]

@[simp] theorem adjRatio_last (a : Fin (n + 1) → G) :
    adjRatio a (Fin.last n) = a (Fin.last n) := by
  simp [adjRatio]

theorem adjRatio_tailProd (x : Fin (n + 1) → G) : adjRatio (tailProd x) = x := by
  funext j
  induction j using Fin.lastCases with
  | last => rw [adjRatio_last, tailProd_last]
  | cast i => rw [adjRatio_castSucc, tailProd_castSucc, mul_div_cancel_right]

theorem tailProd_adjRatio (a : Fin (n + 1) → G) : tailProd (adjRatio a) = a := by
  funext j
  induction j using Fin.reverseInduction with
  | last => rw [tailProd_last, adjRatio_last]
  | cast i ih => rw [tailProd_castSucc, ih, adjRatio_castSucc, div_mul_cancel]

/-- Adjacent ratios of tail products recover the original coordinates. -/
theorem tailProd_div_tailProd (x : Fin (n + 1) → G) (i : Fin n) :
    tailProd x i.castSucc / tailProd x i.succ = x i.castSucc := by
  rw [tailProd_castSucc, mul_div_cancel_right]

/-- Tail products as a multiplicative equivalence, with inverse `adjRatio`. -/
def tailProdEquiv : (Fin (n + 1) → G) ≃* (Fin (n + 1) → G) where
  toFun := tailProd
  invFun := adjRatio
  left_inv := adjRatio_tailProd
  right_inv := tailProd_adjRatio
  map_mul' := tailProd_mul

end Group

section Topology

variable {n : ℕ}

theorem continuous_tailProd {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] :
    Continuous (tailProd : (Fin (n + 1) → M) → Fin (n + 1) → M) :=
  continuous_pi fun _ => continuous_finsetProd _ fun k _ => continuous_apply k

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_adjRatio : Continuous (adjRatio : (Fin (n + 1) → G) → Fin (n + 1) → G) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.lastCases with
  | last => simpa using continuous_apply (Fin.last n)
  | cast i =>
    simp only [adjRatio_castSucc]
    exact (continuous_apply i.castSucc).div' (continuous_apply i.succ)

/-- Tail products as a topological group automorphism. -/
def tailProdHomeomorph : (Fin (n + 1) → G) ≃ₜ* (Fin (n + 1) → G) :=
  { tailProdEquiv with
    continuous_toFun := continuous_tailProd
    continuous_invFun := continuous_adjRatio }

@[simp] theorem coe_tailProdHomeomorph :
    ⇑(tailProdHomeomorph : (Fin (n + 1) → G) ≃ₜ* (Fin (n + 1) → G)) = tailProd :=
  rfl

end Topology

section Measure

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [SecondCountableTopology E]
  [MeasurableSpace Eˣ] [BorelSpace Eˣ] {n : ℕ}

/-- Tail products preserve the product of the normalized multiplicative Haar
measures on `(Eˣ)^(n+1)`. -/
theorem measurePreserving_tailProd :
    MeasurePreserving (tailProd : (Fin (n + 1) → Eˣ) → Fin (n + 1) → Eˣ)
      (Measure.pi fun _ => localMultiplicativeHaar E)
      (Measure.pi fun _ => localMultiplicativeHaar E) := by
  have := localField_t2 E
  have : SecondCountableTopology Eˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : LocallyCompactSpace Eˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := E)).locallyCompactSpace
  set μ : Measure (Fin (n + 1) → Eˣ) := Measure.pi fun _ => localMultiplicativeHaar E
  let e : (Fin (n + 1) → Eˣ) ≃ₜ* (Fin (n + 1) → Eˣ) := tailProdHomeomorph
  have hmeas : Measurable (tailProd : (Fin (n + 1) → Eˣ) → Fin (n + 1) → Eˣ) :=
    continuous_tailProd.measurable
  refine ⟨hmeas, ?_⟩
  have h := Measure.isMulLeftInvariant_eq_smul (μ.map e) μ
  let O : Set Eˣ := (integralUnits (ValuativeRel.valuation E).integer : Set Eˣ)
  have hO : MeasurableSet O :=
    (integralUnits_isOpen _ (Valuation.isOpen_integer (v := ValuativeRel.valuation E))).measurableSet
  let U : Set (Fin (n + 1) → Eˣ) := Set.univ.pi fun _ => O
  have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => hO
  have hμU : μ U = 1 := by
    simp [μ, U, O, Measure.pi_pi]
  have hpre : (tailProd : (Fin (n + 1) → Eˣ) → Fin (n + 1) → Eˣ) ⁻¹' U = U := by
    ext x
    simp only [Set.mem_preimage, U, Set.mem_univ_pi, O, SetLike.mem_coe]
    constructor
    · intro hx j
      induction j using Fin.lastCases with
      | last => rw [← tailProd_last x]; exact hx _
      | cast i => rw [← tailProd_div_tailProd x i]; exact div_mem (hx _) (hx _)
    · intro hx j
      exact Subgroup.prod_mem _ fun k _ => hx k
  have hmapU : μ.map e U = 1 := by
    rw [Measure.map_apply (show Measurable e from hmeas) hU]
    change μ (tailProd ⁻¹' U) = 1
    rw [hpre, hμU]
  have hc : Measure.haarScalarFactor (μ.map e) μ = 1 := by
    rw [h] at hmapU
    simpa [hμU] using hmapU
  change μ.map e = μ
  rw [h, hc, one_smul]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [SecondCountableTopology E] [MeasurableSpace Eˣ] [BorelSpace Eˣ] in
/-- Tail products of units have the tail products of their values as values. -/
theorem coe_tailProd_units (a : Fin (n + 1) → Eˣ) (j : Fin (n + 1)) :
    ((tailProd a j : Eˣ) : E) = tailProd (fun k => (a k : E)) j :=
  map_tailProd (Units.coeHom E) a j

end Measure

section Weights

variable {E : Type*} [Field E] {n : ℕ}

/-- Complex powers of a finite product of nonnegative reals split as products. -/
theorem ofReal_prod_cpow {ι : Type*} (t : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ t, 0 ≤ f i)
    (s : ℂ) : ((∏ i ∈ t, f i : ℝ) : ℂ) ^ s = ∏ i ∈ t, ((f i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a (by simp))
        (Finset.prod_nonneg fun i hi => hf i (by simp [hi])),
      ih fun i hi => hf i (by simp [hi])]

/-- The determinant weight of `τ(x)`: `|∏_j τ(x)_j|^s = ∏_k |x_k|^((k+1) s)`. -/
theorem cpow_abv_prod_tailProd (abv : AbsoluteValue E ℝ) (x : Fin (n + 1) → E) (s : ℂ) :
    ((abv (∏ j, tailProd x j) : ℝ) : ℂ) ^ s =
      ∏ k, ((abv (x k) : ℝ) : ℂ) ^ ((((k : ℕ) + 1 : ℕ) : ℂ) * s) := by
  have h1 : ∀ j, ((abv (tailProd x j) : ℝ) : ℂ) ^ s =
      tailProd (fun k => ((abv (x k) : ℝ) : ℂ) ^ s) j := by
    intro j
    rw [map_tailProd abv, tailProd, tailProd,
      ofReal_prod_cpow _ _ (fun k _ => abv.nonneg _)]
  rw [map_prod abv, ofReal_prod_cpow _ _ (fun j _ => abv.nonneg _)]
  simp_rw [h1]
  rw [prod_tailProd]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Complex.cpow_nat_mul]

end Weights

section Schwartz

variable {E : Type*} [Field E] [TopologicalSpace E] [IsTopologicalRing E] {n : ℕ}

/-- A test function of the first `n` coordinates times a test function of the
tail products is a Schwartz–Bruhat function on `E^(n+1)`. -/
theorem initTail_mem (φ : SchwartzBruhat (Fin n → E)) (Ψ : SchwartzBruhat (Fin (n + 1) → E)) :
    (fun x : Fin (n + 1) → E => φ (fun i => x i.castSucc) * Ψ (tailProd x)) ∈
      schwartzBruhatSubmodule (Fin (n + 1) → E) := by
  have hinit : Continuous fun x : Fin (n + 1) → E => fun i : Fin n => x i.castSucc :=
    continuous_pi fun i => continuous_apply _
  refine ⟨(φ.locallyConstant.comp_continuous hinit).mul
    (Ψ.locallyConstant.comp_continuous continuous_tailProd), ?_⟩
  let C : Fin (n + 1) → Set E := Fin.lastCases (motive := fun _ => Set E)
    ((fun y : Fin (n + 1) → E => y (Fin.last n)) '' tsupport Ψ)
    (fun i => (fun y : Fin n → E => y i) '' tsupport φ)
  have hC : ∀ j, IsCompact (C j) := by
    intro j
    induction j using Fin.lastCases with
    | last => simpa [C] using Ψ.hasCompactSupport.isCompact.image (continuous_apply _)
    | cast i => simpa [C] using φ.hasCompactSupport.isCompact.image (continuous_apply _)
  refine HasCompactSupport.intro (isCompact_univ_pi hC) fun x hx => ?_
  simp only [Set.mem_univ_pi, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  induction j using Fin.lastCases with
  | last =>
    have hΨ : tailProd x ∉ tsupport Ψ := fun h =>
      hj (by simp only [C, Fin.lastCases_last]; exact ⟨_, h, tailProd_last x⟩)
    simp [image_eq_zero_of_notMem_tsupport hΨ]
  | cast i =>
    have hφ : (fun i : Fin n => x i.castSucc) ∉ tsupport φ := fun h =>
      hj (by simp only [C, Fin.lastCases_castSucc]; exact ⟨_, h, rfl⟩)
    simp [image_eq_zero_of_notMem_tsupport hφ]

end Schwartz

section FiniteFunction

variable {A : Type*} [Monoid A] [TopologicalSpace A]

/-- The finite-function predicate of `FiniteFunctionMellinStatement` and
`CoefficientTorusExpansion`: continuity and a finite-dimensional span of
left translates. -/
def IsFiniteFunction (η : A → ℂ) : Prop :=
  Continuous η ∧
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun b : A => fun a : A => η (b * a)))

/-- A continuous function whose translates are scalar multiples of it is finite. -/
theorem IsFiniteFunction.of_mul_apply {η : A → ℂ} (hη : Continuous η) (c : A → ℂ)
    (h : ∀ b a, η (b * a) = c b * η a) : IsFiniteFunction η := by
  refine ⟨hη, ?_⟩
  have hle : Submodule.span ℂ (Set.range fun b : A => fun a : A => η (b * a)) ≤
      Submodule.span ℂ {η} := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : (fun a => η (b * a)) = c b • η := funext fun a => by simp [h]
    show (fun a => η (b * a)) ∈ (Submodule.span ℂ {η} : Set (A → ℂ))
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  exact Submodule.finiteDimensional_of_le hle

/-- Finite functions pull back to finite functions along continuous monoid
homomorphisms. -/
theorem IsFiniteFunction.comp {B : Type*} [Monoid B] [TopologicalSpace B] {η : B → ℂ}
    (hη : IsFiniteFunction η) (f : A →* B) (hf : Continuous f) :
    IsFiniteFunction (η ∘ f) := by
  refine ⟨hη.1.comp hf, ?_⟩
  have := hη.2
  let L : (B → ℂ) →ₗ[ℂ] (A → ℂ) := LinearMap.funLeft ℂ ℂ f
  have hle : Submodule.span ℂ (Set.range fun b : A => fun a : A => (η ∘ f) (b * a)) ≤
      (Submodule.span ℂ (Set.range fun b : B => fun a : B => η (b * a))).map L := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact ⟨fun a => η (f b * a), Submodule.subset_span ⟨f b, rfl⟩,
      funext fun a => by simp [L, LinearMap.funLeft, map_mul]⟩
  exact Submodule.finiteDimensional_of_le hle

/-- Products of finite functions are finite. -/
theorem IsFiniteFunction.mul {η₁ η₂ : A → ℂ} (h₁ : IsFiniteFunction η₁)
    (h₂ : IsFiniteFunction η₂) : IsFiniteFunction (η₁ * η₂) := by
  refine ⟨h₁.1.mul h₂.1, ?_⟩
  set S₁ := Submodule.span ℂ (Set.range fun b : A => fun a : A => η₁ (b * a))
  set S₂ := Submodule.span ℂ (Set.range fun b : A => fun a : A => η₂ (b * a))
  have : FiniteDimensional ℂ S₁ := h₁.2
  have : FiniteDimensional ℂ S₂ := h₂.2
  have hfg : (S₁ * S₂).FG :=
    ((Submodule.fg_iff_finiteDimensional S₁).2 ‹_›).mul
      ((Submodule.fg_iff_finiteDimensional S₂).2 ‹_›)
  have : FiniteDimensional ℂ (S₁ * S₂ : Submodule ℂ (A → ℂ)) :=
    (Submodule.fg_iff_finiteDimensional _).1 hfg
  have hle : Submodule.span ℂ (Set.range fun b : A => fun a : A => (η₁ * η₂) (b * a)) ≤
      S₁ * S₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨b, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

end FiniteFunction

end Langlands.GodementJacquet.WhittakerTorus
