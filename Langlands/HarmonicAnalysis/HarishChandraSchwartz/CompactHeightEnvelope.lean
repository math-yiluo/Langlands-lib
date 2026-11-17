import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights

/-! # Compact bi-invariant envelopes of actual matrix heights

Taking the supremum over two compact translation factors gives the exact
compact invariance used in the open-cell argument while retaining comparison
with the originally supplied matrix height.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Abstract

variable {H : Type*} [Group H]

/-- The supremum of a height over the double coset of a specified subgroup.
Boundedness hypotheses are supplied to the lemmas that compare its values. -/
def compactHeightEnvelope (K : Subgroup H) (σ : H → ℝ) (g : H) : ℝ :=
  sSup (Set.range fun p : K × K => σ ((p.1 : H) * g * p.2))

private theorem compactHeightEnvelope_range_nonempty
    (K : Subgroup H) (σ : H → ℝ) (g : H) :
    (Set.range fun p : K × K => σ ((p.1 : H) * g * p.2)).Nonempty :=
  ⟨_, ⟨(1, 1), rfl⟩⟩

/-- A subadditive height bounded on `K` is bounded on each double coset. -/
theorem compactHeightEnvelope_bddAbove (K : Subgroup H) {σ : H → ℝ}
    (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) {D : ℝ}
    (hD : ∀ k : K, σ k ≤ D) (g : H) :
    BddAbove (Set.range fun p : K × K => σ ((p.1 : H) * g * p.2)) := by
  refine ⟨σ g + 2 * D, ?_⟩
  rintro _ ⟨⟨k, l⟩, rfl⟩
  have h₁ := hsub ((k : H) * g) l
  have h₂ := hsub k g
  have hk := hD k
  have hl := hD l
  linarith

/-- Each translated height is at most the double-coset supremum. -/
theorem le_compactHeightEnvelope (K : Subgroup H) {σ : H → ℝ}
    (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) {D : ℝ}
    (hD : ∀ k : K, σ k ≤ D) (g : H) (k l : K) :
    σ ((k : H) * g * l) ≤ compactHeightEnvelope K σ g :=
  le_csSup (compactHeightEnvelope_bddAbove K hsub hD g) ⟨(k, l), rfl⟩

/-- The envelope differs from the original height by at most twice a bound on `K`. -/
theorem compactHeightEnvelope_bounds (K : Subgroup H) {σ : H → ℝ}
    (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) {D : ℝ}
    (hD : ∀ k : K, σ k ≤ D) (g : H) :
    σ g ≤ compactHeightEnvelope K σ g ∧
      compactHeightEnvelope K σ g ≤ σ g + 2 * D := by
  constructor
  · simpa using le_compactHeightEnvelope K hsub hD g 1 1
  · apply csSup_le (compactHeightEnvelope_range_nonempty K σ g)
    rintro _ ⟨⟨k, l⟩, rfl⟩
    have h₁ := hsub ((k : H) * g) l
    have h₂ := hsub k g
    have hk := hD k
    have hl := hD l
    linarith

/-- Double translation by the chosen subgroup preserves its envelope exactly. -/
theorem compactHeightEnvelope_mul_mul (K : Subgroup H) (σ : H → ℝ)
    (k l : K) (g : H) :
    compactHeightEnvelope K σ ((k : H) * g * l) =
      compactHeightEnvelope K σ g := by
  unfold compactHeightEnvelope
  congr 1
  ext r
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(x * k, l * y), ?_⟩
    simp only [Subgroup.coe_mul]
    congr 1
    group
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(x * k⁻¹, l⁻¹ * y), ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    congr 1
    group

/-- An inversion-invariant height has an inversion-invariant envelope. -/
theorem compactHeightEnvelope_inv (K : Subgroup H) {σ : H → ℝ}
    (hinv : ∀ x, σ x⁻¹ = σ x) (g : H) :
    compactHeightEnvelope K σ g⁻¹ = compactHeightEnvelope K σ g := by
  unfold compactHeightEnvelope
  congr 1
  ext r
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(y⁻¹, x⁻¹), ?_⟩
    simp only [Subgroup.coe_inv]
    rw [← hinv ((y : H)⁻¹ * g * (x : H)⁻¹)]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(y⁻¹, x⁻¹), ?_⟩
    simp only [Subgroup.coe_inv]
    rw [← hinv ((y : H)⁻¹ * g⁻¹ * (x : H)⁻¹)]
    simp only [mul_inv_rev, inv_inv, mul_assoc]

/-- The envelope remains subadditive. -/
theorem compactHeightEnvelope_mul_le (K : Subgroup H) {σ : H → ℝ}
    (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) {D : ℝ}
    (hD : ∀ k : K, σ k ≤ D) (g h : H) :
    compactHeightEnvelope K σ (g * h) ≤
      compactHeightEnvelope K σ g + compactHeightEnvelope K σ h := by
  apply csSup_le (compactHeightEnvelope_range_nonempty K σ (g * h))
  rintro _ ⟨⟨k, l⟩, rfl⟩
  have hk : σ ((k : H) * g) ≤ compactHeightEnvelope K σ g := by
    simpa using le_compactHeightEnvelope K hsub hD g k 1
  have hl : σ (h * (l : H)) ≤ compactHeightEnvelope K σ h := by
    simpa using le_compactHeightEnvelope K hsub hD h 1 l
  have hb := hsub ((k : H) * g) (h * (l : H))
  simp only [mul_assoc] at hb ⊢
  linarith

variable [TopologicalSpace H] [IsTopologicalGroup H]

/-- An envelope for an open subgroup is locally constant, independently of
the local constancy of the original function. -/
theorem eventually_compactHeightEnvelope_eq (K : OpenSubgroup H)
    (σ : H → ℝ) (g : H) :
    ∀ᶠ x in 𝓝 g,
      compactHeightEnvelope K.toSubgroup σ x = compactHeightEnvelope K.toSubgroup σ g := by
  have hc : Continuous (fun x : H => g⁻¹ * x) := continuous_const.mul continuous_id
  have ht : Tendsto (fun x : H => g⁻¹ * x) (𝓝 g) (𝓝 1) := by
    simpa only [inv_mul_cancel] using hc.tendsto g
  filter_upwards [ht.eventually (K.isOpen.mem_nhds K.one_mem)] with x hx
  have h := compactHeightEnvelope_mul_mul K.toSubgroup σ 1 ⟨g⁻¹ * x, hx⟩ g
  simpa only [OneMemClass.coe_one, one_mul, mul_inv_cancel_left] using h

/-- Every double-coset envelope for an open subgroup is locally constant. -/
theorem isLocallyConstant_compactHeightEnvelope (K : OpenSubgroup H) (σ : H → ℝ) :
    IsLocallyConstant (compactHeightEnvelope K.toSubgroup σ) :=
  (IsLocallyConstant.iff_eventually_eq _).mpr (eventually_compactHeightEnvelope_eq K σ)

end Abstract

section SeminormComparison

variable {X : Type*} {Ξ σ τ : X → ℝ}

/-- One-sided comparison of nonnegative heights bounds every Schwartz
seminorm by a constant times a seminorm for the original height. -/
theorem nu_le_of_one_add_height_le_mul
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hτ : ∀ g, 0 ≤ τ g)
    {A : ℝ} (hA : 0 ≤ A) (hcomp : ∀ g, 1 + τ g ≤ A * (1 + σ g))
    (r : ℝ) (f : X → ℂ) :
    nu Ξ τ r f ≤ ENNReal.ofReal (A ^ (max r 0)) * nu Ξ σ (max r 0) f := by
  have hc : 0 ≤ A ^ (max r 0) := Real.rpow_nonneg hA _
  have hw : ∀ g, weight Ξ τ r g ≤
      ENNReal.ofReal (A ^ (max r 0)) * weight Ξ σ (max r 0) g := by
    intro g
    have hbase : 1 ≤ 1 + τ g := by linarith [hτ g]
    have hr : (1 + τ g) ^ r ≤ (1 + τ g) ^ (max r 0) :=
      Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have hm : (1 + τ g) ^ (max r 0) ≤ (A * (1 + σ g)) ^ (max r 0) :=
      Real.rpow_le_rpow (by linarith [hτ g]) (hcomp g) (le_max_right _ _)
    rw [Real.mul_rpow hA (by linarith [hσ g])] at hm
    unfold weight
    rw [← ENNReal.ofReal_mul hc]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (hr.trans hm) (inv_nonneg.mpr (hΞ g).le)
    nlinarith
  unfold nu
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro g
  calc
    ‖f g‖ₑ * weight Ξ τ r g ≤
        ‖f g‖ₑ * (ENNReal.ofReal (A ^ (max r 0)) * weight Ξ σ (max r 0) g) := by
      gcongr
      exact hw g
    _ = _ := by ac_rfl

/-- Finiteness of all Schwartz seminorms transfers under a one-sided
linear comparison of the heights with one added. -/
theorem all_nu_lt_top_of_one_add_height_le_mul
    (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hτ : ∀ g, 0 ≤ τ g)
    {A : ℝ} (hA : 0 ≤ A) (hcomp : ∀ g, 1 + τ g ≤ A * (1 + σ g))
    {f : X → ℂ} (hf : ∀ r : ℝ, nu Ξ σ r f < ⊤) :
    ∀ r : ℝ, nu Ξ τ r f < ⊤ := by
  intro r
  exact (nu_le_of_one_add_height_le_mul hΞ hσ hτ hA hcomp r f).trans_lt
    (ENNReal.mul_lt_top (by simp) (hf _))

end SeminormComparison

section Rational

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The compact bi-invariant envelope of the originally supplied matrix height. -/
def rationalCompactHeight (ρ : MatrixRepresentation G n) (K : Subgroup (rationalPoints G)) :
    rationalPoints G → ℝ :=
  compactHeightEnvelope K (rationalHeight (F := F) ρ)

/-- Compactness alone bounds all the translation factors in the envelope. -/
theorem exists_rationalHeight_le_on_compact (ρ : MatrixRepresentation G n)
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))) :
    ∃ D ≥ 0, ∀ k : K, rationalHeight (F := F) ρ k ≤ D := by
  obtain ⟨D, hD⟩ := hK.bddAbove_image (continuous_rationalHeight ρ).continuousOn
  refine ⟨max D 0, le_max_right _ _, fun k => ?_⟩
  exact (hD (Set.mem_image_of_mem _ k.2)).trans (le_max_left _ _)

/-- Every actual compact-height envelope is equivalent to the given height,
with uniform additive and multiplicative comparison constants. -/
theorem rationalCompactHeight_bounds (ρ : MatrixRepresentation G n)
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))) :
    ∃ D ≥ 0, ∀ g : rationalPoints G,
      rationalHeight (F := F) ρ g ≤ rationalCompactHeight ρ K g ∧
      rationalCompactHeight ρ K g ≤ rationalHeight (F := F) ρ g + 2 * D ∧
      1 + rationalCompactHeight ρ K g ≤
        (1 + 2 * D) * (1 + rationalHeight (F := F) ρ g) := by
  obtain ⟨D, hD, hb⟩ := exists_rationalHeight_le_on_compact ρ K hK
  refine ⟨D, hD, fun g => ?_⟩
  obtain ⟨h₁, h₂⟩ := compactHeightEnvelope_bounds K (rationalHeight_mul_le ρ) hb g
  refine ⟨h₁, h₂, ?_⟩
  have hσ := rationalHeight_nonneg ρ g
  change 1 + compactHeightEnvelope K (rationalHeight (F := F) ρ) g ≤ _
  nlinarith

theorem rationalCompactHeight_nonneg (ρ : MatrixRepresentation G n)
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (g : rationalPoints G) : 0 ≤ rationalCompactHeight ρ K g := by
  obtain ⟨_, _, hb⟩ := rationalCompactHeight_bounds ρ K hK
  exact (rationalHeight_nonneg ρ g).trans (hb g).1

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Exact invariance under the specified compact subgroup. -/
theorem rationalCompactHeight_mul_mul (ρ : MatrixRepresentation G n)
    (K : Subgroup (rationalPoints G)) (k l : K) (g : rationalPoints G) :
    rationalCompactHeight ρ K ((k : rationalPoints G) * g * l) =
      rationalCompactHeight ρ K g :=
  compactHeightEnvelope_mul_mul K _ k l g

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem rationalCompactHeight_inv (ρ : MatrixRepresentation G n)
    (K : Subgroup (rationalPoints G)) (g : rationalPoints G) :
    rationalCompactHeight ρ K g⁻¹ = rationalCompactHeight ρ K g :=
  compactHeightEnvelope_inv K (rationalHeight_inv ρ) g

theorem rationalCompactHeight_mul_le (ρ : MatrixRepresentation G n)
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (g h : rationalPoints G) :
    rationalCompactHeight ρ K (g * h) ≤
      rationalCompactHeight ρ K g + rationalCompactHeight ρ K h := by
  obtain ⟨_, _, hb⟩ := exists_rationalHeight_le_on_compact ρ K hK
  exact compactHeightEnvelope_mul_le K (rationalHeight_mul_le ρ) hb g h

/-- Simultaneous local constancy at a point and its conjugate, as used in
the density step of Lemma II.3.5. -/
theorem eventually_rationalCompactHeight_eq_and_conj (ρ : MatrixRepresentation G n)
    (K : OpenSubgroup (rationalPoints G)) (a g : rationalPoints G) :
    ∀ᶠ x in 𝓝 g, rationalCompactHeight ρ K.toSubgroup x =
      rationalCompactHeight ρ K.toSubgroup g ∧
      rationalCompactHeight ρ K.toSubgroup (a * x * a⁻¹) =
        rationalCompactHeight ρ K.toSubgroup (a * g * a⁻¹) := by
  have ht : Tendsto (fun x : rationalPoints G => a * x * a⁻¹) (𝓝 g)
      (𝓝 (a * g * a⁻¹)) :=
    ((continuous_const.mul continuous_id).mul continuous_const).tendsto g
  exact (eventually_compactHeightEnvelope_eq K _ g).and
    (ht.eventually (eventually_compactHeightEnvelope_eq K _ (a * g * a⁻¹)))

/-- The auxiliary height is locally constant for every supplied open subgroup. -/
theorem isLocallyConstant_rationalCompactHeight (ρ : MatrixRepresentation G n)
    (K : OpenSubgroup (rationalPoints G)) :
    IsLocallyConstant (rationalCompactHeight ρ K.toSubgroup) :=
  isLocallyConstant_compactHeightEnvelope K _

/-- The envelope preserves every Schwartz level submodule, with its original
function values and original bi-invariance subgroup. -/
theorem rationalCompactHeight_levelSubmodule_eq
    (ρ : MatrixRepresentation G n) (K : Subgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G)))
    {Ξ : rationalPoints G → ℝ} (hΞ : ∀ g, 0 < Ξ g)
    (H : Subgroup (rationalPoints G)) :
    levelSubmodule Ξ (rationalCompactHeight ρ K) H =
      levelSubmodule Ξ (rationalHeight (F := F) ρ) H := by
  obtain ⟨D, hD, hb⟩ := rationalCompactHeight_bounds ρ K hK
  have hσ := rationalHeight_nonneg ρ
  have hτ := rationalCompactHeight_nonneg ρ K hK
  ext f
  rw [mem_levelSubmodule_iff, mem_levelSubmodule_iff]
  constructor
  · rintro ⟨hH, hf⟩
    exact ⟨hH, all_nu_lt_top_of_one_add_height_le_mul hΞ hτ hσ zero_le_one
      (fun g => by simpa using add_le_add_left (hb g).1 1) hf⟩
  · rintro ⟨hH, hf⟩
    exact ⟨hH, all_nu_lt_top_of_one_add_height_le_mul hΞ hσ hτ (by positivity)
      (fun g => (hb g).2.2) hf⟩

/-- The underlying Schwartz submodule is unchanged by the auxiliary height. -/
theorem rationalCompactHeight_schwartzSubmodule_eq
    (ρ : MatrixRepresentation G n) (K : Subgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G)))
    {Ξ : rationalPoints G → ℝ} (hΞ : ∀ g, 0 < Ξ g) :
    schwartzSubmodule Ξ (rationalCompactHeight ρ K) =
      schwartzSubmodule Ξ (rationalHeight (F := F) ρ) := by
  unfold schwartzSubmodule
  congr 1
  funext H
  exact rationalCompactHeight_levelSubmodule_eq ρ K hK hΞ H.toSubgroup

variable {N : ℕ} [Nonempty (Fin N)]

/-- For a closed realization and a compact open subgroup, the envelope has
compact sublevels as well as local constancy and compact invariance. -/
theorem isCompact_rationalCompactHeight_le
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (K : OpenSubgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G))) (C : ℝ) :
    IsCompact {g : rationalPoints G | rationalCompactHeight ρ K.toSubgroup g ≤ C} := by
  obtain ⟨_, _, hb⟩ := rationalCompactHeight_bounds ρ K.toSubgroup hK
  exact (isCompact_rationalHeight_le ρ hρ C).of_isClosed_subset
    (isClosed_le (isLocallyConstant_rationalCompactHeight ρ K).continuous continuous_const)
    (fun g hg => (hb g).1.trans hg)

end Rational

end Langlands.HarishChandraSchwartz
