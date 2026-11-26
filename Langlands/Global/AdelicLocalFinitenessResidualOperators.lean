import Langlands.Global.AdelicLocalFinitenessChamberEmbedding
import Langlands.Global.AdelicLocalFinitenessSiegelFrame
import Langlands.Global.AdelicLocalFinitenessComponentShifts

/-! # Residual and box operators on the weighted Siegel space

The Siegel weight in chamber coordinates is the chamber density of the Library's weighted
Siegel spaces; it is invariant under `P₀(F)` and every `U_J(𝔸)` and comparable with its left
translates by the root and central shifts. On `L²` of the Siegel weight, the Harish-Chandra
components, their translates by powers of the shifts and their restrictions to boxes and
positive regions are bounded operators, and the norm is bounded by the box norms of the
components and the positive-region norms of their difference residuals.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints AdelicGroupPoints AdelicSiegelFactors

section Generic

variable {X D : Type*} [Fintype D] {r : ℕ}

/-- If the coordinates of `y` are those of `x` plus `v` with non-negative root part, the Siegel
weight at `x` is at most `exp(2 (∑ ra_β v_β + ∑ |rb_j| |v_j|))` times the weight at `y`. -/
theorem siegelWeight_le_of_coords (c : X → (D → ℝ) × (Fin r → ℝ)) (ra : D → ℝ)
    (rb : Fin r → ℝ) (τ : D → ℝ) {x y : X} {v : (D → ℝ) × (Fin r → ℝ)} (hv : ∀ β, 0 ≤ v.1 β)
    (hxy : c y = c x + v) :
    siegelWeight c ra rb τ x ≤
      ENNReal.ofReal (Real.exp (2 * ((∑ β, ra β * v.1 β) + ∑ j, |rb j| * |v.2 j|))) *
        siegelWeight c ra rb τ y := by
  unfold siegelWeight
  by_cases hx : c x ∈ siegelRegion τ
  · have hy : c y ∈ siegelRegion τ := by
      rw [hxy]
      intro β
      have := hx β
      simp only [Prod.fst_add, Pi.add_apply]
      linarith [hv β]
    rw [indicator_of_mem hx, indicator_of_mem hy, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hlw : localFinitenessLogWeight ra rb (c y) ≤ localFinitenessLogWeight ra rb (c x) +
        ((∑ β, ra β * v.1 β) + ∑ j, |rb j| * |v.2 j|) := by
      rw [hxy]
      unfold localFinitenessLogWeight
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      have hj : ∀ j, rb j * |(c x).2 j + v.2 j| ≤ rb j * |(c x).2 j| + |rb j| * |v.2 j| := by
        intro j
        have h1 : rb j * |(c x).2 j + v.2 j| - rb j * |(c x).2 j| ≤
            |rb j| * |v.2 j| := by
          rw [← mul_sub]
          calc rb j * (|(c x).2 j + v.2 j| - |(c x).2 j|)
              ≤ |rb j * (|(c x).2 j + v.2 j| - |(c x).2 j|)| := le_abs_self _
            _ = |rb j| * |(|(c x).2 j + v.2 j| - |(c x).2 j|)| := abs_mul _ _
            _ ≤ |rb j| * |v.2 j| := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                have := abs_abs_sub_abs_le_abs_sub ((c x).2 j + v.2 j) ((c x).2 j)
                simpa using this
        linarith
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hj j
      rw [Finset.sum_add_distrib] at this
      linarith
    linarith
  · rw [indicator_of_notMem hx]
    exact bot_le

/-- A point moving the coordinates by a fixed vector with non-negative root part has a finite
forward comparison factor for the Siegel weight. -/
theorem exists_siegelWeight_le_mul [Mul X] (c : X → (D → ℝ) × (Fin r → ℝ)) (ra : D → ℝ)
    (rb : Fin r → ℝ) (τ : D → ℝ) (b : X) (v : (D → ℝ) × (Fin r → ℝ)) (hv : ∀ β, 0 ≤ v.1 β)
    (hb : ∀ g, c (b * g) = c g + v) :
    ∃ κ : ℝ≥0∞, κ ≠ ∞ ∧ ∀ g, siegelWeight c ra rb τ g ≤ κ * siegelWeight c ra rb τ (b * g) :=
  ⟨_, ENNReal.ofReal_ne_top, fun g => siegelWeight_le_of_coords c ra rb τ hv (hb g)⟩

/-- Each orthant shift has a finite forward comparison factor for the Siegel weight. -/
theorem exists_siegelWeight_le_orthantShift [DecidableEq D] [Group X]
    (c : X → (D → ℝ) × (Fin r → ℝ)) (a : D → X) (z : Fin r → X)
    (hca : ∀ β g, c (a β * g) = c g + (Pi.single β 1, 0))
    (hcz : ∀ j g, c (z j * g) = c g + (0, Pi.single j 1)) (ra : D → ℝ) (rb : Fin r → ℝ)
    (τ : D → ℝ) (J : D → Prop) (ε : Fin r → Bool) (k : {β : D // ¬ J β} ⊕ Fin r) :
    ∃ κ : ℝ≥0∞, κ ≠ ∞ ∧ ∀ g, siegelWeight c ra rb τ g ≤
      κ * siegelWeight c ra rb τ (orthantShift a z J ε k * g) := by
  rcases k with β | j
  · refine exists_siegelWeight_le_mul c ra rb τ _ (Pi.single β.1 1, 0) (fun β' => ?_) (hca β.1)
    by_cases h : β' = β.1
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · simp only [orthantShift, Sum.elim_inr]
    split_ifs
    · exact exists_siegelWeight_le_mul c ra rb τ _ (0, Pi.single j 1) (fun _ => le_rfl) (hcz j)
    · refine exists_siegelWeight_le_mul c ra rb τ _ (-(0, Pi.single j 1)) (fun _ => by simp)
        fun g => ?_
      rw [coords_inv_mul c z hcz j g, sub_eq_add_neg]

/-- The operator `L m + ∑_{q < m} p_q • L q` of the monic difference polynomial with lower
coefficients `p` in a family `L q` of operators. -/
def residualOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (L : ℕ → E →L[ℂ] E)
    {m : ℕ} (p : Fin m → ℂ) : E →L[ℂ] E :=
  L m + ∑ q, p q • L (q : ℕ)

end Generic

/-- A function left invariant under two subgroups is left invariant under their join. -/
theorem invariant_sup {A β : Type*} [Group A] (H₁ H₂ : Subgroup A) (φ : A → β)
    (h₁ : ∀ h ∈ H₁, ∀ g, φ (h * g) = φ g) (h₂ : ∀ h ∈ H₂, ∀ g, φ (h * g) = φ g) :
    ∀ h ∈ H₁ ⊔ H₂, ∀ g, φ (h * g) = φ g := by
  intro h hh
  rw [Subgroup.sup_eq_closure] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact h₁ x hx
    · exact h₂ x hx
  | one => intro g; rw [one_mul]
  | mul x y _ _ hx hy => intro g; rw [mul_assoc, hx, hy]
  | inv x _ hx =>
    intro g
    have := hx (x⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    exact this.symm

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

private instance : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left

variable {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  [Fintype (simpleRelativeRoots i ν)] [DecidableEq (simpleRelativeRoots i ν)] {r : ℕ}
  (e : RealCharacterDual F (Standard.parabolicScheme i ν ∅) ≃L[ℝ]
    ((simpleRelativeRoots i ν → ℝ) × (Fin r → ℝ)))

/-- The chamber density of the log weight `localFinitenessLogWeight ra rb ∘ e` on the region
`e⁻¹(siegelRegion τ)` is the Siegel weight in chamber coordinates. -/
theorem chamberDensity_eq_siegelWeight (ra τ : simpleRelativeRoots i ν → ℝ) (rb : Fin r → ℝ) :
    WeightedSiegel.chamberDensity F (Standard.parabolicHom i ν ∅) hK
      (localFinitenessLogWeight ra rb ∘ e) (e ⁻¹' siegelRegion τ) =
    siegelWeight (chamberCoords hK e) ra rb τ := by
  funext g
  by_cases hg : chamberCoords hK e g ∈ siegelRegion τ
  · rw [WeightedSiegel.chamberDensity, siegelWeight,
      indicator_of_mem (show g ∈ hK.height ⁻¹' (e ⁻¹' siegelRegion τ) from hg),
      indicator_of_mem hg]
    rfl
  · rw [WeightedSiegel.chamberDensity, siegelWeight,
      indicator_of_notMem (show g ∉ hK.height ⁻¹' (e ⁻¹' siegelRegion τ) from hg),
      indicator_of_notMem hg]

/-- The frame measure of the weighted Siegel space of the region `e⁻¹(siegelRegion τ)` is the
Siegel weight times Haar measure on the fundamental domain of `Λ₀`. -/
theorem frameMeasure_eq_domainWeightedHaar (ra τ : simpleRelativeRoots i ν → ℝ) (rb : Fin r → ℝ) :
    WeightedSiegel.frameMeasure hK (localFinitenessLogWeight ra rb ∘ e) (e ⁻¹' siegelRegion τ) =
      domainWeightedHaar F G i ν (siegelWeight (chamberCoords hK e) ra rb τ) := by
  rw [WeightedSiegel.frameMeasure_eq_standard i ν hK, chamberDensity_eq_siegelWeight]
  rfl

theorem measurable_siegelWeight_chamberCoords (ra τ : simpleRelativeRoots i ν → ℝ)
    (rb : Fin r → ℝ) : Measurable (siegelWeight (chamberCoords hK e) ra rb τ) :=
  measurable_siegelWeight (continuous_chamberCoords hK e).measurable ra rb τ

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

include hG hi hν in
/-- The Siegel weight in chamber coordinates is left invariant under `Λ₀ ⊔ U_J(𝔸)`. -/
theorem siegelWeight_cosetSubgroup_mul (ra τ : simpleRelativeRoots i ν → ℝ) (rb : Fin r → ℝ)
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {h : AdelicGroupPoints F G} (hh : h ∈ cosetSubgroup F G i ν J) (g : AdelicGroupPoints F G) :
    siegelWeight (chamberCoords hK e) ra rb τ (h * g) =
      siegelWeight (chamberCoords hK e) ra rb τ g := by
  unfold siegelWeight
  rw [chamberCoords_cosetSubgroup_mul hK hG hi hν e hJ hh g]

/-- If `L q` computes the translate `g ↦ φ(b^q g)` of a class, the residual operator computes the
residual of `φ`. -/
theorem residualOperator_ae {mu : Measure (AdelicGroupPoints F G)}
    (L : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (b : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) (Fn : Lp ℂ 2 mu)
    (hL : ∀ q, L q Fn =ᵐ[mu] fun g => φ (b ^ q * g)) {m : ℕ} (p : Fin m → ℂ) :
    residualOperator L p Fn =ᵐ[mu] residualFun F G b p φ := by
  unfold residualOperator residualFun
  rw [add_apply, sum_apply]
  have hall : ∀ᵐ g ∂mu, ∀ q : Fin m,
      ((p q • L q) Fn : AdelicGroupPoints F G → ℂ) g = p q * φ (b ^ (q : ℕ) * g) := by
    rw [ae_all_iff]
    intro q
    filter_upwards [Lp.coeFn_smul (p q) (L q Fn), hL q] with g h1 h2
    rw [smul_apply, h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [Lp.coeFn_add (L m Fn) (∑ q, (p q • L q) Fn),
    HarishChandraDecomposition.coeFn_finset_sum_ae Finset.univ (fun q => (p q • L q) Fn), hL m,
    hall] with g h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, Finset.sum_apply]
  exact congrArg _ (Finset.sum_congr rfl fun q _ => h4 q)

end Langlands.Global.StandardConstantTerm

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints AdelicGroupPoints AdelicSiegelFactors
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

variable {𝓕} in
/-- The inverse of a point commuting with `L_J(𝔸)` and normalizing `U_J(𝔸)` has the same
properties. -/
theorem IsLeviNormalizingPoint.inv {J : Set (characterLattice 𝓕.T)} {b : AdelicGroupPoints F G}
    (hb : 𝓕.IsLeviNormalizingPoint J b) : 𝓕.IsLeviNormalizingPoint J b⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := hb
  refine ⟨fun x hx => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have hx' := h1 x hx
    calc b⁻¹ * x = b⁻¹ * (x * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * x) * b⁻¹ := by rw [hx']
      _ = x * b⁻¹ := by group
  · rw [inv_inv]; exact h3 w hw
  · rw [inv_inv]; exact h2 w hw


variable {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) K)
  [Fintype (simpleRelativeRoots 𝓕.i 𝓕.ν)] [DecidableEq (simpleRelativeRoots 𝓕.i 𝓕.ν)] {r : ℕ}
  (e : RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅) ≃L[ℝ]
    ((simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) × (Fin r → ℝ)))

/-- `W · Haar` on the fundamental domain of `Λ₀`, for the Siegel weight `W` in chamber
coordinates. -/
abbrev siegelHaar (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ) :
    Measure (AdelicGroupPoints F G) :=
  𝓕.weightedHaar (siegelWeight (chamberCoords hK e) ra rb τ)

/-- Each orthant shift for the index of `P` commutes with the Levi and normalizes the unipotent
radical of `P`. -/
theorem isLeviNormalizingPoint_orthantShift (a : simpleRelativeRoots 𝓕.i 𝓕.ν → AdelicGroupPoints F G)
    (z : Fin r → AdelicGroupPoints F G)
    (haN : ∀ (β : simpleRelativeRoots 𝓕.i 𝓕.ν) (J : Set (characterLattice 𝓕.T)),
      J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν → β.val ∉ J → 𝓕.IsLeviNormalizingPoint J (a β))
    (hzN : ∀ (j : Fin r) (J : Set (characterLattice 𝓕.T)), J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν →
      𝓕.IsLeviNormalizingPoint J (z j))
    (P : Finset (characterLattice 𝓕.T)) (ε : Fin r → Bool)
    (k : {β : simpleRelativeRoots 𝓕.i 𝓕.ν // ¬ β.val ∈ (𝓕.finsetIndex P).1} ⊕ Fin r) :
    𝓕.IsLeviNormalizingPoint (𝓕.finsetIndex P).1
      (orthantShift a z (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε k) := by
  rcases k with β | j
  · exact haN β.1 _ (𝓕.finsetIndex P).2 β.2
  · simp only [orthantShift, Sum.elim_inr]
    split_ifs
    · exact hzN j _ (𝓕.finsetIndex P).2
    · exact (hzN j _ (𝓕.finsetIndex P).2).inv

open scoped Classical in
/-- **Residual and box operators with a strict norm bound.** Let `a_β` and `z_j` shift the chamber
coordinates by unit vectors, `a_β` (for `β ∉ J`) and `z_j` commuting with `L_J(𝔸)` and
normalizing `U_J(𝔸)` for every `J ⊆ Δ`. For thresholds `τ` and a coefficient bound `M` there is
`R₀ ≥ 0` such that for all rates `ra_β, rb_j ≥ R₀` there are bounded operators on `L²` of the
Siegel weight:

* `E P`, computing the Harish-Chandra component `∑_{S ⊆ P} (−1)^{|P ∖ S|} C_S f` on measurable
  representatives, with `∑_{P ⊆ Δ} E P = 1`;
* `L P ε k q`, computing `g ↦ (E P f)(b^q g)` for the orthant shift `b` of direction `k`;

and, for all degrees `m` and lower coefficients `p` with `∑_q ‖p_q‖ ≤ M`, a constant `C ≥ 0` with
`‖F‖ ≤ C ∑_P ∑_ε (‖E P F‖_box + ∑_k ‖(L m + ∑_q p_q L q) F‖_pos)`. -/
theorem exists_residualOperators (a : simpleRelativeRoots 𝓕.i 𝓕.ν → AdelicGroupPoints F G)
    (z : Fin r → AdelicGroupPoints F G)
    (hca : ∀ β g, chamberCoords hK e (a β * g) = chamberCoords hK e g + (Pi.single β 1, 0))
    (hcz : ∀ j g, chamberCoords hK e (z j * g) = chamberCoords hK e g + (0, Pi.single j 1))
    (haN : ∀ (β : simpleRelativeRoots 𝓕.i 𝓕.ν) (J : Set (characterLattice 𝓕.T)),
      J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν → β.val ∉ J → 𝓕.IsLeviNormalizingPoint J (a β))
    (hzN : ∀ (j : Fin r) (J : Set (characterLattice 𝓕.T)), J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν →
      𝓕.IsLeviNormalizingPoint J (z j))
    (τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (M : ℝ) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ (ra : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ),
      (∀ β, R₀ ≤ ra β) → (∀ j, R₀ ≤ rb j) →
    ∃ (E : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)))
      (L : ∀ (P : Finset (characterLattice 𝓕.T)), (Fin r → Bool) →
        ({β : simpleRelativeRoots 𝓕.i 𝓕.ν // ¬ β.val ∈ (𝓕.finsetIndex P).1} ⊕ Fin r) → ℕ →
        (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb))),
      (∀ P (Fn : Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)) {f : AdelicGroupPoints F G → ℂ},
        Measurable f → f =ᵐ[𝓕.siegelHaar hK e ra τ rb] Fn →
        E P Fn =ᵐ[𝓕.siegelHaar hK e ra τ rb] alternatingSum (fun S => 𝓕.componentFoldCT S f) P) ∧
      (∀ P ε k q (Fn : Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)) {f : AdelicGroupPoints F G → ℂ},
        Measurable f → f =ᵐ[𝓕.siegelHaar hK e ra τ rb] Fn →
        L P ε k q Fn =ᵐ[𝓕.siegelHaar hK e ra τ rb] fun g =>
          alternatingSum (fun S => 𝓕.componentFoldCT S f) P
            (orthantShift a z (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1)
              ε k ^ q * g)) ∧
      (∑ P ∈ 𝓕.simpleRootFinset.powerset, E P = ContinuousLinearMap.id ℂ _) ∧
      ∀ (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool),
          ({β : simpleRelativeRoots 𝓕.i 𝓕.ν // ¬ β.val ∈ (𝓕.finsetIndex P).1} ⊕ Fin r) → ℕ)
        (p : ∀ P ε k, Fin (m P ε k) → ℂ), (∀ P ε k, ∑ q, ‖p P ε k q‖ ≤ M) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ Fn : Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb),
        ‖Fn‖ ≤ C * ∑ P ∈ 𝓕.simpleRootFinset.powerset, ∑ ε : Fin r → Bool,
          (‖LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ (𝓕.siegelHaar hK e ra τ rb) 2
              (orthantBox (chamberCoords hK e) τ
                (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε (m P ε))
              (E P Fn)‖ +
            ∑ k, ‖LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ (𝓕.siegelHaar hK e ra τ rb) 2
              (orthantPos (chamberCoords hK e) τ
                (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε)
              (residualOperator (L P ε k) (p P ε k) Fn)‖) := by
  let Idx := {P // P ∈ 𝓕.simpleRootFinset.powerset}
  obtain ⟨R₀, hR₀, hemb⟩ := exists_chamberEmbedding hK 𝓕.connectedReductive 𝓕.maximalSplit
    𝓕.generic e a z hca hcz (fun β J hJ hβ => haN β J hJ hβ) (fun j J hJ => hzN j J hJ)
    (J := fun P : Idx => (𝓕.finsetIndex P.1).1) (fun P => (𝓕.finsetIndex P.1).2) τ M
  refine ⟨R₀, hR₀, fun ra rb hra hrb => ?_⟩
  set W := siegelWeight (chamberCoords hK e) ra rb τ with hWdef
  set mu := 𝓕.siegelHaar hK e ra τ rb with hmudef
  have hWm : Measurable W := measurable_siegelWeight_chamberCoords hK e ra τ rb
  have hWJ : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν, ∀ h ∈ cosetSubgroup F G 𝓕.i 𝓕.ν J, ∀ x,
      W (h * x) = W x := fun J hJ h hh x =>
    siegelWeight_cosetSubgroup_mul hK e 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic ra τ rb
      hJ hh x
  have hWΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x :=
    fun l hl x => hWJ ∅ (empty_subset _) l (Subgroup.mem_sup_left hl) x
  have hWU : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x :=
    fun J hJ w hw x => hWJ J hJ w (Subgroup.mem_sup_right hw) x
  obtain ⟨T, hT1, hT2, hTtop⟩ := 𝓕.exists_componentOperators W hWm hWΛ hWU
  have hN := 𝓕.isLeviNormalizingPoint_orthantShift a z haN hzN
  have hcmp (P : Finset (characterLattice 𝓕.T)) (ε : Fin r → Bool)
      (k : {β : simpleRelativeRoots 𝓕.i 𝓕.ν // ¬ β.val ∈ (𝓕.finsetIndex P).1} ⊕ Fin r) :=
    exists_siegelWeight_le_orthantShift (chamberCoords hK e) a z hca hcz ra rb τ
      (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε k
  choose κ hκtop hκ using hcmp
  choose L hL using fun P ε k => 𝓕.exists_translatedComponent_pow W hWm hWΛ hWU T hT1 hT2 P
    _ (hN P ε k).1 (hN P ε k).2.1 (hN P ε k).2.2 (hκtop P ε k) (hκ P ε k)
  have hE : ∀ P (Fn : Lp ℂ 2 mu) {f : AdelicGroupPoints F G → ℂ}, Measurable f → f =ᵐ[mu] Fn →
      alternatingSum T P Fn =ᵐ[mu] alternatingSum (fun S => 𝓕.componentFoldCT S f) P :=
    fun P Fn f hf hfF => alternatingSum_apply_ae T Fn (fun S => 𝓕.componentFoldCT S f)
      (fun S => hT2 S Fn hf hfF) P
  have hsumE : ∑ P ∈ 𝓕.simpleRootFinset.powerset, alternatingSum T P =
      ContinuousLinearMap.id ℂ _ := by
    rw [sum_alternatingSum, hTtop]
  refine ⟨fun P => alternatingSum T P, L, hE, fun P ε k q Fn f hf hfF => hL P ε k q Fn hf hfF,
    hsumE, fun m p hp => ?_⟩
  obtain ⟨C, hC, hCest⟩ := hemb ra rb hra hrb (fun P => m P.1) (fun P => p P.1)
    (fun P => hp P.1)
  refine ⟨C, hC, fun Fn => ?_⟩
  have hm := Lp.aestronglyMeasurable Fn
  set f := hm.mk Fn with hfdef
  have hf : Measurable f := hm.stronglyMeasurable_mk.measurable
  have hfF : f =ᵐ[mu] Fn := hm.ae_eq_mk.symm
  let φ : Idx → AdelicGroupPoints F G → ℂ := fun P =>
    alternatingSum (fun S => 𝓕.componentFoldCT S f) P.1
  have hφE : ∀ P : Idx, φ P =ᵐ[mu] alternatingSum T P.1 Fn := fun P => (hE P.1 Fn hf hfF).symm
  have hφm : ∀ P : Idx, Measurable (φ P) := by
    intro P
    have h := Finset.measurable_sum P.1.powerset
      (f := fun S => ((-1 : ℂ) ^ (P.1 \ S).card) • 𝓕.componentFoldCT S f)
      fun S _ => (𝓕.measurable_componentFoldCT S hf).const_smul _
    convert h using 1
    funext x
    simp [φ, alternatingSum, Finset.sum_apply]
  have hφinv : ∀ P : Idx, ∀ h ∈ cosetSubgroup F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P.1).1, ∀ g,
      φ P (h * g) = φ P g := by
    intro P
    refine invariant_sup _ _ (φ P) (fun l hl x => ?_) (fun w hw x => ?_)
    · simp only [φ, alternatingSum, Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun S hS => by
        rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) f).1 l hl x]
    · simp only [φ, alternatingSum, Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun S hS => by
        rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) f).2 w hw x]
  have hsum : f =ᵐ[mu] fun g => ∑ P, φ P g := by
    have hFn : Fn = ∑ P ∈ 𝓕.simpleRootFinset.powerset, alternatingSum T P Fn := by
      rw [← sum_apply, hsumE]
      rfl
    have hall : ∀ᵐ g ∂mu, ∀ P : Idx, φ P g = (alternatingSum T P.1 Fn : AdelicGroupPoints F G → ℂ) g :=
      ae_all_iff.mpr hφE
    filter_upwards [hfF, coeFn_finset_sum_ae (m := mu) 𝓕.simpleRootFinset.powerset
      (fun P => alternatingSum T P Fn), hall] with g h1 h2 h3
    rw [h1, hFn, h2, Finset.sum_apply, ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun P _ => (h3 P).symm
  have hres : ∀ (P : Idx) ε k, residualOperator (L P.1 ε k) (p P.1 ε k) Fn =ᵐ[mu]
      residualFun F G (orthantShift a z
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε k)
        (p P.1 ε k) (φ P) :=
    fun P ε k => residualOperator_ae (L P.1 ε k) _ (φ P) Fn
      (fun q => hL P.1 ε k q Fn hf hfF) (p P.1 ε k)
  have hboxL : ∀ (P : Idx) ε, MemLp (φ P) 2 (mu.restrict (orthantBox (chamberCoords hK e) τ
      (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))) :=
    fun P ε => ((Lp.memLp (alternatingSum T P.1 Fn)).ae_eq (hφE P).symm).restrict _
  have hresL : ∀ (P : Idx) ε k, MemLp (residualFun F G (orthantShift a z
      (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε k)
      (p P.1 ε k) (φ P)) 2 (mu.restrict (orthantPos (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε)) :=
    fun P ε k => ((Lp.memLp _).ae_eq (hres P ε k)).restrict _
  obtain ⟨-, hle⟩ := hCest f φ hf hφm hφinv hsum hboxL hresL
  have h1 : ‖Fn‖ = lpNorm f 2 mu := by
    rw [Lp.norm_def]
    unfold lpNorm
    rw [eLpNorm_congr_ae hfF]
  have h2 : ∀ (P : Idx) ε, lpNorm (φ P) 2 (mu.restrict (orthantBox (chamberCoords hK e) τ
      (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))) =
      ‖LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ mu 2 (orthantBox (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))
        (alternatingSum T P.1 Fn)‖ := by
    intro P ε
    rw [Lp.norm_def]
    unfold lpNorm
    have hr : φ P =ᵐ[mu.restrict (orthantBox (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε (m P.1 ε))]
        alternatingSum T P.1 Fn := ae_restrict_of_ae (hφE P)
    rw [eLpNorm_congr_ae (hr.trans (LpToLpRestrictCLM_coeFn ℂ _ (alternatingSum T P.1 Fn)).symm)]
  have h3 : ∀ (P : Idx) ε k, lpNorm (residualFun F G (orthantShift a z
      (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε k)
      (p P.1 ε k) (φ P)) 2 (mu.restrict (orthantPos (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε)) =
      ‖LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ mu 2 (orthantPos (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε)
        (residualOperator (L P.1 ε k) (p P.1 ε k) Fn)‖ := by
    intro P ε k
    rw [Lp.norm_def]
    unfold lpNorm
    have hr : residualOperator (L P.1 ε k) (p P.1 ε k) Fn =ᵐ[mu.restrict (orthantPos
        (chamberCoords hK e) τ
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε)]
        residualFun F G (orthantShift a z
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P.1).1) ε k)
          (p P.1 ε k) (φ P) := ae_restrict_of_ae (hres P ε k)
    rw [eLpNorm_congr_ae (hr.symm.trans (LpToLpRestrictCLM_coeFn ℂ _ _).symm)]
  rw [h1]
  refine hle.trans (le_of_eq ?_)
  congr 1
  rw [← Finset.sum_coe_sort 𝓕.simpleRootFinset.powerset]
  refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun ε _ => ?_
  exact congrArg₂ (· + ·) (h2 P ε) (Finset.sum_congr rfl fun k _ => h3 P ε k)

end Langlands.Global.StandardParabolicFamily
