import Langlands.Global.AdelicStandardSlabEstimate
import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicStandardLeviHeightRestriction
import Langlands.Global.EisensteinConstantTerm.Points

/-! # Slab estimates in the chamber coordinates of the minimal-parabolic height

The Iwasawa height `H₀` for the standard minimal parabolic is left invariant under the image
of `P₀(F)` and under `U_J(𝔸)`. In linear coordinates `e ∘ H₀` with root and central parts,
translations that shift one coordinate by one give, on each central orthant, renormalizing
shifts for an exponential weight, and the slab estimate of `AdelicStandardSlabEstimate`
applies for all sufficiently large rates (Bernstein–Lapid §§7.5, 7.7).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local notation "A" => AdelicGroupPoints F G
local notation "P₀" => Standard.parabolicScheme i ν ∅
local notation "p₀" => Standard.parabolicHom i ν ∅
local notation "Δ" => simpleRelativeRoots i ν

private instance : IsClosedImmersion (p₀).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (P₀).X.left := isAffine_of_isAffineHom (p₀).hom.hom.left

variable {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)

/-- The minimal-parabolic height is left invariant under the image of `P₀(F)`. -/
theorem height_minimalParabolicImage_mul {l : A} (hl : l ∈ minimalParabolicImage F G i ν) (g : A) :
    hK.height (l * g) = hK.height g := by
  obtain ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩ := hl
  rw [← (Standard.isRepresentedBy_parabolicHom i ν ∅).2] at hx
  obtain ⟨q, hq⟩ := hx
  let q' : RationalGroupPoints F P₀ := q
  have hl : (AdelicGroupPoints.rational F G x : A) = map F P₀ G p₀ (rational F P₀ q') := by
    rw [map_rational]
    exact (congrArg (AdelicGroupPoints.rational F G) hq).symm
  change hK.height (AdelicGroupPoints.rational F G x * g) = _
  rw [hl]
  exact hK.height_rational_mul q' g

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

include hG hi hν in
/-- The minimal-parabolic height is left invariant under `U_J(𝔸)`. -/
theorem height_standardUnipotent_mul {J : Set (characterLattice T)} (hJ : J ⊆ Δ)
    {w : A} (hw : w ∈ adelicPoints F G (standardUnipotent i ν J)) (g : A) :
    hK.height (w * g) = hK.height g := by
  have h := ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).2
    (Set.empty_subset J)
  have hw₀ : w ∈ (standardUnipotent i ν ∅).carrier
      ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)))) :=
    h.2 _ hw
  rw [← (Standard.isRepresentedBy_unipotentHom i ν ∅).2] at hw₀
  obtain ⟨x, hx⟩ := hw₀
  have hU := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν ∅
    (Set.empty_subset _)
  let x' : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅) := x
  have hweq : w = map F P₀ G p₀ (map F _ P₀ (Standard.unipotentToParabolic i ν ∅) x') := by
    rw [← map_comp_apply_of_hom (p := p₀), Standard.unipotentToParabolic_comp, map_apply,
      GroupScheme.affinePointsTarget_apply]
    exact hx.symm
  rw [hweq]
  exact hK.height_unipotent_mul hU _ x' g

include hG hi hν in
/-- The minimal-parabolic height is left invariant under `Λ₀ ⊔ U_J(𝔸)`. -/
theorem height_cosetSubgroup_mul {J : Set (characterLattice T)} (hJ : J ⊆ Δ)
    {h : A} (hh : h ∈ cosetSubgroup F G i ν J) (g : A) : hK.height (h * g) = hK.height g := by
  have hcl : cosetSubgroup F G i ν J =
      Subgroup.closure ((minimalParabolicImage F G i ν : Set A) ∪
        (adelicPoints F G (standardUnipotent i ν J) : Set A)) :=
    Subgroup.sup_eq_closure _ _
  rw [hcl] at hh
  induction hh using Subgroup.closure_induction generalizing g with
  | mem x hx =>
    rcases hx with hx | hx
    · exact height_minimalParabolicImage_mul hK hx g
    · exact height_standardUnipotent_mul hK hG hi hν hJ hx g
  | one => rw [one_mul]
  | mul x y _ _ hx hy => rw [mul_assoc, hx, hy]
  | inv x _ hx =>
    have := hx (x⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    exact this.symm

section Orthant

variable {X D : Type*} [Fintype D] {r : ℕ}

/-- The central coordinate signed by the orthant `ε`: `y` if `ε j`, else `-y`. -/
def orthantCoord (ε : Fin r → Bool) (j : Fin r) (y : ℝ) : ℝ := if ε j then y else -y

/-- The linear log weight on the orthant `ε`: `∑_β ra_β x_β + ∑_j rb_j ε_j y_j`. -/
def orthantLogWeight (ra : D → ℝ) (rb : Fin r → ℝ) (ε : Fin r → Bool)
    (x : (D → ℝ) × (Fin r → ℝ)) : ℝ :=
  (∑ β, ra β * x.1 β) + ∑ j, rb j * orthantCoord ε j (x.2 j)

/-- The region where every root coordinate in `J` exceeds its threshold. -/
def leviRegion (τ : D → ℝ) (J : D → Prop) : Set ((D → ℝ) × (Fin r → ℝ)) :=
  {x | ∀ β, J β → τ β < x.1 β}

/-- The weight `exp(-2 ℓ_ε(c g))` on the region where the coordinates in `J` exceed their
thresholds, zero elsewhere, for a coordinate map `c`. -/
def orthantWeight (c : X → (D → ℝ) × (Fin r → ℝ)) (ra : D → ℝ) (rb : Fin r → ℝ) (τ : D → ℝ)
    (J : D → Prop) (ε : Fin r → Bool) (g : X) : ℝ≥0∞ :=
  (leviRegion τ J).indicator
    (fun x => ENNReal.ofReal (Real.exp (-2 * orthantLogWeight ra rb ε x))) (c g)

/-- The shifts: `a_β` in the root directions outside `J`, `z_j^{±1}` (outward in the orthant)
in the central directions. -/
def orthantShift [Group X] (a : D → X) (z : Fin r → X) (J : D → Prop) (ε : Fin r → Bool) :
    ({β : D // ¬ J β} ⊕ Fin r) → X :=
  Sum.elim (fun β => a β.1) (fun j => if ε j then z j else (z j)⁻¹)

/-- The heights: root coordinate minus threshold, and signed central coordinate plus one. -/
def orthantHeight (c : X → (D → ℝ) × (Fin r → ℝ)) (τ : D → ℝ) (J : D → Prop)
    (ε : Fin r → Bool) : ({β : D // ¬ J β} ⊕ Fin r) → X → ℝ :=
  Sum.elim (fun β g => (c g).1 β.1 - τ β.1) (fun j g => orthantCoord ε j ((c g).2 j) + 1)

end Orthant

section OrthantShift

variable {X D : Type*} [Fintype D] [DecidableEq D] {r : ℕ} [Group X]
  (c : X → (D → ℝ) × (Fin r → ℝ)) (a : D → X) (z : Fin r → X)
  (hca : ∀ β g, c (a β * g) = c g + (Pi.single β 1, 0))
  (hcz : ∀ j g, c (z j * g) = c g + (0, Pi.single j 1))

include hcz in
theorem coords_inv_mul (j : Fin r) (g : X) :
    c ((z j)⁻¹ * g) = c g - (0, Pi.single j 1) := by
  have h := hcz j ((z j)⁻¹ * g)
  rw [mul_inv_cancel_left] at h
  rw [h]
  abel

/-- The rate of the orthant weight in each direction. -/
def orthantRate (ra : D → ℝ) (rb : Fin r → ℝ) (J : D → Prop) :
    ({β : D // ¬ J β} ⊕ Fin r) → ℝ :=
  Sum.elim (fun β => ra β.1) rb

include hca hcz in
/-- Each shift moves its own height up by one and leaves the other heights unchanged. -/
theorem orthantHeight_shift (τ : D → ℝ) (J : D → Prop) (ε : Fin r → Bool)
    (k l : {β : D // ¬ J β} ⊕ Fin r) (g : X) :
    orthantHeight c τ J ε l (orthantShift a z J ε k * g) =
      orthantHeight c τ J ε l g + if k = l then 1 else 0 := by
  rcases k with β | j <;> rcases l with β' | j'
  · simp only [orthantShift, orthantHeight, Sum.elim_inl, hca, Prod.fst_add, Pi.add_apply,
      Sum.inl.injEq]
    by_cases h : β = β'
    · subst h; simp; ring
    · have h' : β.1 ≠ β'.1 := fun h'' => h (Subtype.ext h'')
      simp [h, Pi.single_eq_of_ne' h']
  · simp [orthantShift, orthantHeight, hca]
  · simp only [orthantShift, orthantHeight, Sum.elim_inr, Sum.elim_inl, reduceCtorEq, ↓reduceIte,
      add_zero]
    split_ifs
    · simp [hcz]
    · simp [coords_inv_mul c z hcz]
  · simp only [orthantShift, orthantHeight, Sum.elim_inr, Sum.inr.injEq]
    by_cases h : j = j'
    · subst h
      by_cases hε : ε j
      · simp [hε, hcz, orthantCoord]
      · simp [hε, coords_inv_mul c z hcz, orthantCoord]; ring
    · by_cases hε : ε j
      · simp [hε, hcz, h]
      · simp [hε, coords_inv_mul c z hcz, h]

include hca hcz in
/-- The orthant weight scales by `exp(2 rate)` under each shift. -/
theorem orthantWeight_shift (ra : D → ℝ) (rb : Fin r → ℝ) (τ : D → ℝ) (J : D → Prop)
    (ε : Fin r → Bool) (k : {β : D // ¬ J β} ⊕ Fin r) (g : X) :
    orthantWeight c ra rb τ J ε g =
      ENNReal.ofReal (Real.exp (2 * orthantRate ra rb J k)) *
        orthantWeight c ra rb τ J ε (orthantShift a z J ε k * g) := by
  have hreg : (c (orthantShift a z J ε k * g) ∈ leviRegion τ J) ↔ c g ∈ leviRegion τ J := by
    rcases k with β | j
    · simp only [orthantShift, Sum.elim_inl, hca, leviRegion, Set.mem_ofPred_eq, Prod.fst_add,
        Pi.add_apply]
      refine forall_congr' fun β' => imp_congr_right fun hβ' => ?_
      have hne : β.1 ≠ β' := fun h => β.2 (h ▸ hβ')
      rw [Pi.single_eq_of_ne' hne, add_zero]
    · simp only [orthantShift, Sum.elim_inr, leviRegion, Set.mem_ofPred_eq]
      split_ifs
      · simp [hcz]
      · simp [coords_inv_mul c z hcz]
  have hlog : orthantLogWeight ra rb ε (c (orthantShift a z J ε k * g)) =
      orthantLogWeight ra rb ε (c g) + orthantRate ra rb J k := by
    rcases k with β | j
    · simp only [orthantShift, orthantRate, Sum.elim_inl, hca, orthantLogWeight, Prod.fst_add,
        Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero, mul_add, Finset.sum_add_distrib]
      simp [Pi.single_apply, mul_ite]
      ring
    · simp only [orthantShift, orthantRate, Sum.elim_inr]
      split_ifs with hε
      · simp only [hcz, orthantLogWeight, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Pi.zero_apply, add_zero]
        have : ∀ j', rb j' * orthantCoord ε j' ((c g).2 j' + (Pi.single j 1 : Fin r → ℝ) j') =
            rb j' * orthantCoord ε j' ((c g).2 j') + (Pi.single j (rb j) : Fin r → ℝ) j' := by
          intro j'
          by_cases h : j' = j
          · subst h; simp [orthantCoord, hε]; ring
          · simp [Pi.single_eq_of_ne h]
        simp only [this, Finset.sum_add_distrib, Finset.sum_pi_single']
        simp
        ring
      · simp only [coords_inv_mul c z hcz, orthantLogWeight, Prod.fst_sub, Prod.snd_sub,
          Pi.sub_apply, Pi.zero_apply, sub_zero]
        have : ∀ j', rb j' * orthantCoord ε j' ((c g).2 j' - (Pi.single j 1 : Fin r → ℝ) j') =
            rb j' * orthantCoord ε j' ((c g).2 j') + (Pi.single j (rb j) : Fin r → ℝ) j' := by
          intro j'
          by_cases h : j' = j
          · subst h; simp [orthantCoord, hε]; ring
          · simp [Pi.single_eq_of_ne h]
        simp only [this, Finset.sum_add_distrib, Finset.sum_pi_single']
        simp
        ring
  unfold orthantWeight
  by_cases hg : c g ∈ leviRegion τ J
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hreg.mpr hg), hlog,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hreg.mp h)), mul_zero]

end OrthantShift

section Continuity

variable {D : Type*} [Fintype D] {r : ℕ}

theorem continuous_orthantLogWeight (ra : D → ℝ) (rb : Fin r → ℝ) (ε : Fin r → Bool) :
    Continuous (orthantLogWeight ra rb ε) := by
  have h₂ (j : Fin r) : Continuous fun x : (D → ℝ) × (Fin r → ℝ) =>
      rb j * orthantCoord ε j (x.2 j) := by
    unfold orthantCoord
    by_cases hε : ε j
    · simp only [hε, ↓reduceIte]; fun_prop
    · simp only [hε, Bool.false_eq_true, ↓reduceIte]; fun_prop
  unfold orthantLogWeight
  exact (continuous_finsetSum _ fun β _ => by fun_prop).add (continuous_finsetSum _ fun j _ => h₂ j)

theorem measurableSet_leviRegion (τ : D → ℝ) (J : D → Prop) :
    MeasurableSet (leviRegion (r := r) τ J) := by
  have h : leviRegion (r := r) τ J = ⋂ β, ⋂ (_ : J β), {x | τ β < x.1 β} := by
    ext x; simp [leviRegion]
  rw [h]
  exact MeasurableSet.iInter fun β => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const ((measurable_pi_apply β).comp measurable_fst)

end Continuity

/-- The sufficient coefficient condition of the slab estimates. -/
theorem lowerMass_lt_pow {m : ℕ} (p : Fin m → ℂ) {f : ℝ} (hf : 1 ≤ f) (hp : ∑ q, ‖p q‖ < f) :
    ∑ q, ‖p q‖ * f ^ (q : ℕ) < f ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    have hm : 0 < f ^ m := pow_pos (by linarith) _
    calc
      ∑ q, ‖p q‖ * f ^ (q : ℕ) ≤ (∑ q, ‖p q‖) * f ^ m := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hf (Nat.le_of_lt_succ q.isLt)) (norm_nonneg _)
      _ < f * f ^ m := mul_lt_mul_of_pos_right hp hm
      _ = f ^ (m + 1) := (pow_succ' _ _).symm

/-- For a positive constant `c`, the factor `√(exp(2R) c)` exceeds any bound once `R` is large. -/
theorem exists_rate_factor_gt (c : ℝ≥0) (hc : 0 < c) (M : ℝ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      1 ≤ (NNReal.sqrt ((Real.exp (2 * R)).toNNReal * c) : ℝ) ∧
      M < (NNReal.sqrt ((Real.exp (2 * R)).toNNReal * c) : ℝ) := by
  refine ⟨Real.log (max 1 M + 1) - Real.log (Real.sqrt c), fun R hR => ?_⟩
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr (by exact_mod_cast hc)
  have heq : (NNReal.sqrt ((Real.exp (2 * R)).toNNReal * c) : ℝ) =
      Real.exp R * Real.sqrt c := by
    rw [Real.coe_sqrt, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Real.sqrt_mul (Real.exp_pos _).le,
      show 2 * R = R + R by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [heq]
  have hlog : Real.log (max 1 M + 1) ≤ R + Real.log (Real.sqrt c) := by linarith
  have hpos : 0 < max 1 M + 1 := by positivity
  have hle : max 1 M + 1 ≤ Real.exp R * Real.sqrt c := by
    rw [← Real.exp_log hpos, ← Real.exp_log hsc, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hlog
  constructor
  · linarith [le_max_left 1 M]
  · linarith [le_max_right 1 M]

section Estimate

variable [Fintype (simpleRelativeRoots i ν)] [DecidableEq (simpleRelativeRoots i ν)] {r : ℕ}
  (e : RealCharacterDual F (Standard.parabolicScheme i ν ∅) ≃L[ℝ]
    ((simpleRelativeRoots i ν → ℝ) × (Fin r → ℝ)))

/-- The chamber coordinates `g ↦ e(H₀(g))`. -/
def chamberCoords (g : AdelicGroupPoints F G) : (Δ → ℝ) × (Fin r → ℝ) := e (hK.height g)

theorem continuous_chamberCoords : Continuous (chamberCoords hK e) :=
  e.continuous.comp hK.continuous_height

include hG hi hν in
theorem chamberCoords_cosetSubgroup_mul {J : Set (characterLattice T)} (hJ : J ⊆ Δ)
    {h : AdelicGroupPoints F G} (hh : h ∈ cosetSubgroup F G i ν J) (g : AdelicGroupPoints F G) :
    chamberCoords hK e (h * g) = chamberCoords hK e g := by
  unfold chamberCoords
  rw [height_cosetSubgroup_mul hK hG hi hν hJ hh g]

open scoped Classical in
include hG hi hν in
/-- **Slab estimate on a central orthant in chamber coordinates.** Let `a_β` and `z_j` shift
the root and central chamber coordinates by one, and let the `a_β` for `β ∉ J` and all `z_j`
commute with `L_J(𝔸)` and normalize `U_J(𝔸)`. For every bound `M` there is `R₀` such that, for
all rates at least `R₀` and all coefficient families with `∑_q ‖p_{kq}‖ ≤ M`, the slab
estimate of `exists_slabEstimate` holds for the orthant weight, heights and shifts. -/
theorem exists_orthantSlabEstimate (a : Δ → AdelicGroupPoints F G)
    (z : Fin r → AdelicGroupPoints F G)
    (hca : ∀ β g, chamberCoords hK e (a β * g) = chamberCoords hK e g + (Pi.single β 1, 0))
    (hcz : ∀ j g, chamberCoords hK e (z j * g) = chamberCoords hK e g + (0, Pi.single j 1))
    {J : Set (characterLattice T)} (hJ : J ⊆ Δ)
    (haL : ∀ β : Δ, β.val ∉ J →
      ∀ x ∈ adelicPoints F G (standardLevi i ν J), a β * x = x * a β)
    (haU : ∀ β : Δ, β.val ∉ J → ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a β * w * (a β)⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
    (haU' : ∀ β : Δ, β.val ∉ J → ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      (a β)⁻¹ * w * a β ∈ adelicPoints F G (standardUnipotent i ν J))
    (hzL : ∀ j, ∀ x ∈ adelicPoints F G (standardLevi i ν J), z j * x = x * z j)
    (hzU : ∀ j, ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      z j * w * (z j)⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
    (hzU' : ∀ j, ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      (z j)⁻¹ * w * z j ∈ adelicPoints F G (standardUnipotent i ν J))
    (τ : Δ → ℝ) (ε : Fin r → Bool) (M : ℝ) :
    ∃ R₀ : ℝ, ∀ (ra : Δ → ℝ) (rb : Fin r → ℝ), (∀ β, R₀ ≤ ra β) → (∀ j, R₀ ≤ rb j) →
    ∀ (m : ({β : Δ // ¬ (fun β : Δ => β.val ∈ J) β} ⊕ Fin r) → ℕ) (p : ∀ k, Fin (m k) → ℂ),
    (∀ k, ∑ q, ‖p k q‖ ≤ M) →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {φ : AdelicGroupPoints F G → ℂ}, Measurable φ →
      (∀ h ∈ cosetSubgroup F G i ν J, ∀ g, φ (h * g) = φ g) →
      MemLp φ 2 ((domainWeightedHaar F G i ν
          (orthantWeight (chamberCoords hK e) ra rb τ (fun β : Δ => β.val ∈ J) ε)).restrict
        {g | ∀ k, 0 < orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g ∧
          orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g ≤ m k}) →
      (∀ k, MemLp (residualFun F G (orthantShift a z (fun β : Δ => β.val ∈ J) ε k) (p k) φ) 2
        ((domainWeightedHaar F G i ν
          (orthantWeight (chamberCoords hK e) ra rb τ (fun β : Δ => β.val ∈ J) ε)).restrict
          {g | ∀ k, 0 < orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g})) →
      MemLp φ 2 ((domainWeightedHaar F G i ν
          (orthantWeight (chamberCoords hK e) ra rb τ (fun β : Δ => β.val ∈ J) ε)).restrict
          {g | ∀ k, 0 < orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g}) ∧
      lpNorm φ 2 ((domainWeightedHaar F G i ν
          (orthantWeight (chamberCoords hK e) ra rb τ (fun β : Δ => β.val ∈ J) ε)).restrict
          {g | ∀ k, 0 < orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g}) ≤
        C * (lpNorm φ 2 ((domainWeightedHaar F G i ν
          (orthantWeight (chamberCoords hK e) ra rb τ (fun β : Δ => β.val ∈ J) ε)).restrict
          {g | ∀ k, 0 < orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g ∧
            orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g ≤ m k}) +
          ∑ k, lpNorm (residualFun F G (orthantShift a z (fun β : Δ => β.val ∈ J) ε k) (p k) φ) 2
            ((domainWeightedHaar F G i ν
              (orthantWeight (chamberCoords hK e) ra rb τ (fun β : Δ => β.val ∈ J) ε)).restrict
              {g | ∀ k, 0 < orthantHeight (chamberCoords hK e) τ (fun β : Δ => β.val ∈ J) ε k g})) := by
  classical
  set c := chamberCoords hK e with hc
  set Jp : Δ → Prop := fun β : Δ => β.val ∈ J with hJp
  set b := orthantShift a z Jp ε with hb
  have hbL : ∀ k, ∀ x ∈ adelicPoints F G (standardLevi i ν J), b k * x = x * b k := by
    rintro (β | j) x hx
    · exact haL β.1 β.2 x hx
    · simp only [hb, orthantShift, Sum.elim_inr]
      split_ifs
      · exact hzL j x hx
      · have h := hzL j x hx
        calc (z j)⁻¹ * x = (z j)⁻¹ * (x * z j) * (z j)⁻¹ := by group
          _ = (z j)⁻¹ * (z j * x) * (z j)⁻¹ := by rw [h]
          _ = x * (z j)⁻¹ := by group
  have hbU : ∀ k, ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      b k * w * (b k)⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J) := by
    rintro (β | j) w hw
    · exact haU β.1 β.2 w hw
    · simp only [hb, orthantShift, Sum.elim_inr]
      split_ifs
      · exact hzU j w hw
      · simpa only [inv_inv] using hzU' j w hw
  have hbU' : ∀ k, ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      (b k)⁻¹ * w * b k ∈ adelicPoints F G (standardUnipotent i ν J) := by
    rintro (β | j) w hw
    · exact haU' β.1 β.2 w hw
    · simp only [hb, orthantShift, Sum.elim_inr]
      split_ifs
      · exact hzU' j w hw
      · simpa only [inv_inv] using hzU j w hw
  have hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
  have : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
    hcl.locallyCompactSpace
  let cst : ({β : Δ // ¬ Jp β} ⊕ Fin r) → ℝ≥0 := fun k =>
    mulEquivHaarChar (conjPoints F G (b k) (hbU k) (hbU' k))
  have hcst (k) : 0 < cst k := mulEquivHaarChar_pos _
  choose R hR using fun k => exists_rate_factor_gt (cst k) (hcst k) M
  refine ⟨∑ k, |R k|, fun ra rb hra hrb m p hp => ?_⟩
  have hRk (k) : R k ≤ ∑ k, |R k| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun l _ => abs_nonneg (R l)) (Finset.mem_univ k))
  have hrate (k) : R k ≤ orthantRate ra rb Jp k := by
    rcases k with β | j
    · exact (hRk _).trans (hra β.1)
    · exact (hRk _).trans (hrb j)
  let κ : ({β : Δ // ¬ Jp β} ⊕ Fin r) → ℝ≥0 := fun k =>
    (Real.exp (2 * orthantRate ra rb Jp k)).toNNReal
  have hκ (k) : 0 < κ k := Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hcm : Measurable c := (continuous_chamberCoords hK e).measurable
  have hWm : Measurable (orthantWeight c ra rb τ Jp ε) := by
    have h₁ : Measurable fun x : (Δ → ℝ) × (Fin r → ℝ) =>
        ENNReal.ofReal (Real.exp (-2 * orthantLogWeight ra rb ε x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (continuous_orthantLogWeight ra rb ε).measurable))
    exact (h₁.indicator (measurableSet_leviRegion τ Jp)).comp hcm
  have hWH : ∀ h ∈ cosetSubgroup F G i ν J, ∀ g,
      orthantWeight c ra rb τ Jp ε (h * g) = orthantWeight c ra rb τ Jp ε g := by
    intro h hh g
    simp only [orthantWeight, hc, chamberCoords_cosetSubgroup_mul hK hG hi hν e hJ hh g]
  have hW : ∀ k g, orthantWeight c ra rb τ Jp ε g =
      κ k * orthantWeight c ra rb τ Jp ε (b k * g) := fun k g =>
    orthantWeight_shift c a z hca hcz ra rb τ Jp ε k g
  have htm : ∀ k, Measurable (orthantHeight c τ Jp ε k) := by
    rintro (β | j)
    · exact (((measurable_pi_apply β.1).comp measurable_fst).comp hcm).sub_const _
    · refine Measurable.add_const ?_ _
      unfold orthantCoord
      by_cases hε : ε j
      · simp only [hε, ↓reduceIte]
        exact ((measurable_pi_apply j).comp measurable_snd).comp hcm
      · simp only [hε, Bool.false_eq_true, ↓reduceIte]
        exact (((measurable_pi_apply j).comp measurable_snd).comp hcm).neg
  have htH : ∀ k, ∀ h ∈ cosetSubgroup F G i ν J, ∀ g,
      orthantHeight c τ Jp ε k (h * g) = orthantHeight c τ Jp ε k g := by
    rintro (β | j) h hh g <;>
      simp only [orthantHeight, Sum.elim_inl, Sum.elim_inr, hc,
        chamberCoords_cosetSubgroup_mul hK hG hi hν e hJ hh g]
  have hta : ∀ k l g, orthantHeight c τ Jp ε l (b k * g) =
      orthantHeight c τ Jp ε l g + if k = l then 1 else 0 := fun k l g =>
    orthantHeight_shift c a z hca hcz τ Jp ε k l g
  have hsmall : ∀ k, ∑ q, ‖p k q‖ * (NNReal.sqrt (κ k * cst k) : ℝ) ^ (q : ℕ) <
      (NNReal.sqrt (κ k * cst k) : ℝ) ^ m k := by
    intro k
    obtain ⟨h1, hM⟩ := hR k _ (hrate k)
    exact lowerMass_lt_pow (p k) h1 ((hp k).trans_lt hM)
  exact exists_slabEstimate F G i ν (hG := hG) (hi := hi) (hν := hν) hJ b hbL hbU hbU' hWm hWH κ hκ
    hW (orthantHeight c τ Jp ε) htm htH hta m p hsmall

end Estimate

end Langlands.Global.StandardConstantTerm
