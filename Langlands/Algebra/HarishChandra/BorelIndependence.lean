import Langlands.Algebra.HarishChandra.VermaWallCrossing

/-! # Independence of the Borel subalgebra for the shifted central characters

Let `𝔥` be a split Cartan subalgebra of a finite-dimensional complex Lie algebra `𝔤` and fix a
basis of simultaneous eigenvectors of `ad 𝔥`. For real-regular `X ∈ 𝔥` let `ρ_X` be half the sum
of the roots with positive real part at `X`. This file proves that for a central element `z` of
`U(𝔤)` the scalar congruent to `z` modulo the mirror Verma right ideal `R_X(λ + ρ_X)` does not
depend on `X`.

The proof joins two real-regular elements by a segment, after moving the endpoint inside its
chamber so that no two non-proportional roots vanish at the same point of the segment. The
positive system then changes one root at a time along the segment, and each change is a wall
crossing in the sense of `Langlands.Algebra.HarishChandra.VermaWallCrossing`. -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

open LieModule Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

section WeightBasis

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

variable (H : LieSubalgebra ℂ L)

/-- A basis of simultaneous eigenvectors of `ad 𝔥` with linear weights, containing one vector for
each nonzero weight that occurs. -/
structure WeightBasis where
  /-- The number of basis vectors. -/
  n : ℕ
  /-- The basis. -/
  b : Module.Basis (Fin n) ℂ L
  /-- The weights, as linear forms on `𝔥`. -/
  w : Fin n → H →ₗ[ℂ] ℂ
  mem : ∀ a, b a ∈ weightSpace L ⇑(w a)
  line : ∀ a a', ⇑(w a) ≠ 0 → w a = w a' → a = a'

variable {H}

theorem IsSplitCartan.nonempty_weightBasis [FiniteDimensional ℂ L] (hC : IsSplitCartan H) :
    Nonempty (WeightBasis H) := by
  obtain ⟨r, b, χ, hb, hline, -⟩ := hC.exists_ordered_weight_basis 0
  have hne : ∀ a, weightSpace L (χ a) ≠ ⊥ := fun a => weightSpace_ne_bot_of_mem (hb a) (b.ne_zero a)
  exact ⟨⟨r, b, fun a => weightForm (hne a), hb, fun a a' ha h =>
    hline a a' ha (congrArg DFunLike.coe h)⟩⟩

namespace WeightBasis

variable (B : WeightBasis H)

theorem weightSpace_ne_bot (a : Fin B.n) : weightSpace L ⇑(B.w a) ≠ ⊥ :=
  weightSpace_ne_bot_of_mem (B.mem a) (B.b.ne_zero a)

/-- Every root is the weight of a basis vector. -/
theorem exists_index {χ : H → ℂ} (hbot : weightSpace L χ ≠ ⊥) : ∃ a, ⇑(B.w a) = χ := by
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_weightSpace_ne_bot hbot
  have hsupp : B.b.repr x ≠ 0 := fun h => hx0 (B.b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hsupp
  exact ⟨a, weight_eq_of_basis_repr_ne_zero B.b (fun a => ⇑(B.w a)) B.mem hx
    (Finsupp.mem_support_iff.mp ha)⟩

theorem line' (a a' : Fin B.n) (ha : ⇑(B.w a) ≠ 0) (h : ⇑(B.w a) = ⇑(B.w a')) : a = a' :=
  B.line a a' ha (LinearMap.coe_injective h)

/-- The negative of a root is a root. -/
theorem exists_neg (hC : IsSplitCartan H) (a : Fin B.n) (ha : ⇑(B.w a) ≠ 0) :
    ∃ a', B.w a' = -B.w a := by
  obtain ⟨e, -, f, hf, h, hef, hval⟩ := hC.exists_sl2 (⇑(B.w a)) ha (B.weightSpace_ne_bot a)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [lie_zero] at hef
    have h0 : h = 0 := Subtype.ext hef.symm
    rw [h0, map_zero] at hval
    exact two_ne_zero hval.symm
  obtain ⟨a', ha'⟩ := B.exists_index (weightSpace_ne_bot_of_mem hf hf0)
  exact ⟨a', LinearMap.coe_injective (by rw [ha', LinearMap.coe_neg])⟩

theorem isRealRegular_iff (X : H) :
    IsRealRegular H X ↔ ∀ a, ⇑(B.w a) ≠ 0 → (B.w a X).re ≠ 0 := by
  constructor
  · intro hX a ha
    exact hX _ ha (B.weightSpace_ne_bot a)
  · intro h χ hχ hbot
    obtain ⟨a, rfl⟩ := B.exists_index hbot
    exact h a hχ

theorem ne_zero_of_re_ne_zero {a : Fin B.n} {X : H} (h : (B.w a X).re ≠ 0) : ⇑(B.w a) ≠ 0 := by
  intro h0
  apply h
  rw [show B.w a X = (⇑(B.w a)) X from rfl, h0, Pi.zero_apply, Complex.zero_re]

/-- Half the sum of the roots with positive real part at `X`. -/
def rho (X : H) : H →ₗ[ℂ] ℂ :=
  (2 : ℂ)⁻¹ • ∑ a ∈ Finset.univ.filter (fun a => 0 < (B.w a X).re), B.w a

/-- Elements with the same positive roots have the same positive root submodule and the same
`ρ`. -/
theorem positiveRootSubmodule_eq_of_iff {X X' : H}
    (h : ∀ a, 0 < (B.w a X).re ↔ 0 < (B.w a X').re) :
    positiveRootSubmodule H X = positiveRootSubmodule H X' := by
  have key : ∀ {Y Y' : H}, (∀ a, 0 < (B.w a Y).re ↔ 0 < (B.w a Y').re) →
      positiveRootSubmodule H Y ≤ positiveRootSubmodule H Y' := by
    intro Y Y' hY
    refine iSup₂_le fun χ hχ => ?_
    by_cases hbot : weightSpace L χ = ⊥
    · rw [hbot]
      exact bot_le
    obtain ⟨a, rfl⟩ := B.exists_index hbot
    exact le_iSup₂_of_le (f := fun (χ : H → ℂ) (_ : 0 < (χ Y').re) =>
      (weightSpace L χ : Submodule ℂ L)) _ ((hY a).mp hχ) le_rfl
  exact le_antisymm (key h) (key fun a => (h a).symm)

theorem rho_eq_of_iff {X X' : H} (h : ∀ a, 0 < (B.w a X).re ↔ 0 < (B.w a X').re) :
    B.rho X = B.rho X' := by
  rw [rho, rho]
  congr 2
  ext a
  simp [h a]

theorem vermaIdeal_eq_of_iff {X X' : H} (h : ∀ a, 0 < (B.w a X).re ↔ 0 < (B.w a X').re)
    (lam : H →ₗ[ℂ] ℂ) : vermaIdeal H X lam = vermaIdeal H X' lam := by
  rw [vermaIdeal, vermaIdeal, B.positiveRootSubmodule_eq_of_iff h]

/-- Across a wall the shifts differ by the crossed root. -/
theorem rho_sub_rho_of_wallCrossing {X X' : H} {α : H →ₗ[ℂ] ℂ} {e f : L} {h : H}
    (W : WallCrossing X X' α e f h) : B.rho X - B.rho X' = α := by
  classical
  obtain ⟨ap, hap⟩ := B.exists_index W.weightSpace_alpha_ne_bot
  obtain ⟨am, ham⟩ := B.exists_index W.weightSpace_neg_alpha_ne_bot
  have hap' : B.w ap = α := LinearMap.coe_injective hap
  have ham' : B.w am = -α := LinearMap.coe_injective (by rw [ham, LinearMap.coe_neg])
  set S := Finset.univ.filter (fun a => 0 < (B.w a X).re)
  set S' := Finset.univ.filter (fun a => 0 < (B.w a X').re)
  have hmemp : ap ∈ S := by simp [S, hap', W.pos]
  have hmemm : am ∈ S' := by
    simp only [S', Finset.mem_filter, Finset.mem_univ, true_and, ham', LinearMap.neg_apply,
      Complex.neg_re]
    exact neg_pos.mpr W.neg
  have herase : S.erase ap = S'.erase am := by
    ext a
    simp only [S, S', Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h0 : ⇑(B.w a) = 0
    · have h1 : B.w a X = 0 := by rw [show B.w a X = (⇑(B.w a)) X from rfl, h0, Pi.zero_apply]
      have h2 : B.w a X' = 0 := by rw [show B.w a X' = (⇑(B.w a)) X' from rfl, h0, Pi.zero_apply]
      simp [h1, h2]
    by_cases hp : ⇑(B.w a) = ⇑α
    · have : a = ap := B.line' a ap h0 (hp.trans hap.symm)
      subst this
      simp only [ne_eq, not_true_eq_false, false_and, false_iff, not_and]
      intro _ hpos
      rw [hap'] at hpos
      exact absurd W.neg (not_lt.mpr hpos.le)
    by_cases hn : ⇑(B.w a) = -⇑α
    · have : a = am := B.line' a am h0 (hn.trans ham.symm)
      subst this
      simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_and]
      intro _ hpos
      rw [ham', LinearMap.neg_apply, Complex.neg_re] at hpos
      exact absurd W.pos (not_lt.mpr (by linarith))
    have hnep : a ≠ ap := fun h' => hp (h' ▸ hap)
    have hnem : a ≠ am := fun h' => hn (h' ▸ ham)
    simp only [ne_eq, hnep, hnem, not_false_eq_true, true_and]
    exact W.adj _ h0 (B.weightSpace_ne_bot a) hp hn
  rw [rho, rho, ← Finset.add_sum_erase S _ hmemp, ← Finset.add_sum_erase S' _ hmemm, herase,
    hap', ham']
  ext x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.neg_apply, smul_eq_mul]
  ring

/-- The wall-crossing identity with the shifts by `ρ`. -/
theorem sub_mem_vermaIdeal_rho_of_wallCrossing [FiniteDimensional ℂ L] (hC : IsSplitCartan H)
    {X X' : H} {α : H →ₗ[ℂ] ℂ} {e f : L} {h : H} (W : WallCrossing X X' α e f h)
    (hX : IsRealRegular H X) (hX' : IsRealRegular H X') (lam : H →ₗ[ℂ] ℂ) {z : U}
    (hz : z ∈ Subalgebra.center ℂ U) {s : ℂ}
    (h₁ : z - algebraMap ℂ U s ∈ vermaIdeal H X (lam + B.rho X)) :
    z - algebraMap ℂ U s ∈ vermaIdeal H X' (lam + B.rho X') := by
  have := W.sub_mem_vermaIdeal hC hX hX' (lam + B.rho X) hz h₁
  have heq : lam + B.rho X - α = lam + B.rho X' := by
    rw [← B.rho_sub_rho_of_wallCrossing W]
    abel
  rwa [heq] at this

end WeightBasis

end WeightBasis

section RealFunctionals

/-- Finitely many nonzero real-linear functionals on a complex vector space have a common
point where none of them vanishes. -/
theorem exists_forall_ne_zero_of_real_linear {V : Type*} [AddCommGroup V] [Module ℂ V]
    {κ : Type*} (s : Finset κ) (φ : κ → V → ℝ)
    (hadd : ∀ i x y, φ i (x + y) = φ i x + φ i y)
    (hsmul : ∀ i (r : ℝ) x, φ i ((r : ℂ) • x) = r * φ i x)
    (hne : ∀ i ∈ s, ∃ x, φ i x ≠ 0) : ∃ Z, ∀ i ∈ s, φ i Z ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s hj ih =>
    obtain ⟨Z, hZ⟩ := ih fun i hi => hne i (Finset.mem_insert_of_mem hi)
    by_cases hjZ : φ j Z ≠ 0
    · exact ⟨Z, fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hjZ
        · exact hZ i hi⟩
    push Not at hjZ
    obtain ⟨Y, hY⟩ := hne j (Finset.mem_insert_self j s)
    let bad : Finset ℝ := insert 0 (s.image fun i => -φ i Z / φ i Y)
    obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset bad
    refine ⟨Z + (r : ℂ) • Y, fun i hi => ?_⟩
    rw [hadd, hsmul]
    have hr0 : r ≠ 0 := fun h => hr (h ▸ Finset.mem_insert_self 0 _)
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hjZ, zero_add]
      exact mul_ne_zero hr0 hY
    · intro h0
      by_cases hiY : φ i Y = 0
      · rw [hiY, mul_zero, add_zero] at h0
        exact hZ i hi h0
      · apply hr
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, ?_⟩)
        field_simp
        linarith

end RealFunctionals

namespace WeightBasis

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L] {H : LieSubalgebra ℂ L} (B : WeightBasis H)

local notation "U" => UniversalEnvelopingAlgebra ℂ L

theorem re_add_smul (a : Fin B.n) (X Z : H) (t : ℝ) :
    (B.w a (X + (t : ℂ) • Z)).re = (B.w a X).re + t * (B.w a Z).re := by
  rw [map_add, map_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]

theorem re_segment (a : Fin B.n) (X X' : H) (t : ℝ) :
    (B.w a (X + (t : ℂ) • (X' - X))).re = (1 - t) * (B.w a X).re + t * (B.w a X').re := by
  rw [re_add_smul, map_sub, Complex.sub_re]
  ring

/-- The determinant of the real parts of two roots at two elements of `𝔥`; it vanishes when both
roots vanish at a common point of the segment joining them. -/
def det (a a' : Fin B.n) (X X' : H) : ℝ :=
  (B.w a X).re * (B.w a' X').re - (B.w a' X).re * (B.w a X').re

/-- No two non-proportional roots vanish at a common point of the segment from `X` to `X'`. -/
def IsGeneric (X X' : H) : Prop :=
  ∀ a a', ⇑(B.w a) ≠ 0 → ⇑(B.w a') ≠ 0 → B.w a ≠ B.w a' → B.w a ≠ -B.w a' →
    B.det a a' X X' ≠ 0

/-- The roots positive at `X` and negative at `X'`. -/
def crossings (X X' : H) : Finset (Fin B.n) :=
  Finset.univ.filter fun a => 0 < (B.w a X).re ∧ (B.w a X').re < 0

theorem re_ne_zero {X : H} (hX : IsRealRegular H X) {a : Fin B.n} (ha : ⇑(B.w a) ≠ 0) :
    (B.w a X).re ≠ 0 :=
  (B.isRealRegular_iff X).mp hX a ha

theorem iff_of_crossings_eq_empty (hC : IsSplitCartan H) {X X' : H} (hX : IsRealRegular H X)
    (hX' : IsRealRegular H X') (h : B.crossings X X' = ∅) (a : Fin B.n) :
    0 < (B.w a X).re ↔ 0 < (B.w a X').re := by
  have hmem : ∀ a, ¬ (0 < (B.w a X).re ∧ (B.w a X').re < 0) := fun a ha => by
    have : a ∈ B.crossings X X' := by simp [crossings, ha]
    rw [h] at this
    exact Finset.notMem_empty a this
  constructor
  · intro hA
    have ha0 := B.ne_zero_of_re_ne_zero hA.ne'
    have hB := B.re_ne_zero hX' ha0
    by_contra hneg
    exact hmem a ⟨hA, lt_of_le_of_ne (not_lt.mp hneg) hB⟩
  · intro hB
    have ha0 := B.ne_zero_of_re_ne_zero hB.ne'
    have hA := B.re_ne_zero hX ha0
    by_contra hneg
    obtain ⟨a', ha'⟩ := B.exists_neg hC a ha0
    apply hmem a'
    rw [ha', LinearMap.neg_apply, LinearMap.neg_apply, Complex.neg_re, Complex.neg_re]
    exact ⟨neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hneg) hA), neg_neg_of_pos hB⟩

/-- One step along a generic segment: cross the first wall. -/
theorem exists_step (hC : IsSplitCartan H) {X X' : H} (hX : IsRealRegular H X)
    (hX' : IsRealRegular H X') (hgen : B.IsGeneric X X') (hne : (B.crossings X X').Nonempty) :
    ∃ (X'' : H) (α : H →ₗ[ℂ] ℂ) (e f : L) (h : H), WallCrossing X X'' α e f h ∧
      IsRealRegular H X'' ∧ B.IsGeneric X'' X' ∧
      (B.crossings X'' X').card + 1 = (B.crossings X X').card := by
  classical
  set S := B.crossings X X' with hS
  let A : Fin B.n → ℝ := fun a => (B.w a X).re
  let C : Fin B.n → ℝ := fun a => (B.w a X').re
  let t : Fin B.n → ℝ := fun a => A a / (A a - C a)
  obtain ⟨a₀, ha₀S, hmin⟩ := S.exists_min_image t hne
  have hA₀ : 0 < A a₀ := (Finset.mem_filter.mp ha₀S).2.1
  have hC₀ : C a₀ < 0 := (Finset.mem_filter.mp ha₀S).2.2
  have hD₀ : 0 < A a₀ - C a₀ := by linarith
  have ht₀ : t a₀ < 1 := by
    rw [div_lt_one hD₀]
    linarith
  have hw₀ : ⇑(B.w a₀) ≠ 0 := B.ne_zero_of_re_ne_zero hA₀.ne'
  let S' := Finset.univ.filter fun a => A a * C a < 0
  have hmin' : ∀ a ∈ S', t a₀ ≤ t a := by
    intro a ha
    have hAC : A a * C a < 0 := (Finset.mem_filter.mp ha).2
    rcases lt_or_gt_of_ne (show A a ≠ 0 by rintro h; rw [h, zero_mul] at hAC; exact lt_irrefl 0 hAC)
      with hA | hA
    · have hCpos : 0 < C a := by
        by_contra hc
        push Not at hc
        nlinarith
      obtain ⟨a', ha'⟩ := B.exists_neg hC a (B.ne_zero_of_re_ne_zero hA.ne)
      have hA' : A a' = -A a := by simp [A, ha']
      have hC' : C a' = -C a := by simp [C, ha']
      have ha'S : a' ∈ S := by
        simp only [hS, crossings, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by change 0 < A a'; linarith, by change C a' < 0; linarith⟩
      have := hmin a' ha'S
      have htt : t a' = t a := by
        simp only [t, hA', hC']
        rw [show -A a - -C a = -(A a - C a) by ring, neg_div_neg_eq]
      linarith
    · have hCneg : C a < 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      exact hmin a (by
        simp only [hS, crossings, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hA, hCneg⟩)
  let T := (S'.filter fun a => t a₀ < t a).image t
  let m := (insert 1 T).min' (Finset.insert_nonempty _ _)
  have hm : t a₀ < m := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ht₀
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp ha).2
  have hm1 : m ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hmT : ∀ a ∈ S', t a₀ < t a → m ≤ t a := fun a ha hlt =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨ha, hlt⟩, rfl⟩))
  have ht₀pos : 0 < t a₀ := div_pos hA₀ hD₀
  set t' := (t a₀ + m) / 2 with ht'
  have ht'1 : t' < 1 := by rw [ht']; linarith
  have ht'0 : 0 < t' := by rw [ht']; linarith
  have ht't₀ : t a₀ < t' := by rw [ht']; linarith
  have ht'm : t' < m := by rw [ht']; linarith
  set X'' := X + (t' : ℂ) • (X' - X) with hX''
  let g : Fin B.n → ℝ := fun a => (1 - t') * A a + t' * C a
  have hg : ∀ a, (B.w a X'').re = g a := fun a => B.re_segment a X X' t'
  have hg₀ : g a₀ < 0 := by
    have h1 : t a₀ * (A a₀ - C a₀) = A a₀ := div_mul_cancel₀ _ hD₀.ne'
    have h2 : g a₀ = A a₀ - t' * (A a₀ - C a₀) := by simp only [g]; ring
    rw [h2]
    nlinarith
  have hgw : ∀ a, B.w a = B.w a₀ → g a = g a₀ := fun a h => by simp only [g, A, C, h]
  have hgn : ∀ a, B.w a = -B.w a₀ → g a = -g a₀ := fun a h => by
    simp only [g, A, C, h, LinearMap.neg_apply, Complex.neg_re]
    ring
  -- Behaviour of the roots other than `±α`.
  have hgen' : ∀ a, ⇑(B.w a) ≠ 0 → B.w a ≠ B.w a₀ → B.w a ≠ -B.w a₀ →
      (0 < g a ↔ 0 < A a) ∧ g a ≠ 0 := by
    intro a ha hp hn
    have hA := B.re_ne_zero hX ha
    have hCa := B.re_ne_zero hX' ha
    change A a ≠ 0 at hA
    change C a ≠ 0 at hCa
    by_cases hAC : A a * C a < 0
    · have haS' : a ∈ S' := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hAC⟩
      have htne : t a ≠ t a₀ := by
        intro heq
        apply hgen a a₀ ha hw₀ hp hn
        have hDa : A a - C a ≠ 0 := by
          intro h0
          have : A a = C a := by linarith
          rw [this] at hAC
          nlinarith
        simp only [t] at heq
        rw [div_eq_div_iff hDa hD₀.ne'] at heq
        simp only [det]
        change A a * C a₀ - A a₀ * C a = 0
        linear_combination -heq
      have hlt : t a₀ < t a := lt_of_le_of_ne (hmin' a haS') (Ne.symm htne)
      have ht'a : t' < t a := lt_of_lt_of_le ht'm (hmT a haS' hlt)
      rcases lt_or_gt_of_ne hA with hA' | hA'
      · have hCpos : 0 < C a := by
          by_contra hc
          push Not at hc
          nlinarith
        have hDa : A a - C a < 0 := by linarith
        have h1 : t a * (A a - C a) = A a := div_mul_cancel₀ _ hDa.ne
        have hgneg : g a < 0 := by
          have h2 : g a = A a - t' * (A a - C a) := by simp only [g]; ring
          rw [h2]
          nlinarith
        exact ⟨⟨fun h => absurd h (not_lt.mpr hgneg.le), fun h => absurd h (not_lt.mpr hA'.le)⟩,
          hgneg.ne⟩
      · have hCneg : C a < 0 := by
          by_contra hc
          push Not at hc
          nlinarith
        have hDa : 0 < A a - C a := by linarith
        have h1 : t a * (A a - C a) = A a := div_mul_cancel₀ _ hDa.ne'
        have hgpos : 0 < g a := by
          have h2 : g a = A a - t' * (A a - C a) := by simp only [g]; ring
          rw [h2]
          nlinarith
        exact ⟨⟨fun _ => hA', fun _ => hgpos⟩, hgpos.ne'⟩
    · push Not at hAC
      have hpos : 0 < A a * C a := lt_of_le_of_ne hAC (Ne.symm (mul_ne_zero hA hCa))
      rcases lt_or_gt_of_ne hA with hA' | hA'
      · have hC' : C a < 0 := by
          by_contra hc
          push Not at hc
          nlinarith
        have : g a < 0 := by simp only [g]; nlinarith
        exact ⟨⟨fun h => absurd h (not_lt.mpr this.le), fun h => absurd h (not_lt.mpr hA'.le)⟩,
          this.ne⟩
      · have hC' : 0 < C a := by
          by_contra hc
          push Not at hc
          nlinarith
        have : 0 < g a := by simp only [g]; nlinarith
        exact ⟨⟨fun _ => hA', fun _ => this⟩, this.ne'⟩
  obtain ⟨e, he, f, hf, h, hef, hval⟩ := hC.exists_sl2 (⇑(B.w a₀)) hw₀ (B.weightSpace_ne_bot a₀)
  refine ⟨X'', B.w a₀, e, f, h, ?_, ?_, ?_, ?_⟩
  · refine ⟨hA₀, by rw [hg]; exact hg₀, fun χ h0 hbot hp hn => ?_, he, hf, hef, hval⟩
    obtain ⟨a, rfl⟩ := B.exists_index hbot
    have hp' : B.w a ≠ B.w a₀ := fun h' => hp (congrArg DFunLike.coe h')
    have hn' : B.w a ≠ -B.w a₀ := fun h' => hn (by rw [h', LinearMap.coe_neg])
    change 0 < A a ↔ 0 < (B.w a X'').re
    rw [hg]
    exact (hgen' a h0 hp' hn').1.symm
  · rw [B.isRealRegular_iff]
    intro a ha
    rw [hg]
    by_cases hp : B.w a = B.w a₀
    · rw [hgw a hp]
      exact hg₀.ne
    by_cases hn : B.w a = -B.w a₀
    · rw [hgn a hn]
      exact (neg_pos.mpr hg₀).ne'
    exact (hgen' a ha hp hn).2
  · intro a a' ha ha' hp hn
    have hdet : B.det a a' X'' X' = (1 - t') * B.det a a' X X' := by
      simp only [det, hg, g, A, C]
      ring
    rw [hdet]
    exact mul_ne_zero (by linarith) (hgen a a' ha ha' hp hn)
  · have hcross : B.crossings X'' X' = S.erase a₀ := by
      ext a
      simp only [hS, crossings, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        hg]
      constructor
      · rintro ⟨hga, hCa⟩
        have ha := B.ne_zero_of_re_ne_zero hCa.ne
        have hp : B.w a ≠ B.w a₀ := fun h' => by
          rw [hgw a h'] at hga
          exact lt_asymm hga hg₀
        have hn : B.w a ≠ -B.w a₀ := fun h' => by
          have : C a = -C a₀ := by simp [C, h']
          change C a < 0 at hCa
          linarith
        refine ⟨fun h' => hp (h' ▸ rfl), (hgen' a ha hp hn).1.mp hga, hCa⟩
      · rintro ⟨hne₀, hAa, hCa⟩
        have ha := B.ne_zero_of_re_ne_zero hAa.ne'
        have hp : B.w a ≠ B.w a₀ := fun h' => hne₀ (B.line a a₀ ha h')
        have hn : B.w a ≠ -B.w a₀ := fun h' => by
          have : A a = -A a₀ := by simp [A, h']
          change 0 < A a at hAa
          linarith
        exact ⟨(hgen' a ha hp hn).1.mpr hAa, hCa⟩
    rw [hcross, Finset.card_erase_add_one ha₀S]

/-- Along a generic segment the shifted central characters agree. -/
theorem sub_mem_of_isGeneric [FiniteDimensional ℂ L] (hC : IsSplitCartan H) {X' : H}
    (hX' : IsRealRegular H X') (lam : H →ₗ[ℂ] ℂ) {z : U} (hz : z ∈ Subalgebra.center ℂ U)
    {s : ℂ} : ∀ (N : ℕ) (X : H), IsRealRegular H X → B.IsGeneric X X' →
      (B.crossings X X').card = N →
      z - algebraMap ℂ U s ∈ vermaIdeal H X (lam + B.rho X) →
      z - algebraMap ℂ U s ∈ vermaIdeal H X' (lam + B.rho X') := by
  intro N
  induction N with
  | zero =>
    intro X hX _ hN h₁
    have hiff := B.iff_of_crossings_eq_empty hC hX hX' (Finset.card_eq_zero.mp hN)
    rwa [← B.vermaIdeal_eq_of_iff hiff, ← B.rho_eq_of_iff hiff]
  | succ N ih =>
    intro X hX hgen hN h₁
    obtain ⟨X'', α, e, f, h, W, hX'', hgen'', hcard⟩ :=
      B.exists_step hC hX hX' hgen (Finset.card_pos.mp (by omega))
    exact ih X'' hX'' hgen'' (by omega)
      (B.sub_mem_vermaIdeal_rho_of_wallCrossing hC W hX hX'' lam hz h₁)

/-- An endpoint can be moved inside its chamber to make the segment generic. -/
theorem exists_generic (hC : IsSplitCartan H) {X X' : H} (hX : IsRealRegular H X)
    (hX' : IsRealRegular H X') :
    ∃ X'' : H, IsRealRegular H X'' ∧ (∀ a, 0 < (B.w a X'').re ↔ 0 < (B.w a X').re) ∧
      B.IsGeneric X X'' := by
  classical
  let P := Finset.univ.filter fun p : Fin B.n × Fin B.n =>
    ⇑(B.w p.1) ≠ 0 ∧ ⇑(B.w p.2) ≠ 0 ∧ B.w p.1 ≠ B.w p.2 ∧ B.w p.1 ≠ -B.w p.2
  let φ : Fin B.n × Fin B.n → H → ℝ := fun p Z => B.det p.1 p.2 X Z
  have hadd : ∀ p x y, φ p (x + y) = φ p x + φ p y := by
    intro p x y
    simp only [φ, det, map_add, Complex.add_re]
    ring
  have hsmul : ∀ p (r : ℝ) x, φ p ((r : ℂ) • x) = r * φ p x := by
    intro p r x
    simp only [φ, det, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
    ring
  have hne : ∀ p ∈ P, ∃ x, φ p x ≠ 0 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := (Finset.mem_filter.mp hp).2
    by_contra hall
    push Not at hall
    have hA := B.re_ne_zero hX h1
    set c : ℝ := (B.w p.2 X).re / (B.w p.1 X).re with hc
    have hre : ∀ Z, (B.w p.2 Z).re = c * (B.w p.1 Z).re := by
      intro Z
      have h0 := hall Z
      simp only [φ, det] at h0
      rw [hc, div_mul_eq_mul_div, eq_div_iff hA]
      linarith
    have him : ∀ (q : Fin B.n) (Z : H), (B.w q Z).im = -(B.w q (Complex.I • Z)).re := by
      intro q Z
      rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im]
      ring
    have hw : B.w p.2 = (c : ℂ) • B.w p.1 := by
      ext Z
      apply Complex.ext
      · rw [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, hre]
      · rw [LinearMap.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, him, him, hre]
        ring
    have hc0 : (c : ℂ) ≠ 0 := by
      intro h0
      apply h2
      rw [hw, h0, zero_smul]
      rfl
    have hbot : weightSpace L ((c : ℂ) • ⇑(B.w p.1)) ≠ ⊥ := by
      have := B.weightSpace_ne_bot p.2
      rwa [hw, LinearMap.coe_smul] at this
    rcases hC.reduced _ h1 (B.weightSpace_ne_bot p.1) _ hc0 hbot with h | h
    · exact h3 (by rw [hw, h, one_smul])
    · exact h4 (by rw [hw, h, neg_one_smul, neg_neg])
  obtain ⟨Z, hZ⟩ := exists_forall_ne_zero_of_real_linear P φ hadd hsmul hne
  let R := Finset.univ.filter fun a => ⇑(B.w a) ≠ 0
  let ε : Fin B.n → ℝ := fun a => |(B.w a X').re| / (|(B.w a Z).re| + 1)
  have hε : ∀ a ∈ R, 0 < ε a := fun a ha =>
    div_pos (abs_pos.mpr (B.re_ne_zero hX' (Finset.mem_filter.mp ha).2)) (by positivity)
  obtain ⟨δ₀, hδ₀, hδ₀ε⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ a ∈ R, δ₀ ≤ ε a := by
    by_cases hR : R.Nonempty
    · exact ⟨R.inf' hR ε, (Finset.lt_inf'_iff hR).mpr hε, fun a ha => Finset.inf'_le _ ha⟩
    · exact ⟨1, one_pos, fun a ha => absurd ⟨a, ha⟩ hR⟩
  let bad : Finset ℝ := P.image fun p => -B.det p.1 p.2 X X' / φ p Z
  obtain ⟨δ, hδ, hδbad⟩ := (Set.Ioo_infinite hδ₀).exists_notMem_finset bad
  have hsmall : ∀ a, ⇑(B.w a) ≠ 0 → |δ * (B.w a Z).re| < |(B.w a X').re| := by
    intro a ha
    have haR : a ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
    have h1 : δ < ε a := lt_of_lt_of_le hδ.2 (hδ₀ε a haR)
    have h2 : ε a * (|(B.w a Z).re| + 1) = |(B.w a X').re| := div_mul_cancel₀ _ (by positivity)
    rw [abs_mul, abs_of_pos hδ.1]
    nlinarith [abs_nonneg (B.w a Z).re, hδ.1]
  have hsign : ∀ a, ⇑(B.w a) ≠ 0 →
      (0 < (B.w a (X' + (δ : ℂ) • Z)).re ↔ 0 < (B.w a X').re) ∧
        (B.w a (X' + (δ : ℂ) • Z)).re ≠ 0 := by
    intro a ha
    rw [re_add_smul]
    have hb := hsmall a ha
    rcases lt_or_gt_of_ne (B.re_ne_zero hX' ha) with hC' | hC'
    · rw [abs_of_neg hC'] at hb
      have := (abs_lt.mp hb).2
      constructor
      · constructor
        · intro h
          linarith
        · intro h
          linarith
      · linarith
    · rw [abs_of_pos hC'] at hb
      have := (abs_lt.mp hb).1
      constructor
      · exact ⟨fun _ => hC', fun _ => by linarith⟩
      · linarith
  refine ⟨X' + (δ : ℂ) • Z, ?_, fun a => ?_, ?_⟩
  · rw [B.isRealRegular_iff]
    exact fun a ha => (hsign a ha).2
  · by_cases ha : ⇑(B.w a) = 0
    · have h1 : B.w a (X' + (δ : ℂ) • Z) = 0 := by
        rw [show B.w a (X' + (δ : ℂ) • Z) = (⇑(B.w a)) (X' + (δ : ℂ) • Z) from rfl, ha,
          Pi.zero_apply]
      have h2 : B.w a X' = 0 := by rw [show B.w a X' = (⇑(B.w a)) X' from rfl, ha, Pi.zero_apply]
      rw [h1, h2]
    · exact (hsign a ha).1
  · intro a a' ha ha' hp hn
    have hpP : (a, a') ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, ha', hp, hn⟩
    have hdet : B.det a a' X (X' + (δ : ℂ) • Z) = B.det a a' X X' + δ * φ (a, a') Z := by
      simp only [det, φ, re_add_smul]
      ring
    rw [hdet]
    intro h0
    apply hδbad
    refine Finset.mem_image.mpr ⟨(a, a'), hpP, ?_⟩
    have hφ := hZ (a, a') hpP
    field_simp
    linarith

/-- **Independence of the Borel subalgebra.** For central `z`, the scalar congruent to `z` modulo
`R_X(λ + ρ_X)` does not depend on the real-regular element `X`. -/
theorem sub_mem_vermaIdeal_rho [FiniteDimensional ℂ L] (hC : IsSplitCartan H) {X X' : H}
    (hX : IsRealRegular H X) (hX' : IsRealRegular H X') (lam : H →ₗ[ℂ] ℂ) {z : U}
    (hz : z ∈ Subalgebra.center ℂ U) {s : ℂ}
    (h₁ : z - algebraMap ℂ U s ∈ vermaIdeal H X (lam + B.rho X)) :
    z - algebraMap ℂ U s ∈ vermaIdeal H X' (lam + B.rho X') := by
  obtain ⟨X'', hX'', hiff, hgen⟩ := B.exists_generic hC hX hX'
  have := B.sub_mem_of_isGeneric hC hX'' lam hz _ X hX hgen rfl h₁
  rwa [B.vermaIdeal_eq_of_iff hiff, B.rho_eq_of_iff hiff] at this

end WeightBasis

end Langlands.Algebra.HarishChandra
