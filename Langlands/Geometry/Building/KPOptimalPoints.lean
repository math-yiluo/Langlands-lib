import Langlands.Geometry.Building.AffineChamberReflections
import Langlands.Geometry.Building.AffineChamberSeparation
import Langlands.Geometry.Building.RankZeroAffineRootSystem
import Langlands.Geometry.Building.ValuationAffineRootSystems

/-!
# Optimal points (Kaletha–Prasad §13.4)

For a set `Ψ` of affine functionals on a real affine space `A` and a point `c` of `A`, with
`C = facet Ψ c` (a chamber when `c` is regular):

* `rationalRootPeriods Ψ`: the positive rational numbers `t` with `ψ + t ∈ Ψ` for every
  `ψ ∈ Ψ`, and `rootPeriod Ψ`, their infimum. KP's `ℓ` ("the smallest positive rational number
  such that for any affine root `ψ`, `ψ + ℓ` is also an affine root") is `rootPeriod Ψ` when
  the least element exists (`rootPeriod_eq_of_isLeast`). It exists for a nonempty affine root
  system with a positive rational period (`exists_isLeast_rationalRootPeriods`) and for the
  nonempty actual affine roots of supplied valuation building data, where `2` is a period
  (`ValuationBuildingData.isLeast_rootPeriod_affineRoots`).
* `positiveRootsBelowPeriod Ψ c`: KP's `Σ`, the affine roots `ψ` with `ψ > 0` and `ψ - ℓ < 0`
  on `C`. It is finite for an affine root system, and nonempty when moreover `Ψ` is nonempty,
  `c` is regular and `ℓ` is a period.
* `IsRationalPoint Ψ x` and `IsRationalAffineFunctional Ψ c f` (KP Definition 13.4.1).
* `IsOptimalPointFor Ψ c S x` (KP Definition 13.4.2, first sentence) for a finite set `S`,
  `IsOptimalPoint Ψ x` (optimal for some chamber of `A`), and
  `ValuationBuildingData.IsOptimalPoint y` for a point of the building (second sentence).

The existence of optimal points (the linear-programming argument after Definition 13.4.2) and
Lemma 13.4.4 are not formalized. If `Ψ` is empty there is no optimal point
(`not_isOptimalPoint_of_eq_empty`).
-/

noncomputable section

universe u

namespace Langlands.Geometry.Building

namespace AffineRootSystem

open GalleryGeometry

variable {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-! ### The translation period `ℓ` -/

/-- The positive rational numbers `t` such that `ψ + t` is an affine root for every affine
root `ψ`. -/
def rationalRootPeriods (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Set ℝ :=
  {t | 0 < t ∧ t ∈ Set.range ((↑) : ℚ → ℝ) ∧ ∀ ψ ∈ Ψ, ψ + AffineMap.const ℝ A t ∈ Ψ}

/-- KP's `ℓ` in §13.4: the infimum of the positive rational periods of `Ψ`. It is the least
positive rational period when one exists (`rootPeriod_eq_of_isLeast`). -/
def rootPeriod (Ψ : Set (A →ᵃ[ℝ] ℝ)) : ℝ :=
  sInf (rationalRootPeriods Ψ)

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)}

theorem rootPeriod_eq_of_isLeast {ℓ : ℝ} (h : IsLeast (rationalRootPeriods Ψ) ℓ) :
    rootPeriod Ψ = ℓ :=
  h.csInf_eq

/-- If every derivative fibre of `Ψ` is finite in bounded distance, `Ψ` is nonempty and some
positive rational period exists, then there is a least positive rational period. -/
theorem exists_isLeast_rationalRootPeriods
    (hfin : ∀ ψ ∈ Ψ, ∀ M : ℝ,
      {η | η ∈ Ψ ∧ η.linear = ψ.linear ∧ ∀ x : A, |η x - ψ x| ≤ M}.Finite)
    (hne : Ψ.Nonempty) {t : ℝ} (ht : t ∈ rationalRootPeriods Ψ) :
    ∃ ℓ, IsLeast (rationalRootPeriods Ψ) ℓ := by
  obtain ⟨ψ, hψ⟩ := hne
  set T := rationalRootPeriods Ψ ∩ Set.Iic t with hTdef
  have hinj : Set.InjOn (fun s : ℝ => ψ + AffineMap.const ℝ A s) T := by
    intro s _ s' _ h
    obtain ⟨x⟩ : Nonempty A := inferInstance
    have hx := congrArg (fun g : A →ᵃ[ℝ] ℝ => g x) h
    simpa using hx
  have hmaps : Set.MapsTo (fun s : ℝ => ψ + AffineMap.const ℝ A s) T
      {η | η ∈ Ψ ∧ η.linear = ψ.linear ∧ ∀ x : A, |η x - ψ x| ≤ t} := by
    rintro s ⟨⟨hs0, -, hsΨ⟩, hst⟩
    refine ⟨hsΨ ψ hψ, by simp, fun x => ?_⟩
    simp only [AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply, Function.const_apply,
      add_sub_cancel_left]
    rw [abs_of_pos hs0]
    exact hst
  have hT : T.Finite :=
    Set.Finite.of_finite_image ((hfin ψ hψ t).subset hmaps.image_subset) hinj
  obtain ⟨ℓ, hℓT, hmin⟩ := Set.exists_min_image T id hT ⟨t, ht, Set.mem_Iic.2 le_rfl⟩
  refine ⟨ℓ, hℓT.1, fun s hs => ?_⟩
  rcases le_or_gt s t with hst | hst
  · exact hmin s ⟨hs, hst⟩
  · exact (hℓT.2 : ℓ ≤ t).trans hst.le

theorem IsAffineRootSystemWithRankZero.exists_isLeast_rationalRootPeriods
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (hne : Ψ.Nonempty) {t : ℝ}
    (ht : t ∈ rationalRootPeriods Ψ) : ∃ ℓ, IsLeast (rationalRootPeriods Ψ) ℓ :=
  AffineRootSystem.exists_isLeast_rationalRootPeriods hΨ.finite_bounded hne ht

theorem IsAffineRootSystemWithRankZero.isLeast_rootPeriod
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (hne : Ψ.Nonempty) {t : ℝ}
    (ht : t ∈ rationalRootPeriods Ψ) : IsLeast (rationalRootPeriods Ψ) (rootPeriod Ψ) := by
  obtain ⟨ℓ, hℓ⟩ := hΨ.exists_isLeast_rationalRootPeriods hne ht
  rwa [rootPeriod_eq_of_isLeast hℓ]

/-! ### The set `Σ` -/

/-- The roots `ψ` with `ψ > 0` and `ψ - rootPeriod Ψ < 0` on `facet Ψ c`. This gives KP's
`Σ` in §13.4 when `c` represents a chamber and the least positive rational period exists. -/
def positiveRootsBelowPeriod (Ψ : Set (A →ᵃ[ℝ] ℝ)) (c : A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ positiveRoots Ψ (facet Ψ c) ∧ ∀ y ∈ facet Ψ c, ψ y - rootPeriod Ψ < 0}

theorem positiveRootsBelowPeriod_subset (c : A) : positiveRootsBelowPeriod Ψ c ⊆ Ψ :=
  fun _ hψ => hψ.1.1

theorem mem_positiveRootsBelowPeriod_apply {c : A} {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ positiveRootsBelowPeriod Ψ c) : 0 < ψ c ∧ ψ c < rootPeriod Ψ := by
  have hc : c ∈ facet Ψ c := (facetRel_equivalence Ψ).refl c
  exact ⟨hψ.1.2 c hc, sub_neg.1 (hψ.2 c hc)⟩

/-- `Σ` is finite (KP: "the finite set `Σ`"). -/
theorem IsAffineRootSystemWithRankZero.finite_positiveRootsBelowPeriod
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (c : A) :
    (positiveRootsBelowPeriod Ψ c).Finite := by
  refine (hΨ.finite_bounded_at c (fun _ => rootPeriod Ψ)).subset ?_
  intro ψ hψ
  obtain ⟨h0, hℓ⟩ := mem_positiveRootsBelowPeriod_apply hψ
  exact ⟨hψ.1.1, by rw [abs_of_pos h0]; exact hℓ.le⟩

/-- In an affine root system, a period `ℓ` gives `ψ + kℓ ∈ Ψ` for every integer `k`. -/
theorem IsAffineRootSystemWithRankZero.add_intCast_mul_mem
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {ℓ : ℝ}
    (hℓ : ∀ ψ ∈ Ψ, ψ + AffineMap.const ℝ A ℓ ∈ Ψ) {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) (k : ℤ) :
    ψ + AffineMap.const ℝ A ((k : ℝ) * ℓ) ∈ Ψ := by
  have hsub : ∀ η ∈ Ψ, η - AffineMap.const ℝ A ℓ ∈ Ψ := fun η hη => by
    have h := hΨ.neg_mem (hℓ _ (hΨ.neg_mem hη))
    have he : -(-η + AffineMap.const ℝ A ℓ) = η - AffineMap.const ℝ A ℓ := by abel
    rwa [he] at h
  induction k using Int.induction_on with
  | zero =>
    have he : ψ + AffineMap.const ℝ A (((0 : ℤ) : ℝ) * ℓ) = ψ := by
      ext x
      simp
    rw [he]
    exact hψ
  | succ k ih =>
    have he : ψ + AffineMap.const ℝ A (((k + 1 : ℤ) : ℝ) * ℓ) =
        (ψ + AffineMap.const ℝ A ((k : ℝ) * ℓ)) + AffineMap.const ℝ A ℓ := by
      ext x
      simp only [AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply, Function.const_apply]
      push_cast
      ring
    rw [he]
    exact hℓ _ ih
  | pred k ih =>
    have he : ψ + AffineMap.const ℝ A (((-(k : ℤ) - 1 : ℤ) : ℝ) * ℓ) =
        (ψ + AffineMap.const ℝ A (((-(k : ℤ) : ℤ) : ℝ) * ℓ)) - AffineMap.const ℝ A ℓ := by
      ext x
      simp only [AffineMap.coe_add, AffineMap.coe_sub, AffineMap.coe_const, Pi.add_apply,
        Pi.sub_apply, Function.const_apply]
      push_cast
      ring
    rw [he]
    exact hsub _ ih

/-- For a nonempty affine root system, a regular point `c` and `ℓ` a period, `Σ` is nonempty:
translating a root positive at `c` by a multiple of `ℓ` lands in `Σ`. -/
theorem IsAffineRootSystemWithRankZero.positiveRootsBelowPeriod_nonempty
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {c : A} (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (hℓ : rootPeriod Ψ ∈ rationalRootPeriods Ψ) :
    (positiveRootsBelowPeriod Ψ c).Nonempty := by
  set ℓ := rootPeriod Ψ with hℓdef
  obtain ⟨hℓ0, -, hadd⟩ := hℓ
  have hC : IsChamber Ψ (facet Ψ c) := ⟨c, hc, rfl⟩
  have hcC : c ∈ facet Ψ c := (facetRel_equivalence Ψ).refl c
  -- a root positive at `c`
  obtain ⟨η, hη, hηc⟩ : ∃ η ∈ Ψ, 0 < η c := by
    obtain ⟨ψ, hψ⟩ := hne
    rcases lt_or_gt_of_ne (hc ψ hψ) with h | h
    · exact ⟨-ψ, hΨ.neg_mem hψ, by simpa using h⟩
    · exact ⟨ψ, hψ, h⟩
  set k : ℤ := ⌈η c / ℓ⌉ - 1 with hkdef
  have hk1 : (k : ℝ) < η c / ℓ := by
    have := Int.ceil_lt_add_one (η c / ℓ)
    rw [hkdef]
    push_cast
    linarith
  have hk2 : η c / ℓ ≤ (k : ℝ) + 1 := by
    rw [hkdef]
    push_cast
    linarith [Int.le_ceil (η c / ℓ)]
  have hk1' : (k : ℝ) * ℓ < η c := (lt_div_iff₀ hℓ0).1 hk1
  have hk2' : η c ≤ ((k : ℝ) + 1) * ℓ := (div_le_iff₀ hℓ0).1 hk2
  set θ := η + AffineMap.const ℝ A (((-k : ℤ) : ℝ) * ℓ) with hθdef
  have hθ : θ ∈ Ψ := hΨ.add_intCast_mul_mem hadd hη (-k)
  have hθc : θ c = η c - (k : ℝ) * ℓ := by
    simp only [hθdef, AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply,
      Function.const_apply]
    push_cast
    ring
  have hθ' : θ + AffineMap.const ℝ A (((-1 : ℤ) : ℝ) * ℓ) ∈ Ψ :=
    hΨ.add_intCast_mul_mem hadd hθ (-1)
  have hθ'c : (θ + AffineMap.const ℝ A (((-1 : ℤ) : ℝ) * ℓ)) c = θ c - ℓ := by
    simp only [AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply, Function.const_apply]
    push_cast
    ring
  have hθpos : 0 < θ c := by rw [hθc]; linarith
  have hθlt : θ c < ℓ := by
    rcases lt_or_eq_of_le (show θ c ≤ ℓ by rw [hθc]; linarith) with h | h
    · exact h
    · exact absurd (by rw [hθ'c, h, sub_self]) (hc _ hθ')
  refine ⟨θ, ?_, fun y hy => ?_⟩
  · rcases hC.mem_positiveRoots_or_mem_negativeRoots hθ with h | h
    · exact h
    · exact absurd (h.2 c hcC) (not_lt.2 hθpos.le)
  · rcases hC.mem_positiveRoots_or_mem_negativeRoots hθ' with h | h
    · exact absurd (h.2 c hcC) (by rw [hθ'c]; linarith)
    · have := h.2 y hy
      simp only [AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply,
        Function.const_apply] at this
      push_cast at this
      linarith

/-! ### Rationality (KP Definition 13.4.1) -/

/-- A point `x` is rational if every affine root takes a rational value at `x`
(KP Definition 13.4.1). -/
def IsRationalPoint (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Prop :=
  ∀ ψ ∈ Ψ, ψ x ∈ Set.range ((↑) : ℚ → ℝ)

/-- The roots positive on `C` that are not sums of two roots positive on `C`.
These are the generators used in KP §13.4, not the wall-root set of Definition 1.3.19. -/
def indecomposablePositiveRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ positiveRoots Ψ C ∧
    ¬ ∃ φ ∈ positiveRoots Ψ C, ∃ η ∈ positiveRoots Ψ C, ψ = φ + η}

/-- An affine functional is rational (KP Definition 13.4.1) if `c` represents a chamber and
it is a finite rational linear combination of the positive indecomposable roots of that
chamber `facet Ψ c`. -/
def IsRationalAffineFunctional (Ψ : Set (A →ᵃ[ℝ] ℝ)) (c : A) (f : A →ᵃ[ℝ] ℝ) : Prop :=
  IsRegular Ψ c ∧
    ∃ (s : Finset (A →ᵃ[ℝ] ℝ)) (q : (A →ᵃ[ℝ] ℝ) → ℚ),
      (↑s : Set (A →ᵃ[ℝ] ℝ)) ⊆ indecomposablePositiveRoots Ψ (facet Ψ c) ∧
        f = ∑ ψ ∈ s, (q ψ : ℝ) • ψ

/-- A rational affine functional takes a rational value at a rational point. -/
theorem IsRationalAffineFunctional.apply_mem_range {c x : A} {f : A →ᵃ[ℝ] ℝ}
    (hf : IsRationalAffineFunctional Ψ c f) (hx : IsRationalPoint Ψ x) :
    f x ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨-, s, q, hs, rfl⟩ := hf
  let ev : (A →ᵃ[ℝ] ℝ) →+ ℝ :=
    { toFun := fun g => g x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hev : (∑ ψ ∈ s, (q ψ : ℝ) • ψ) x = ∑ ψ ∈ s, (q ψ : ℝ) * ψ x := by
    change ev (∑ ψ ∈ s, (q ψ : ℝ) • ψ) = _
    rw [map_sum]
    rfl
  rw [hev]
  have hR : ∀ y : ℝ, y ∈ Set.range ((↑) : ℚ → ℝ) ↔ y ∈ (Rat.castHom ℝ).range := by
    intro y
    simp [RingHom.mem_range]
  rw [hR]
  refine Subring.sum_mem _ fun ψ hψ => Subring.mul_mem _ ⟨q ψ, by simp⟩ ?_
  rw [← hR]
  exact hx ψ (hs hψ).1.1

/-! ### Optimal points (KP Definition 13.4.2) -/

/-- `x` is an optimal point for the finite set `S` of affine roots and the chamber
`C = facet Ψ c` (KP Definition 13.4.2): `c` is regular, `S` is a nonempty subset of `Σ`,
`x` lies in the closure of `C`, `min_{ψ ∈ S} ψ(x) ≥ min_{ψ ∈ S} ψ(y)` for every `y` in the
closure, and `x` is a rational point. -/
def IsOptimalPointFor (Ψ : Set (A →ᵃ[ℝ] ℝ)) (c : A) (S : Finset (A →ᵃ[ℝ] ℝ)) (x : A) :
    Prop :=
  IsRegular Ψ c ∧
    ∃ hS : S.Nonempty, (↑S : Set (A →ᵃ[ℝ] ℝ)) ⊆ positiveRootsBelowPeriod Ψ c ∧
      x ∈ facetClosure Ψ c ∧
      (∀ y ∈ facetClosure Ψ c, S.inf' hS (fun ψ => ψ y) ≤ S.inf' hS (fun ψ => ψ x)) ∧
      IsRationalPoint Ψ x

/-- `x` is an optimal point of the apartment `A`: it is optimal for some nonempty finite subset
of `Σ` of some chamber of `A` (KP Definition 13.4.2, second sentence, within one apartment). -/
def IsOptimalPoint (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Prop :=
  ∃ (c : A) (S : Finset (A →ᵃ[ℝ] ℝ)), IsOptimalPointFor Ψ c S x

/-- The minimum condition without `Finset.inf'`. -/
theorem isOptimalPointFor_iff {c x : A} {S : Finset (A →ᵃ[ℝ] ℝ)} :
    IsOptimalPointFor Ψ c S x ↔
      IsRegular Ψ c ∧ S.Nonempty ∧ (↑S : Set (A →ᵃ[ℝ] ℝ)) ⊆ positiveRootsBelowPeriod Ψ c ∧
        x ∈ facetClosure Ψ c ∧
        (∀ y ∈ facetClosure Ψ c, ∃ φ ∈ S, ∀ ψ ∈ S, φ y ≤ ψ x) ∧ IsRationalPoint Ψ x := by
  constructor
  · rintro ⟨hc, hS, hsub, hx, hmin, hrat⟩
    refine ⟨hc, hS, hsub, hx, fun y hy => ?_, hrat⟩
    obtain ⟨φ, hφ, he⟩ := S.exists_mem_eq_inf' hS (fun ψ => ψ y)
    refine ⟨φ, hφ, fun ψ hψ => ?_⟩
    rw [← he]
    exact (hmin y hy).trans (S.inf'_le _ hψ)
  · rintro ⟨hc, hS, hsub, hx, hmin, hrat⟩
    refine ⟨hc, hS, hsub, hx, fun y hy => ?_, hrat⟩
    obtain ⟨φ, hφ, hle⟩ := hmin y hy
    exact (S.inf'_le _ hφ).trans ((S.le_inf'_iff hS _).2 hle)

theorem IsOptimalPointFor.isRegular {c x : A} {S : Finset (A →ᵃ[ℝ] ℝ)}
    (h : IsOptimalPointFor Ψ c S x) : IsRegular Ψ c :=
  h.1

theorem IsOptimalPointFor.mem_facetClosure {c x : A} {S : Finset (A →ᵃ[ℝ] ℝ)}
    (h : IsOptimalPointFor Ψ c S x) : x ∈ facetClosure Ψ c :=
  h.2.2.2.1

theorem IsOptimalPointFor.isRationalPoint {c x : A} {S : Finset (A →ᵃ[ℝ] ℝ)}
    (h : IsOptimalPointFor Ψ c S x) : IsRationalPoint Ψ x :=
  h.2.2.2.2.2

theorem IsOptimalPointFor.subset {c x : A} {S : Finset (A →ᵃ[ℝ] ℝ)}
    (h : IsOptimalPointFor Ψ c S x) : (↑S : Set (A →ᵃ[ℝ] ℝ)) ⊆ positiveRootsBelowPeriod Ψ c :=
  h.2.2.1

/-- For a single root of `Σ`, optimality means that the representative `c` is regular and `x`
is rational and maximizes the root over the closed chamber. -/
theorem isOptimalPointFor_singleton_iff {c x : A} {ψ : A →ᵃ[ℝ] ℝ} :
    IsOptimalPointFor Ψ c {ψ} x ↔
      IsRegular Ψ c ∧ ψ ∈ positiveRootsBelowPeriod Ψ c ∧ x ∈ facetClosure Ψ c ∧
        (∀ y ∈ facetClosure Ψ c, ψ y ≤ ψ x) ∧ IsRationalPoint Ψ x := by
  rw [isOptimalPointFor_iff]
  simp

/-- With no affine roots there are no optimal points: `Σ` is empty and `S` must be a nonempty
subset of it. -/
theorem not_isOptimalPointFor_of_eq_empty (hΨ : Ψ = ∅) (c x : A) (S : Finset (A →ᵃ[ℝ] ℝ)) :
    ¬ IsOptimalPointFor Ψ c S x := by
  rintro ⟨-, ⟨ψ, hψ⟩, hsub, -⟩
  have := positiveRootsBelowPeriod_subset c (hsub hψ)
  rw [hΨ] at this
  exact this

theorem not_isOptimalPoint_of_eq_empty (hΨ : Ψ = ∅) (x : A) : ¬ IsOptimalPoint Ψ x := by
  rintro ⟨c, S, h⟩
  exact not_isOptimalPointFor_of_eq_empty hΨ c x S h

end AffineRootSystem

end Langlands.Geometry.Building

/-! ### Actual affine roots and points of the building -/

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Adding the constant `2` preserves the actual affine roots. -/
theorem add_two_mem_affineRoots {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    ψ + AffineMap.const ℝ B.Apartment 2 ∈ B.affineRoots := by
  obtain ⟨a, ha, -⟩ := id hψ
  obtain ⟨n, hn⟩ := B.exists_conjugateAffineFunctional_eq_add_two a
  rw [← hn ψ ha]
  exact B.apartment.conjugateAffineFunctional_mem_affineRoots n hψ

theorem two_mem_rationalRootPeriods_affineRoots :
    (2 : ℝ) ∈ AffineRootSystem.rationalRootPeriods B.affineRoots :=
  ⟨two_pos, ⟨2, by norm_num⟩, fun _ hψ => B.add_two_mem_affineRoots hψ⟩

/-- For nonempty actual affine roots, `ℓ = rootPeriod B.affineRoots` is the least positive
rational period. -/
theorem isLeast_rootPeriod_affineRoots (hne : B.affineRoots.Nonempty) :
    IsLeast (AffineRootSystem.rationalRootPeriods B.affineRoots)
      (AffineRootSystem.rootPeriod B.affineRoots) :=
  B.isAffineRootSystemWithRankZero_affineRoots.isLeast_rootPeriod hne
    B.two_mem_rationalRootPeriods_affineRoots

theorem rootPeriod_affineRoots_pos (hne : B.affineRoots.Nonempty) :
    0 < AffineRootSystem.rootPeriod B.affineRoots :=
  (B.isLeast_rootPeriod_affineRoots hne).1.1

theorem rootPeriod_affineRoots_le_two (hne : B.affineRoots.Nonempty) :
    AffineRootSystem.rootPeriod B.affineRoots ≤ 2 :=
  (B.isLeast_rootPeriod_affineRoots hne).2 B.two_mem_rationalRootPeriods_affineRoots

/-- For nonempty actual affine roots, `Σ` of every chamber is finite and nonempty. -/
theorem positiveRootsBelowPeriod_affineRoots_finite_nonempty (hne : B.affineRoots.Nonempty)
    {c : B.Apartment} (hc : AffineRootSystem.GalleryGeometry.IsRegular B.affineRoots c) :
    (AffineRootSystem.positiveRootsBelowPeriod B.affineRoots c).Finite ∧
      (AffineRootSystem.positiveRootsBelowPeriod B.affineRoots c).Nonempty :=
  ⟨B.isAffineRootSystemWithRankZero_affineRoots.finite_positiveRootsBelowPeriod c,
    B.isAffineRootSystemWithRankZero_affineRoots.positiveRootsBelowPeriod_nonempty hc hne
      (B.isLeast_rootPeriod_affineRoots hne).1⟩

/-- An optimal point of `B(G)` (KP Definition 13.4.2): a `G(F)`-translate of the image of an
optimal point of the apartment, that is, a point that is optimal in some apartment
`g · A(S)` for some chamber and some nonempty finite subset of its `Σ`. -/
def IsOptimalPoint (y : B.ReducedBuilding) : Prop :=
  ∃ (g : rationalPoints G) (x : B.Apartment),
    g • B.apartmentMap x = y ∧ AffineRootSystem.IsOptimalPoint B.affineRoots x

theorem isOptimalPoint_apartmentMap {x : B.Apartment}
    (h : AffineRootSystem.IsOptimalPoint B.affineRoots x) : B.IsOptimalPoint (B.apartmentMap x) :=
  ⟨1, x, one_smul _ _, h⟩

theorem IsOptimalPoint.smul {y : B.ReducedBuilding} (hy : B.IsOptimalPoint y)
    (g : rationalPoints G) : B.IsOptimalPoint (g • y) := by
  obtain ⟨h, x, rfl, hx⟩ := hy
  exact ⟨g * h, x, mul_smul g h _, hx⟩

/-- If there are no actual affine roots, `B(G)` has no optimal point: Definition 13.4.2 needs
a nonempty subset of `Σ`. -/
theorem not_isOptimalPoint_of_affineRoots_eq_empty (hΨ : B.affineRoots = ∅)
    (y : B.ReducedBuilding) : ¬ B.IsOptimalPoint y := by
  rintro ⟨-, x, -, hx⟩
  exact AffineRootSystem.not_isOptimalPoint_of_eq_empty hΨ x hx

end Langlands.Geometry.Building.ValuationBuildingData
