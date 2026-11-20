import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.TraceFormula.TwistedOrbital
import Mathlib.GroupTheory.DoubleCoset

/-! The compact-open double coset expansion of twisted orbital integrals. -/

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open Langlands.QuotientIntegration

universe u v

namespace Langlands.QuotientIntegration

section DoubleCosets

variable {G : Type u} [Group G] [TopologicalSpace G]
variable (H : Subgroup G) (K : OpenSubgroup G)

/-- The part of the actual left quotient `H \ G` corresponding to a double coset. -/
def compactOpenDoubleCoset (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    Set (LeftQuotient H) :=
  leftQuotientMap H '' DoubleCoset.quotToDoubleCoset H K.toSubgroup d

@[simp] theorem leftQuotientMap_mem_compactOpenDoubleCoset (x : G)
    (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    leftQuotientMap H x ∈ compactOpenDoubleCoset H K d ↔
      DoubleCoset.mk H K.toSubgroup x = d := by
  constructor
  · rintro ⟨y, hy, hq⟩
    have hxy : x * y⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    have hmk : DoubleCoset.mk H K.toSubgroup y = DoubleCoset.mk H K.toSubgroup x :=
      DoubleCoset.eq.mpr ⟨x * y⁻¹, hxy, 1, K.one_mem, by simp⟩
    exact hmk.symm.trans ((DoubleCoset.mem_quotToDoubleCoset_iff d y).mp hy)
  · exact fun hx => ⟨x, (DoubleCoset.mem_quotToDoubleCoset_iff d x).mpr hx, rfl⟩

/-- The subset belonging to the double coset of `g` is the image of the left coset `gK`. -/
theorem compactOpenDoubleCoset_mk (g : G) :
    compactOpenDoubleCoset H K (DoubleCoset.mk H K.toSubgroup g) =
      (fun k : G => leftQuotientMap H (g * k)) '' (K : Set G) := by
  ext q
  induction q using Quotient.inductionOn with
  | h x =>
    change leftQuotientMap H x ∈ _ ↔ _
    rw [leftQuotientMap_mem_compactOpenDoubleCoset]
    constructor
    · intro hx
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.eq.mp hx.symm
      refine ⟨k, hk, ?_⟩
      change leftQuotientMap H (g * k) = leftQuotientMap H (h * g * k)
      rw [mul_assoc, leftQuotientMap_subgroup_mul H ⟨h, hh⟩]
    · rintro ⟨k, hk, hq⟩
      have hh : x * (g * k)⁻¹ ∈ H :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
      exact (DoubleCoset.eq.mpr ⟨x * (g * k)⁻¹, hh, k, hk, by group⟩).symm

theorem pairwiseDisjoint_compactOpenDoubleCoset :
    Pairwise (Disjoint on (compactOpenDoubleCoset H K)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    change leftQuotientMap H x ∈ _ → leftQuotientMap H x ∉ _
    simp only [leftQuotientMap_mem_compactOpenDoubleCoset]
    exact fun ha hb => hab (ha.symm.trans hb)

variable [IsTopologicalGroup G]

theorem isOpen_compactOpenDoubleCoset
    (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
    IsOpen (compactOpenDoubleCoset H K d) := by
  rw [← DoubleCoset.out_eq' d, compactOpenDoubleCoset_mk, ← image_image]
  exact (leftQuotient_isOpenQuotientMap H).isOpenMap _
    ((Homeomorph.mulLeft d.out).isOpenMap _ K.isOpen)

/-- There are at most countably many double cosets when `G` is separable and `K` open. -/
theorem countable_compactOpenDoubleCosets [SeparableSpace G] :
    Countable (DoubleCoset.Quotient (H : Set G) (K : Set G)) := by
  let : SeparableSpace (LeftQuotient H) :=
    (leftQuotient_isOpenQuotientMap H).isQuotientMap.separableSpace
  exact (pairwiseDisjoint_compactOpenDoubleCoset H K).countable_of_isOpen_disjoint
    (isOpen_compactOpenDoubleCoset H K) fun d =>
      ⟨leftQuotientMap H d.out,
        (leftQuotientMap_mem_compactOpenDoubleCoset H K d.out d).mpr (DoubleCoset.out_eq' d)⟩

end DoubleCosets

section Mass

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
variable (μG : Measure G) (μH : Measure H)
variable [IsHaarMeasure μG] [μG.Regular]
variable [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]

set_option linter.overlappingInstances false in
/-- The mass of a double coset in a compatible quotient is the ratio of the compact
open subgroup mass to the conjugate intersection mass in the stabilizer. -/
theorem IsCompatible.measure_compactOpenDoubleCoset (hH : IsClosed (H : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μG μH ν) (g : G) :
    ν (compactOpenDoubleCoset H K (DoubleCoset.mk H K.toSubgroup g)) =
      μG (K : Set G) / μH {h : H | g⁻¹ * (h : G) * g ∈ K} := by
  obtain ⟨_, _, hres⟩ := compactOpenOrbitMeasure H hH μG μH K hK ν hν g
  have hp : Continuous (fun k : G => leftQuotientMap H (g * k)) :=
    (leftQuotient_isOpenQuotientMap H).continuous.comp (continuous_const.mul continuous_id)
  have huniv := congrArg (fun m : Measure (LeftQuotient H) => m Set.univ) hres
  rw [Measure.restrict_apply_univ, Measure.smul_apply,
    Measure.map_apply hp.measurable MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, smul_eq_mul] at huniv
  rw [compactOpenDoubleCoset_mk, huniv, ENNReal.div_eq_inv_mul]

end Mass

end Langlands.QuotientIntegration

namespace Langlands.TraceFormula

section Sum

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {F : Type v} [FunLike F G G] [MonoidHomClass F G G]
variable (θ : F) (δ : G) (K : OpenSubgroup G)

private theorem twistedConj_mem_iff_of_doubleCoset_eq
    (hθ : ∀ k ∈ K, θ k ∈ K) {x y : G}
    (hxy : DoubleCoset.mk (twistedCentralizer θ δ) K.toSubgroup x =
      DoubleCoset.mk (twistedCentralizer θ δ) K.toSubgroup y) :
    twistedConj θ y δ ∈ K ↔ twistedConj θ x δ ∈ K := by
  obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.eq.mp hxy
  rw [mul_assoc, ← twistedConj_mul, twistedConj_apply θ h δ, hh, ← twistedConj_mul]
  change k⁻¹ * twistedConj θ x δ * θ k ∈ K.toSubgroup ↔
    twistedConj θ x δ ∈ K.toSubgroup
  exact (K.toSubgroup.mul_mem_cancel_right (hθ k hk)).trans
    (K.toSubgroup.mul_mem_cancel_left (K.inv_mem hk))

/-- Double cosets contributing to the compact-open twisted orbital integral. -/
def compactOpenTwistedDoubleCosets :=
  {d : DoubleCoset.Quotient (twistedCentralizer θ δ : Set G) (K : Set G) //
    twistedConj θ d.out δ ∈ K}

theorem compactOpenTwistedDoubleCosets_mk_iff (hθ : ∀ k ∈ K, θ k ∈ K) (x : G) :
    twistedConj θ (DoubleCoset.mk (twistedCentralizer θ δ) K.toSubgroup x).out δ ∈ K ↔
      twistedConj θ x δ ∈ K :=
  twistedConj_mem_iff_of_doubleCoset_eq θ δ K hθ (DoubleCoset.out_eq' _).symm

variable [IsTopologicalGroup G] [SeparableSpace G]
variable [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
variable [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]

/-- The compact-open indicator orbital integral is the conversion to `ℂ` of the
sum of the extended nonnegative masses of the contributing double cosets.
The conversion uses `toReal`, so it also agrees with the total Bochner integral
when the support has infinite mass. -/
theorem twistedOrbitalIntegral_compactOpen (hθ : ∀ k ∈ K, θ k ∈ K)
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) :
    twistedOrbitalIntegral θ δ ν ((K : Set G).indicator (fun _ => (1 : ℂ))) =
      ((∑' d : compactOpenTwistedDoubleCosets θ δ K,
        ν (compactOpenDoubleCoset (twistedCentralizer θ δ) K d.val)).toReal : ℂ) := by
  classical
  let H := twistedCentralizer θ δ
  let A := compactOpenTwistedDoubleCosets θ δ K
  let C (d : A) := compactOpenDoubleCoset H K d.val
  let : Countable (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
    countable_compactOpenDoubleCosets H K
  let : Countable A := by
    dsimp [A, compactOpenTwistedDoubleCosets]
    infer_instance
  have hC (d : A) : MeasurableSet (C d) := (isOpen_compactOpenDoubleCoset H K d.val).measurableSet
  have hd : Pairwise (Disjoint on C) := fun _ _ h =>
    pairwiseDisjoint_compactOpenDoubleCoset H K (Subtype.val_injective.ne h)
  have hind : twistedOrbitFunction θ δ ((K : Set G).indicator (fun _ => (1 : ℂ))) =
      (⋃ d : A, C d).indicator (fun _ => (1 : ℂ)) := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      simp only [twistedOrbitFunction_mk, Set.indicator_apply]
      have hmem : Quotient.mk _ x ∈ ⋃ d : A, C d ↔ twistedConj θ x δ ∈ K := by
        change leftQuotientMap H x ∈ _ ↔ _
        simp only [mem_iUnion, C, leftQuotientMap_mem_compactOpenDoubleCoset]
        constructor
        · rintro ⟨d, hd⟩
          exact (twistedConj_mem_iff_of_doubleCoset_eq θ δ K hθ
            (hd.trans (DoubleCoset.out_eq' d.val).symm)).mp d.property
        · intro hx
          exact ⟨⟨DoubleCoset.mk H K.toSubgroup x,
            (compactOpenTwistedDoubleCosets_mk_iff θ δ K hθ x).mpr hx⟩, rfl⟩
      change (if twistedConj θ x δ ∈ K then (1 : ℂ) else 0) =
        (if Quotient.mk _ x ∈ ⋃ d : A, C d then 1 else 0)
      rw [hmem]
  rw [twistedOrbitalIntegral, hind, integral_indicator_const _ (MeasurableSet.iUnion hC),
    measureReal_def, measure_iUnion hd hC, Complex.real_smul, mul_one]

end Sum

end Langlands.TraceFormula
