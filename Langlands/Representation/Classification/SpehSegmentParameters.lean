import Langlands.Representation.Classification.TadicSpehHeads
import Langlands.Representation.Classification.HeadTargetTransport

/-! # Segment parameters of Speh representations

The multisegment formed by centered real twists of a single segment, its
half-twist recurrence, and its relation to the actual centered Speh induction.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The `k` centered twists of `Δ`, listed with decreasing real exponents.
If `δ` is the special head of `Δ`, this is the Langlands parameter of `u(δ,k)`. -/
def spehSegmentMultisegment (Δ : T.Segment.{uV,uF}) (k : ℕ) :
    T.Multisegment.{uV,uF} :=
  (List.ofFn (fun i : Fin k => Δ.twist (((k : ℝ) - 1) / 2 - (i : ℕ))) :
    Multiset (T.Segment.{uV,uF}))

theorem spehSegmentMultisegment_degree (Δ : T.Segment.{uV,uF}) (k : ℕ) :
    (spehSegmentMultisegment Δ k).degree = k * Δ.degree := by
  simp [spehSegmentMultisegment, Multisegment.degree, List.map_ofFn, List.sum_ofFn,
    Segment.twist, Segment.degree, Segment.rank, CuspidalDatum.twist]

/-- Adding the largest centered exponent gives the negative half-twist recurrence. -/
theorem spehSegmentMultisegment_succ (Δ : T.Segment.{uV,uF}) (k : ℕ) :
    spehSegmentMultisegment Δ (k + 1) =
      {Δ.twist ((k : ℝ) / 2)} + (spehSegmentMultisegment Δ k).twist (-(1 / 2)) := by
  unfold spehSegmentMultisegment Multisegment.twist
  rw [List.ofFn_succ]
  simp only [Multiset.map_coe, List.map_ofFn, Multiset.singleton_add,
    ← Multiset.cons_coe]
  apply congrArg₂ Multiset.cons
  · apply congrArg (fun t : ℝ => Δ.twist t)
    simp only [Fin.val_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    ring
  · apply congrArg (fun f : Fin k → T.Segment.{uV,uF} =>
      (List.ofFn f : Multiset (T.Segment.{uV,uF})))
    funext i
    dsimp only [Function.comp_apply]
    rw [Segment.twist_twist]
    apply congrArg (fun t : ℝ => Δ.twist t)
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- The positive half-twist recurrence leaves the centered parameter of length `k`. -/
theorem spehSegmentMultisegment_twist_succ (Δ : T.Segment.{uV,uF}) (k : ℕ) :
    (spehSegmentMultisegment Δ (k + 1)).twist (1 / 2) =
      {Δ.twist (((k : ℝ) + 1) / 2)} + spehSegmentMultisegment Δ k := by
  rw [spehSegmentMultisegment_succ]
  unfold Multisegment.twist
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
    Function.comp_def, Segment.twist_twist]
  have hzero : (1 / 2 : ℝ) + -(1 / 2) = 0 := by ring
  simp only [hzero, Segment.twist_zero, Multiset.map_id']
  rw [show (1 / 2 : ℝ) + (k : ℝ) / 2 = ((k : ℝ) + 1) / 2 by ring]

/-- Opposite half-twists have the same multiset sum as the two neighbor lengths. -/
theorem spehSegmentMultisegment_endpoint (Δ : T.Segment.{uV,uF}) (k : ℕ)
    (hk : 1 ≤ k) :
    (spehSegmentMultisegment Δ k).twist (1 / 2) +
        (spehSegmentMultisegment Δ k).twist (-(1 / 2)) =
      spehSegmentMultisegment Δ (k + 1) + spehSegmentMultisegment Δ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 1 + j = j + 1 by omega,
    show j + 1 - 1 = j by omega,
    spehSegmentMultisegment_twist_succ, spehSegmentMultisegment_succ Δ (j + 1)]
  simp only [Nat.cast_add, Nat.cast_one]
  ac_rfl

namespace SpehDatum

variable (d : SpehDatum.{uF,uV} F T) (Δ : T.Segment.{max uF uV,uF})

/-- The actual segment product inducing the centered Speh module when `δ` is
the head of `Δ`; the rank equality retains the original `δ` as every block. -/
def segmentProductDatum (hΔ : Δ.degree = d.rank) :
    T.SegmentProductDatum.{max uF uV,uF} d.degree where
  length := d.length
  segments i := Δ.twist (d.exponent i)
  degree_sum := by
    change ∑ _i : Fin d.length, Δ.degree = d.length * d.rank
    simp [hΔ]
  blocks i := hΔ.symm ▸ T.segmentFactor d.delta (d.exponent i)

theorem segmentProductDatum_multisegment (hΔ : Δ.degree = d.rank) :
    (d.segmentProductDatum Δ hΔ).multisegment = spehSegmentMultisegment Δ d.length := rfl

theorem segmentProductDatum_induced (hΔ : Δ.degree = d.rank) :
    (d.segmentProductDatum Δ hΔ).induced = d.centeredInduced := by
  rcases d with ⟨r, hr, k, hk, δ⟩
  dsimp at hΔ
  cases hΔ
  rfl

theorem segmentProductDatum_isPrecedenceOrdered (hΔ : Δ.degree = d.rank) :
    (d.segmentProductDatum Δ hΔ).IsPrecedenceOrdered := by
  intro i j hij hprec
  obtain ⟨-, k, hk, hkeq⟩ := hprec
  change (Δ.twist (d.exponent j)).base =
    (Δ.twist (d.exponent i)).base.twist (k : ℝ) at hkeq
  simp only [Segment.twist, CuspidalDatum.twist_twist] at hkeq
  have hx := cuspidalDatum_twist_injective Δ.base hkeq
  have hij' := d.exponent_strictAnti hij
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  linarith

theorem segmentProductDatum_hasSegmentHeads (hΔ : Δ.degree = d.rank)
    (hδ : T.IsSegmentHead Δ (hΔ.symm ▸ d.delta)) :
    (d.segmentProductDatum Δ hΔ).HasSegmentHeads := by
  rcases d with ⟨r, hr, k, hk, δ⟩
  dsimp at hΔ
  cases hΔ
  intro i
  exact ((segmentConstituentRealTwistCompatibility.{uF,max uF uV} F T
    Δ _ δ).2.1).mp hδ

/-- Every supplied actual Speh representation has the centered multisegment
parameter of any segment whose special head is its discrete-series block. -/
theorem IsSpeh.isLanglandsHead (hΔ : Δ.degree = d.rank)
    (hδ : T.IsSegmentHead Δ (hΔ.symm ▸ d.delta))
    {S : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier)}
    (hS : d.IsSpeh S) :
    (spehSegmentMultisegment Δ d.length).IsLanglandsHead S := by
  let := T.topology
  obtain ⟨P, hP⟩ := glRegularLanglandsHeadExistence.{uF,uV} p F T d.degree d.degree_pos
    (d.temperedLanglandsDatum hS.1)
  obtain ⟨e⟩ := hS.2.2 P hP.isLanglandsQuotient
  refine ⟨d.segmentProductDatum Δ hΔ, d.segmentProductDatum_multisegment Δ hΔ,
    d.segmentProductDatum_isPrecedenceOrdered Δ hΔ,
    d.segmentProductDatum_hasSegmentHeads Δ hΔ hδ, ?_⟩
  rw [d.segmentProductDatum_induced Δ hΔ]
  exact hP.of_targetEquiv (SmoothRep.equivOfIso e)

end SpehDatum

end Langlands.Classification
