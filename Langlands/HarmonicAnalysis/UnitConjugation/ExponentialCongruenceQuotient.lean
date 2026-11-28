import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialCongruenceHaar
import Mathlib.Topology.Algebra.Group.Compact

/-! # Exponential coordinates on finite congruence quotients -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Function Metric

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

local notation "B(" R "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup R h)
local notation "K(" R "," h "," k ")" => normUnitCongruence (R := R) (le_of_lt h) k

/-- The additive ball of radius `s` pulled back to the additive ball of radius `r`. -/
def additiveCongruenceLevel {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : AddSubgroup B(R, hr) :=
  B(R, hs).comap B(R, hr).subtype

/-- The unit subgroup of radius `s` pulled back to the unit subgroup of radius `r`. -/
def unitCongruenceLevel {r s : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hs : 0 < s) (hs₁ : s < 1) : Subgroup K(R, hr, hr₁) :=
  K(R, hs, hs₁).subgroupOf K(R, hr, hr₁)

theorem unitCongruenceLevel_normal {r s : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hsmall : max 1 ‖(1 : R)‖ * r < 1) (hs : 0 < s) (hs₁ : s < 1) :
    (unitCongruenceLevel (R := R) hr hr₁ hs hs₁).Normal := by
  constructor
  intro n hn g
  change ‖(g.val : R) * (n.val : R) * (g.val⁻¹ : Rˣ).val - 1‖ ≤ s
  have h : (g.val : R) * (n.val : R) * (g.val⁻¹ : Rˣ).val - 1 =
      conjugationHomeomorph g.val ((n.val : R) - 1) := by
    rw [conjugationHomeomorph_apply, mul_sub, mul_one, sub_mul, Units.mul_inv]
  rw [h, norm_conjugation_eq_of_mem_normUnitCongruence hr.le hr₁ hsmall g.property]
  exact hn

private theorem norm_mul_right_unit (u : Rˣ) (hu : ‖(u : R) - 1‖ < 1) (x : R) :
    ‖x * (u : R)‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hlt : ‖x * ((u : R) - 1)‖ < ‖x‖ := calc
    _ ≤ ‖x‖ * ‖(u : R) - 1‖ := norm_mul_le _ _
    _ < ‖x‖ * 1 := mul_lt_mul_of_pos_left hu (norm_pos_iff.mpr hx)
    _ = _ := mul_one _
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  rwa [max_eq_right hlt.le, mul_sub, mul_one, sub_add_cancel] at h

/-- Equality of two classes in a unit congruence quotient is the distance condition
on their unit values. -/
theorem unitCongruence_mk_eq_iff {r s : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hsmall : max 1 ‖(1 : R)‖ * r < 1) (hs : 0 < s) (hs₁ : s < 1)
    {u v : K(R, hr, hr₁)} :
    (QuotientGroup.mk u : K(R, hr, hr₁) ⧸ unitCongruenceLevel hr hr₁ hs hs₁) = QuotientGroup.mk v ↔
      dist (u.val : R) (v.val : R) ≤ s := by
  let _ := unitCongruenceLevel_normal hr hr₁ hsmall hs hs₁
  rw [QuotientGroup.eq_iff_div_mem, dist_eq_norm]
  change ‖(u.val : R) * (v.val⁻¹ : Rˣ).val - 1‖ ≤ s ↔ _
  rw [show (u.val : R) * (v.val⁻¹ : Rˣ).val - 1 =
      ((u.val : R) - (v.val : R)) * (v.val⁻¹ : Rˣ).val by rw [sub_mul, Units.mul_inv],
    norm_mul_right_unit _ (((K(R, hr, hr₁)).inv_mem v.property :
      ‖(v.val⁻¹ : Rˣ).val - 1‖ ≤ r).trans_lt hr₁)]

private def equivOfQuotientMaps {X Y X' Y' : Type*} (f : X → X') (g : Y → Y')
    (hf : Surjective f) (hg : Surjective g) (E : X ≃ Y)
    (hE : ∀ x z, f x = f z ↔ g (E x) = g (E z)) :
    { e : X' ≃ Y' // ∀ x, e (f x) = g (E x) } := by
  let v := hf.hasRightInverse.choose
  have hv := hf.hasRightInverse.choose_spec
  let e := g ∘ E ∘ v
  have he (x : X) : e (f x) = g (E x) := (hE (v (f x)) x).1 (hv (f x))
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, he⟩
  · intro a b h
    exact (hv a).symm.trans (((hE (v a) (v b)).2 h).trans (hv b))
  · intro y
    obtain ⟨x, hx⟩ := hg y
    exact ⟨f (E.symm x), by rw [he, E.apply_symm_apply, hx]⟩

theorem additiveCongruence_mk_eq_iff {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {x y : B(R, hr)} :
    (QuotientAddGroup.mk x : B(R, hr) ⧸ additiveCongruenceLevel hr hs) = QuotientAddGroup.mk y ↔
      dist (x : R) (y : R) ≤ s := by
  rw [QuotientAddGroup.eq_iff_sub_mem, dist_eq_norm]
  change dist ((x : R) - (y : R)) 0 ≤ s ↔ _
  rw [dist_zero_right]

/-- Isometric bijections of the product of two equal balls descend to every
pair of additive congruence quotients at a common radius. -/
theorem additiveCongruencePairEquiv {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (Φ : (B(R, hr) × B(R, hr)) ≃ᵢ (B(R, hr) × B(R, hr))) :
    let Q := B(R, hr) ⧸ additiveCongruenceLevel hr hs
    ∃ Φ' : Q × Q ≃ Q × Q, ∀ z : B(R, hr) × B(R, hr),
      Φ' (QuotientAddGroup.mk z.1, QuotientAddGroup.mk z.2) =
        (QuotientAddGroup.mk (Φ z).1, QuotientAddGroup.mk (Φ z).2) := by
  let Q := B(R, hr) ⧸ additiveCongruenceLevel hr hs
  let q : B(R, hr) × B(R, hr) → Q × Q := Prod.map QuotientAddGroup.mk QuotientAddGroup.mk
  have hq : Surjective q := QuotientAddGroup.mk_surjective.prodMap QuotientAddGroup.mk_surjective
  have hdist {x y : B(R, hr) × B(R, hr)} : q x = q y ↔ dist x y ≤ s := by
    change ((QuotientAddGroup.mk x.1 : Q), (QuotientAddGroup.mk x.2 : Q)) =
      (QuotientAddGroup.mk y.1, QuotientAddGroup.mk y.2) ↔ dist x y ≤ s
    rw [Prod.mk.injEq, additiveCongruence_mk_eq_iff hr hs, additiveCongruence_mk_eq_iff hr hs,
      Prod.dist_eq, max_le_iff]
    rfl
  let E' := equivOfQuotientMaps q q hq hq Φ.toEquiv (fun x y => by
    change q x = q y ↔ q (Φ x) = q (Φ y)
    rw [hdist, hdist, Φ.dist_eq])
  exact ⟨E'.val, E'.property⟩

/-- Small exponential coordinates induce bijections from additive to unit
congruence quotients, and the unit quotients are finite. -/
def ExponentialCongruenceQuotientStatement (F R : Type*) [NontriviallyNormedField F] [CharZero F]
    [IsUltrametricDist F] [NormedRing R] [NormedAlgebra F R] [IsUltrametricDist R]
    [ProperSpace R] : Prop :=
  ∃ ε > (0 : ℝ), ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1), r ≤ ε →
    max 1 ‖(1 : R)‖ * r < 1 →
    ∀ (s : ℝ) (hs : 0 < s) (hs₁ : s < 1),
      let M := unitCongruenceLevel (R := R) hr hr₁ hs hs₁
      let N := additiveCongruenceLevel (R := R) hr hs
      Finite (K(R, hr, hr₁) ⧸ M) ∧
        ∃ E : (B(R, hr) ⧸ N) ≃ (K(R, hr, hr₁) ⧸ M), ∀ x : B(R, hr),
          ∃ u : K(R, hr, hr₁), (u.val : R) = NormedSpace.exp (x : R) ∧
            E (QuotientAddGroup.mk x) = QuotientGroup.mk u

variable {F : Type*} [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
  [NormedAlgebra F R] [ProperSpace R]

theorem exponentialCongruenceQuotient : ExponentialCongruenceQuotientStatement F R := by
  let : MeasurableSpace R := borel R
  let : BorelSpace R := ⟨rfl⟩
  let : MeasurableSpace Rˣ := borel Rˣ
  let : BorelSpace Rˣ := ⟨rfl⟩
  obtain ⟨ε₁, hε₁, H₁⟩ := exponentialBallTransport (F := F) (A := R)
  obtain ⟨ε₂, hε₂, H₂⟩ := exponentialCongruenceHaar (F := F) (A := R)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r hr hr₁ hε hsmall s hs hs₁ => ?_⟩
  obtain ⟨e, he, _⟩ := H₁ r hr (le_min_iff.mp hε).1
  obtain ⟨E, hE, _⟩ := H₂ r hr hr₁ (le_min_iff.mp hε).2
  let E₀ : B(R, hr) ≃ K(R, hr, hr₁) := E.toEquiv
  have hE₀ (x : B(R, hr)) : ((E₀ x).val : R) = NormedSpace.exp (x : R) := hE x
  let M := unitCongruenceLevel (R := R) hr hr₁ hs hs₁
  let N := additiveCongruenceLevel (R := R) hr hs
  let : CompactSpace K(R, hr, hr₁) := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence hr.le hr₁)
  have hMo : IsOpen (M : Set K(R, hr, hr₁)) :=
    (isOpen_normUnitCongruence hs hs₁).preimage continuous_subtype_val
  refine ⟨Subgroup.quotient_finite_of_isOpen M hMo, ?_⟩
  have hclasses (x y : B(R, hr)) :
      (QuotientAddGroup.mk x : B(R, hr) ⧸ N) = QuotientAddGroup.mk y ↔
        (QuotientGroup.mk (E₀ x) : K(R, hr, hr₁) ⧸ M) = QuotientGroup.mk (E₀ y) := by
    rw [additiveCongruence_mk_eq_iff hr hs, unitCongruence_mk_eq_iff hr hr₁ hsmall hs hs₁,
      hE₀ x, hE₀ y]
    let x₀ : Metric.closedBall (0 : R) r := x
    let y₀ : Metric.closedBall (0 : R) r := y
    have h : dist (e x₀ : R) (e y₀ : R) = dist (x₀ : R) (y₀ : R) := e.dist_eq x₀ y₀
    rw [he x₀, he y₀, dist_sub_right] at h
    change dist (NormedSpace.exp (x : R)) (NormedSpace.exp (y : R)) =
      dist (x : R) (y : R) at h
    rw [h]
  let E' := equivOfQuotientMaps (QuotientAddGroup.mk : B(R, hr) → B(R, hr) ⧸ N)
    (QuotientGroup.mk : K(R, hr, hr₁) → K(R, hr, hr₁) ⧸ M)
    QuotientAddGroup.mk_surjective QuotientGroup.mk_surjective E₀ hclasses
  exact ⟨E'.val, fun x => ⟨E₀ x, hE₀ x, E'.property x⟩⟩

end Langlands.HarmonicAnalysis.UnitConjugation
