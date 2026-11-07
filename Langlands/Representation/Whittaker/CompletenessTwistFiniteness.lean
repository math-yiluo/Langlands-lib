import Langlands.Representation.Whittaker.CompletenessUnlinkedBase
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Twist.SubquotientProof

/-!
# Whittaker completeness: finitely many exceptional twists

Twist the blocks `ρ_a` with `S a` of a family of cuspidal data by `ν^u`, leaving the
others unchanged. Only finitely many real `u` link a pair `(a, b)` with one block
twisted and the other not. Pairs with both blocks on the same side keep their
linkage status. So if some crossing pair is linked at `u = 0`, then for all `u ≠ 0`
near `0` the twisted family has fewer linked ordered pairs. This is the counting
step of the reduction of Jacquet–Shalika 1985, Lemma (3.2), to unlinked products of
supercuspidals.
-/

noncomputable section

open Filter Topology

namespace Langlands.PadicField.TopologicalData.CuspidalDatum

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Real twist freeness: `ν^s ρ = ρ` only for `s = 0`. The central character of an
irreducible admissible representation of `GL_r(F)` changes by `|ϖ|^(r s)` on the
scalar uniformizer under `ν^s`. -/
theorem twist_eq_self_iff (ρ : CuspidalDatum.{uV, uF} T) (s : ℝ) : ρ.twist s = ρ ↔ s = 0 := by
  let := T.topology
  constructor
  · intro h
    rcases ρ with ⟨r, hr, c⟩
    have hc : T.supercuspidalClassRealPowerTwist r s c = c := by
      simpa only [twist, mk.injEq, heq_eq_eq, true_and] using h
    induction c using Quotient.inductionOn with
    | h A =>
      let At := GeneralLinear.SupercuspidalRep.twist (T.determinantPowerCharacter r s)
        (T.isOpen_ker_determinantPowerCharacter r s)
        (T.ker_determinant_le_ker_determinantPowerCharacter r s) A
      change At.isoClass = A.isoClass at hc
      obtain ⟨e⟩ := (GeneralLinear.SupercuspidalRep.isoClass_eq_iff At A).mp hc
      let e' := SmoothRep.equivOfIso ((GeneralLinear.supercuspidalProperty (F := F.Carrier)
        (n := r)).ι.mapIso e.symm)
      exact Classification.IntegralTwistFreeness.exponent_eq_zero_of_equiv T r hr A.obj
        A.property.2.1 A.property.1 s e'
  · rintro rfl
    simp

/-- `s ↦ ν^s ρ` is injective. -/
theorem twist_injective (ρ : CuspidalDatum.{uV, uF} T) :
    Function.Injective fun s : ℝ => ρ.twist s := by
  intro s t h
  have h' : (ρ.twist s).twist (-t) = (ρ.twist t).twist (-t) :=
    congrArg (twist (-t)) (show ρ.twist s = ρ.twist t from h)
  rw [twist_twist, twist_twist, neg_add_cancel, twist_zero, twist_eq_self_iff] at h'
  linarith

theorem twist_inj {ρ : CuspidalDatum.{uV, uF} T} {s t : ℝ} : ρ.twist s = ρ.twist t ↔ s = t :=
  ρ.twist_injective.eq_iff

/-- Twisting by a common `ν^s` is injective. -/
theorem twist_left_inj {ρ σ : CuspidalDatum.{uV, uF} T} (s : ℝ) :
    ρ.twist s = σ.twist s ↔ ρ = σ := by
  constructor
  · intro h
    simpa [twist_twist] using congrArg (twist (-s)) h
  · rintro rfl
    rfl

/-- No cuspidal datum is linked to itself: `ρ ≠ ν ρ`. -/
theorem ne_twist_one (ρ : CuspidalDatum.{uV, uF} T) : ρ ≠ ρ.twist 1 := fun h =>
  one_ne_zero ((twist_eq_self_iff ρ 1).mp h.symm)

end Langlands.PadicField.TopologicalData.CuspidalDatum

namespace Langlands.Whittaker

open PadicField.TopologicalData

universe uF uV uW

section Data

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData} {k : ℕ}

/-- The ordered pairs `(a, b)` of blocks with `ρ_a = ν ρ_b`. -/
def linkedPairs (ρ : Fin k → CuspidalDatum.{uV, uF} T) : Set (Fin k × Fin k) :=
  {ab | ρ ab.1 = (ρ ab.2).twist 1}

/-- The number of ordered pairs `(a, b)` with `ρ_a = ν ρ_b`. -/
def linkedCount (ρ : Fin k → CuspidalDatum.{uV, uF} T) : ℕ :=
  (linkedPairs ρ).ncard

theorem mem_linkedPairs {ρ : Fin k → CuspidalDatum.{uV, uF} T} {ab : Fin k × Fin k} :
    ab ∈ linkedPairs ρ ↔ ρ ab.1 = (ρ ab.2).twist 1 :=
  Iff.rfl

/-- The family has no linked pair exactly when its linked-pair count is zero. -/
theorem linkedCount_eq_zero_iff (ρ : Fin k → CuspidalDatum.{uV, uF} T) :
    linkedCount ρ = 0 ↔ ∀ a b, ρ a ≠ (ρ b).twist 1 := by
  rw [linkedCount, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h a b hab => h (a, b) hab, fun h ab hab => h ab.1 ab.2 hab⟩

/-- A linked family can be cut after some block `j` so that a linked pair crosses the
cut. -/
theorem exists_crossing_of_linkedCount_ne_zero (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (h : linkedCount ρ ≠ 0) :
    ∃ j a b, ¬(j < a ↔ j < b) ∧ ρ a = (ρ b).twist 1 := by
  have h₀ : ¬∀ a b, ρ a ≠ (ρ b).twist 1 := fun h' => h ((linkedCount_eq_zero_iff ρ).mpr h')
  push Not at h₀
  obtain ⟨a, b, hab⟩ := h₀
  have hne : a ≠ b := by
    rintro rfl
    exact (ρ a).ne_twist_one hab
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨a, a, b, by simp [hlt], hab⟩
  · exact ⟨b, a, b, by simp [hlt], hab⟩

/-- Twist the blocks `a` with `S a` by `ν^u` and leave the others unchanged. -/
def twistOn (S : Fin k → Prop) [DecidablePred S] (u : ℝ)
    (ρ : Fin k → CuspidalDatum.{uV, uF} T) (a : Fin k) : CuspidalDatum.{uV, uF} T :=
  (ρ a).twist (if S a then u else 0)

variable (S : Fin k → Prop) [DecidablePred S]

theorem twistOn_of_pos (u : ℝ) (ρ : Fin k → CuspidalDatum.{uV, uF} T) {a : Fin k}
    (ha : S a) : twistOn S u ρ a = (ρ a).twist u := by
  simp [twistOn, ha]

theorem twistOn_of_neg (u : ℝ) (ρ : Fin k → CuspidalDatum.{uV, uF} T) {a : Fin k}
    (ha : ¬S a) : twistOn S u ρ a = ρ a := by
  simp [twistOn, ha]

@[simp]
theorem twistOn_zero (ρ : Fin k → CuspidalDatum.{uV, uF} T) : twistOn S 0 ρ = ρ := by
  funext a
  simp [twistOn]

/-- A pair with both blocks on the same side keeps its linkage status. -/
theorem twistOn_linked_iff_of_iff (u : ℝ) (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    {a b : Fin k} (hab : S a ↔ S b) :
    twistOn S u ρ a = (twistOn S u ρ b).twist 1 ↔ ρ a = (ρ b).twist 1 := by
  have hc : (if S b then u else 0) = if S a then u else 0 := by
    simp only [hab]
  rw [twistOn, twistOn, hc, CuspidalDatum.twist_twist, add_comm,
    ← CuspidalDatum.twist_twist, CuspidalDatum.twist_left_inj]

/-- A crossing pair is linked for at most one twist parameter. -/
theorem subsingleton_setOf_crossing_linked (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (a b : Fin k) :
    {u : ℝ | ¬(S a ↔ S b) ∧ twistOn S u ρ a = (twistOn S u ρ b).twist 1}.Subsingleton := by
  rintro u ⟨hab, hu⟩ v ⟨-, hv⟩
  by_cases ha : S a
  · have hb : ¬S b := fun hb => hab (iff_of_true ha hb)
    rw [twistOn_of_pos S u ρ ha, twistOn_of_neg S u ρ hb] at hu
    rw [twistOn_of_pos S v ρ ha, twistOn_of_neg S v ρ hb] at hv
    exact CuspidalDatum.twist_inj.mp (hu.trans hv.symm)
  · have hb : S b := not_not.mp fun hb => hab (iff_of_false ha hb)
    rw [twistOn_of_neg S u ρ ha, twistOn_of_pos S u ρ hb, CuspidalDatum.twist_twist] at hu
    rw [twistOn_of_neg S v ρ ha, twistOn_of_pos S v ρ hb, CuspidalDatum.twist_twist] at hv
    have h := CuspidalDatum.twist_inj.mp (hu.symm.trans hv)
    linarith

/-- P6. Only finitely many twist parameters link a crossing pair. -/
theorem finite_setOf_crossing_linked (ρ : Fin k → CuspidalDatum.{uV, uF} T) :
    {u : ℝ | ∃ a b, ¬(S a ↔ S b) ∧ twistOn S u ρ a = (twistOn S u ρ b).twist 1}.Finite := by
  have heq : {u : ℝ | ∃ a b, ¬(S a ↔ S b) ∧ twistOn S u ρ a = (twistOn S u ρ b).twist 1} =
      ⋃ a, ⋃ b,
        {u : ℝ | ¬(S a ↔ S b) ∧ twistOn S u ρ a = (twistOn S u ρ b).twist 1} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact Set.finite_iUnion fun a => Set.finite_iUnion fun b =>
    (subsingleton_setOf_crossing_linked S ρ a b).finite

/-- For all `u ≠ 0` near `0`, no crossing pair of the twisted family is linked. -/
theorem eventually_not_crossing_linked (ρ : Fin k → CuspidalDatum.{uV, uF} T) :
    ∀ᶠ u in 𝓝[≠] (0 : ℝ), ∀ a b, ¬(S a ↔ S b) →
      twistOn S u ρ a ≠ (twistOn S u ρ b).twist 1 := by
  set E := {u : ℝ | ∃ a b, ¬(S a ↔ S b) ∧ twistOn S u ρ a = (twistOn S u ρ b).twist 1}
  have hE : IsClosed (E \ {0}) := ((finite_setOf_crossing_linked S ρ).sdiff).isClosed
  have h0 : (E \ {0})ᶜ ∈ 𝓝 (0 : ℝ) := hE.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h0, self_mem_nhdsWithin] with u hu hu0
  intro a b hab hl
  exact hu ⟨⟨a, b, hab, hl⟩, hu0⟩

/-- Away from the exceptional parameters, the linked pairs of the twisted family are
linked pairs of the original family that do not cross. -/
theorem linkedPairs_twistOn_subset (ρ : Fin k → CuspidalDatum.{uV, uF} T) {u : ℝ}
    (hu : ∀ a b, ¬(S a ↔ S b) → twistOn S u ρ a ≠ (twistOn S u ρ b).twist 1) :
    linkedPairs (twistOn S u ρ) ⊆ linkedPairs ρ := by
  rintro ⟨a, b⟩ hab
  by_cases hs : S a ↔ S b
  · exact (twistOn_linked_iff_of_iff S u ρ hs).mp hab
  · exact absurd hab (hu a b hs)

/-- The linked-pair count of the twisted family drops below that of the original
family when the original family has a linked crossing pair and `u` is not
exceptional. -/
theorem linkedCount_twistOn_lt (ρ : Fin k → CuspidalDatum.{uV, uF} T) {u : ℝ}
    (hu : ∀ a b, ¬(S a ↔ S b) → twistOn S u ρ a ≠ (twistOn S u ρ b).twist 1)
    (h : ∃ a b, ¬(S a ↔ S b) ∧ ρ a = (ρ b).twist 1) :
    linkedCount (twistOn S u ρ) < linkedCount ρ := by
  obtain ⟨a, b, hab, hl⟩ := h
  refine Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset
    (linkedPairs_twistOn_subset S ρ hu)).mpr ⟨(a, b), hl, ?_⟩) (Set.toFinite _)
  exact hu a b hab

/-- P6, counting form. If a crossing pair is linked, then for all `u ≠ 0` near `0` the
twisted family has fewer linked ordered pairs. -/
theorem eventually_linkedCount_twistOn_lt (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (h : ∃ a b, ¬(S a ↔ S b) ∧ ρ a = (ρ b).twist 1) :
    ∀ᶠ u in 𝓝[≠] (0 : ℝ), linkedCount (twistOn S u ρ) < linkedCount ρ := by
  filter_upwards [eventually_not_crossing_linked S ρ] with u hu
  exact linkedCount_twistOn_lt S ρ hu h

end Data

section Blocks

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

variable {k : ℕ} {m : Fin k → ℕ}
  {W : Fin k → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Twist each block `τ a` by `ν^(c a) = |det|^(c a)`. -/
def twistBlocks (c : Fin k → ℝ)
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)) (a : Fin k) :
    Representation ℂ (Langlands.GeneralLinear (m a + 1) F.Carrier) (W a) :=
  Langlands.twist (F.canonicalTopologicalData.determinantPowerCharacter (m a + 1) (c a)) (τ a)

variable (c : Fin k → ℝ)
  (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))

theorem isSmooth_twistBlocks (hs : ∀ i, IsSmooth (τ i)) (a : Fin k) :
    IsSmooth (twistBlocks c τ a) :=
  (isSmooth_twist_iff _ (τ a)
    (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (m a + 1) (c a))).mpr
    (hs a)

theorem isIrreducible_twistBlocks (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (a : Fin k) : Representation.IsIrreducible (twistBlocks c τ a) :=
  (isIrreducible_twist_iff _ (τ a)).mpr (hirr a)

theorem isSupercuspidal_twistBlocks (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (a : Fin k) : GeneralLinear.IsSupercuspidal (twistBlocks c τ a) :=
  (GeneralLinear.isSupercuspidal_twist_iff _
    (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (m a + 1) (c a))
    (F.canonicalTopologicalData.ker_determinant_le_ker_determinantPowerCharacter (m a + 1)
      (c a)) (τ a)).mpr (hsc a)

/-- The datum of the twisted block `τ a ⊗ ν^(c a)` is `ν^(c a)` times the datum of
`τ a`. -/
theorem blockDatum_twistBlocks (hs : ∀ i, IsSmooth (τ i))
    (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (hs' : ∀ i, IsSmooth (twistBlocks c τ i))
    (hirr' : ∀ i, Representation.IsIrreducible (twistBlocks c τ i))
    (hsc' : ∀ i, GeneralLinear.IsSupercuspidal (twistBlocks c τ i)) (a : Fin k) :
    blockDatum (twistBlocks c τ) hs' hirr' hsc' a = (blockDatum τ hs hirr hsc a).twist (c a) :=
  rfl

/-- Twisting the blocks with `S a` by `ν^u` twists their data the same way. -/
theorem blockDatum_twistBlocks_ite (S : Fin k → Prop) [DecidablePred S] (u : ℝ)
    (hs : ∀ i, IsSmooth (τ i))
    (hirr : ∀ i, Representation.IsIrreducible (τ i))
    (hsc : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (hs' : ∀ i, IsSmooth (twistBlocks (fun i => if S i then u else 0) τ i))
    (hirr' : ∀ i, Representation.IsIrreducible (twistBlocks (fun i => if S i then u else 0) τ i))
    (hsc' : ∀ i, GeneralLinear.IsSupercuspidal (twistBlocks (fun i => if S i then u else 0) τ i)) :
    blockDatum (twistBlocks (fun i => if S i then u else 0) τ) hs' hirr' hsc' =
      twistOn S u (blockDatum τ hs hirr hsc) :=
  rfl

end Blocks

end Langlands.Whittaker
