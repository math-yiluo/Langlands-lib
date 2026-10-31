import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.HarmonicAnalysis.PadicLatticeTopology

/-!
# Proof of the compact last-row cutoff for zero-row Whittaker coefficients

An open stabilizer of a preimage vector contains small upper columns. Conjugating
them by `diag(g, I)` makes the Whittaker character read the last row of `g`, and
the additive conductor bounds that row. See the paired Markdown for the route.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open HarmonicAnalysis

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- If `x ↦ ψ(a x)` is trivial on `π^(-m) O`, then `a` lies in `π^(m - n(ψ)) O`. -/
theorem mem_additiveLattice_of_forall_mul_eq_one (ψ : AdditiveCharacter)
    (m : ℤ) (a : F.Carrier) (h : ∀ x ∈ T.additiveLattice m, ψ (a * x) = 1) :
    a ∈ T.additiveLattice (T.additiveConductor ψ - m) := by
  have hπ : T.uniformizer ^ (-m) ≠ 0 := by
    apply zpow_ne_zero
    apply T.discreteValuation.ne_zero_iff.mp
    rw [T.discreteValuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hlevel : T.additiveConductor ψ - m =
      T.additiveConductor ψ + T.ord (T.uniformizer ^ (-m)) := by
    rw [T.ord_zpow, T.ord_uniformizer, mul_one, sub_eq_add_neg]
  rw [hlevel]
  apply (T.mul_mem_additiveLattice_iff hπ _ a).mp
  apply (T.integer_annihilator_iff_mem_additiveLattice ψ _).mp
  intro t
  have ht : T.uniformizer ^ (-m) * (t : F.Carrier) ∈ T.additiveLattice m :=
    (T.mem_additiveLattice_iff_exists_integer m _).mpr ⟨t, rfl⟩
  have hprod : (t : F.Carrier) * (T.uniformizer ^ (-m) * a) =
      a * (T.uniformizer ^ (-m) * (t : F.Carrier)) := by ring
  rw [hprod]
  exact h _ ht

end Langlands.PadicField.TopologicalData

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis Topology
open scoped Matrix

universe uF uV

section Column

variable {F : Type uF} [Field F]

private theorem sum_initial {d N : ℕ} (hd : d ≤ N) (f : Fin N → F)
    (hf : ∀ i, d ≤ i.val → f i = 0) :
    (∑ i, f i) = ∑ i : Fin d, f ⟨i.val, lt_of_lt_of_le i.isLt hd⟩ := by
  let e : Fin d ↪ Fin N :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hd⟩,
      fun i j h => Fin.ext (congrArg (fun x : Fin N => x.val) h)⟩
  have hs : ∑ i ∈ Finset.univ.map e, f i = ∑ i : Fin N, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply hf
    by_contra hn
    apply hi
    exact Finset.mem_map.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
  rw [← hs, Finset.sum_map]
  rfl

/-- The column supported in the first `n + 1` rows and the first appended
coordinate `n + 1`, inside rank `n + (d + 1) + 1`. -/
def zeroRowColumnEntries (n d : ℕ) (y : Fin (n + 1) → F) :
    Matrix (Fin (n + (d + 1) + 1)) (Fin (n + (d + 1) + 1)) F :=
  fun a b =>
    if ha : a.val < n + 1 then
      if b.val = n + 1 then y ⟨a.val, ha⟩ else 0
    else 0

/-- Any two such columns have zero product. -/
theorem zeroRowColumnEntries_mul (n d : ℕ) (y y' : Fin (n + 1) → F) :
    zeroRowColumnEntries n d y * zeroRowColumnEntries n d y' = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c.val < n + 1
  · have hc' : c.val ≠ n + 1 := by omega
    simp [zeroRowColumnEntries, hc, hc']
  · simp [zeroRowColumnEntries, hc]

@[simp] theorem zeroRowColumnEntries_zero (n d : ℕ) :
    zeroRowColumnEntries (F := F) n d 0 = 0 := by
  ext a b
  simp [zeroRowColumnEntries]

/-- All entries on or below the diagonal vanish. -/
theorem zeroRowColumnEntries_eq_zero_of_le (n d : ℕ) (y : Fin (n + 1) → F)
    {a b : Fin (n + (d + 1) + 1)} (h : b ≤ a) :
    zeroRowColumnEntries n d y a b = 0 := by
  by_cases ha : a.val < n + 1
  · have hb : b.val ≠ n + 1 := by
      simp only [Fin.le_def] at h
      omega
    simp [zeroRowColumnEntries, ha, hb]
  · simp [zeroRowColumnEntries, ha]

/-- The actual column unipotent `I + E(y)`, with explicit inverse `I - E(y)`. -/
def zeroRowColumnUnipotent (n d : ℕ) (y : Fin (n + 1) → F) :
    Langlands.GeneralLinear (n + (d + 1) + 1) F where
  val := 1 + zeroRowColumnEntries n d y
  inv := 1 - zeroRowColumnEntries n d y
  val_inv := by simp [mul_sub, add_mul, zeroRowColumnEntries_mul]
  inv_val := by simp [sub_mul, mul_add, zeroRowColumnEntries_mul]

@[simp] theorem zeroRowColumnUnipotent_val (n d : ℕ) (y : Fin (n + 1) → F) :
    (zeroRowColumnUnipotent n d y).val = 1 + zeroRowColumnEntries n d y := rfl

@[simp] theorem zeroRowColumnUnipotent_zero (n d : ℕ) :
    zeroRowColumnUnipotent (F := F) n d 0 = 1 := by
  apply Units.ext
  simp

/-- The column unipotent belongs to the actual upper-unipotent subgroup. -/
theorem zeroRowColumnUnipotent_mem_upperUnipotent (n d : ℕ) (y : Fin (n + 1) → F) :
    zeroRowColumnUnipotent n d y ∈ upperUnipotent (n + (d + 1) + 1) F := by
  constructor
  · intro a b hab
    change b < a at hab
    change (1 + zeroRowColumnEntries n d y) a b = 0
    simp only [Matrix.add_apply, Matrix.one_apply, ite_eq_right (ne_of_gt hab),
      zeroRowColumnEntries_eq_zero_of_le n d y (le_of_lt hab), add_zero]
  · intro a
    change (1 + zeroRowColumnEntries n d y) a a = 1
    simp [zeroRowColumnEntries_eq_zero_of_le n d y le_rfl]

/-- The first superdiagonal of `I + E(y)` has the single entry `y_n`. -/
theorem zeroRowColumnUnipotent_superdiagonal_sum (n d : ℕ) (y : Fin (n + 1) → F) :
    ∑ i : Fin (n + (d + 1)),
        (zeroRowColumnUnipotent n d y).val i.castSucc i.succ = y (Fin.last n) := by
  rw [Fintype.sum_eq_single (⟨n, by omega⟩ : Fin (n + (d + 1)))]
  · have hne : (Fin.castSucc (⟨n, by omega⟩ : Fin (n + (d + 1)))) ≠
        Fin.succ (⟨n, by omega⟩ : Fin (n + (d + 1))) := by
      simp [Fin.ext_iff]
    simp only [zeroRowColumnUnipotent_val, Matrix.add_apply, Matrix.one_apply_ne hne,
      zero_add, zeroRowColumnEntries]
    simp [Fin.last]
  · intro i hi
    have hi' : i.val ≠ n := fun h => hi (Fin.ext h)
    have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
    simp only [zeroRowColumnUnipotent_val, Matrix.add_apply, Matrix.one_apply_ne hne,
      zero_add, zeroRowColumnEntries]
    by_cases ha : i.val < n + 1
    · simp [ha, hi']
    · simp [ha]

/-- The standard character reads the last coordinate of the column. -/
theorem standardCharacter_zeroRowColumnUnipotent [TopologicalSpace F]
    (ψ : UnitaryAdditiveCharacter F) (n d : ℕ) (y : Fin (n + 1) → F) :
    (standardCharacter ψ (n + (d + 1))
        ⟨zeroRowColumnUnipotent n d y,
          zeroRowColumnUnipotent_mem_upperUnipotent n d y⟩ : ℂ) =
      ψ.complex (y (Fin.last n)) := by
  rw [standardCharacter_apply]
  exact congrArg ψ.complex (zeroRowColumnUnipotent_superdiagonal_sum n d y)

/-- Left multiplication by `diag(g, I)` moves the column to `g y`. -/
theorem appendIdentity_mul_zeroRowColumnEntries (n d : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) (y : Fin (n + 1) → F) :
    (appendIdentity n (d + 1) g).val * zeroRowColumnEntries n d y =
      zeroRowColumnEntries n d (g.val *ᵥ y) := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hb : b.val = n + 1
  · rw [sum_initial (d := n + 1) (by omega) _ (by
      intro c hc
      simp [zeroRowColumnEntries, show ¬c.val < n + 1 by omega])]
    by_cases ha : a.val < n + 1
    · simp [zeroRowColumnEntries, ha, hb, Matrix.mulVec, dotProduct, appendIdentity_entry,
        Fin.is_le]
    · apply (Finset.sum_eq_zero _).trans
      · simp [zeroRowColumnEntries, ha]
      · intro c _
        have hac : (a : Fin (n + (d + 1) + 1)) ≠ ⟨c.val, by omega⟩ := by
          intro h
          rw [Fin.ext_iff] at h
          simp at h
          omega
        simp [appendIdentity_entry, ha, hac]
  · simp [zeroRowColumnEntries, hb]

/-- Right multiplication by `diag(g, I)` fixes the column. -/
theorem zeroRowColumnEntries_mul_appendIdentity (n d : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) (z : Fin (n + 1) → F) :
    zeroRowColumnEntries n d z * (appendIdentity n (d + 1) g).val =
      zeroRowColumnEntries n d z := by
  let c : Fin (n + (d + 1) + 1) := ⟨n + 1, by omega⟩
  ext a b
  rw [Matrix.mul_apply]
  by_cases ha : a.val < n + 1
  · rw [Fintype.sum_eq_single c]
    · have hrow : (appendIdentity n (d + 1) g).val c b = if c = b then 1 else 0 := by
        have hc : ¬ c.val < n + 1 := by simp [c]
        rw [appendIdentity_entry]
        simp only [dite_eq_right hc]
      rw [hrow]
      have hc : b.val = n + 1 ↔ c = b := by
        constructor <;> intro h
        · apply Fin.ext
          exact h.symm
        · exact (congrArg Fin.val h).symm
      simp [zeroRowColumnEntries, ha, c, hc]
    · intro i hi
      have hi' : i.val ≠ n + 1 := by
        intro h
        exact hi (Fin.ext h)
      simp [zeroRowColumnEntries, ha, hi']
  · simp [zeroRowColumnEntries, ha]

/-- Conjugation identity `diag(g, I) (I + E(y)) = (I + E(g y)) diag(g, I)`. -/
theorem appendIdentity_mul_zeroRowColumnUnipotent (n d : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) (y : Fin (n + 1) → F) :
    appendIdentity n (d + 1) g * zeroRowColumnUnipotent n d y =
      zeroRowColumnUnipotent n d (g.val *ᵥ y) * appendIdentity n (d + 1) g := by
  apply Units.ext
  change (appendIdentity n (d + 1) g).val * (1 + zeroRowColumnEntries n d y) =
    (1 + zeroRowColumnEntries n d (g.val *ᵥ y)) * (appendIdentity n (d + 1) g).val
  rw [mul_add, mul_one, add_mul, one_mul, appendIdentity_mul_zeroRowColumnEntries,
    zeroRowColumnEntries_mul_appendIdentity]

section Topology

variable [TopologicalSpace F]

/-- Continuity of the supported column for the supplied topology. -/
theorem continuous_zeroRowColumnEntries (n d : ℕ) :
    Continuous (zeroRowColumnEntries (F := F) n d) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases ha : a.val < n + 1
  · by_cases hb : b.val = n + 1
    · simpa only [zeroRowColumnEntries, dite_eq_left ha, ite_eq_left hb] using
        (continuous_apply (⟨a.val, ha⟩ : Fin (n + 1)) :
          Continuous fun y : Fin (n + 1) → F => y ⟨a.val, ha⟩)
    · simpa only [zeroRowColumnEntries, dite_eq_left ha, ite_eq_right hb] using
        (continuous_const : Continuous fun _ : Fin (n + 1) → F => (0 : F))
  · simpa only [zeroRowColumnEntries, dite_eq_right ha] using
      (continuous_const : Continuous fun _ : Fin (n + 1) → F => (0 : F))

variable [IsTopologicalRing F]

/-- Continuity into `GL` checks both the value and its explicit inverse. -/
theorem continuous_zeroRowColumnUnipotent (n d : ℕ) :
    Continuous (zeroRowColumnUnipotent (F := F) n d) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous fun y : Fin (n + 1) → F =>
      (1 : Matrix _ _ F) + zeroRowColumnEntries n d y
    exact continuous_const.add (continuous_zeroRowColumnEntries n d)
  · change Continuous fun y : Fin (n + 1) → F =>
      (1 : Matrix _ _ F) - zeroRowColumnEntries n d y
    exact continuous_const.sub (continuous_zeroRowColumnEntries n d)

end Topology

end Column

/-- Every smooth zero-row Whittaker coefficient admits a zero-or-one compact
open last-row cutoff, for every supplied p-adic field realization. -/
theorem zeroRowLastRowCutoff : ZeroRowLastRowCutoffStatement.{uF,uV} := by
  intro p _ F T n k
  let := T.topology
  let := T.valuativeRel
  let := T.valuativeExtension
  let := T.moduleTopology
  let := T.localField
  intro ψ V _ _ π hπ ℓ f
  have : T2Space F.Carrier := T.fieldT2
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  obtain ⟨K, hK⟩ := hπ v
  have hfix : ∀ u ∈ K, π u v = v := fun u hu =>
    (Representation.mem_invariants _ v).mp hK ⟨u, hu⟩
  -- A lattice of single-coordinate columns fixing `v`.
  let s : Set F.Carrier := ⋂ i : Fin (n + 1),
    (fun x => zeroRowColumnUnipotent n (0 + k) (Pi.single i x)) ⁻¹'
      (K : Set (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier))
  have hs : IsOpen s := isOpen_iInter_of_finite fun i =>
    K.isOpen.preimage ((continuous_zeroRowColumnUnipotent n (0 + k)).comp
      (continuous_single i))
  have h0 : (0 : F.Carrier) ∈ s := by
    simp only [s, Set.mem_iInter, Set.mem_preimage, Pi.single_zero,
      zeroRowColumnUnipotent_zero]
    exact fun _ => K.one_mem
  obtain ⟨m, hm⟩ := T.exists_additiveLattice_subset (hs.mem_nhds h0)
  -- The compact open box of last rows.
  let M : ℤ := T.additiveConductor ψ - m
  let B : Set (Fin (n + 1) → F.Carrier) :=
    Set.univ.pi fun _ => (T.additiveLattice M : Set F.Carrier)
  have hBc : IsCompact B := isCompact_univ_pi fun _ => T.isCompact_additiveLattice M
  have hBo : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_additiveLattice M
  refine ⟨compactOpenIndicator B hBc hBo, fun y => ?_, fun g => ?_⟩
  · rw [coe_compactOpenIndicator]
    by_cases hy : y ∈ B
    · exact Or.inr (Set.indicator_of_mem hy _)
    · exact Or.inl (Set.indicator_of_notMem hy _)
  · let h := appendIdentity n (0 + k + 1) g
    change ℓ.val (π h v) * _ = ℓ.val (π h v)
    by_cases hz : ℓ.val (π h v) = 0
    · rw [hz, zero_mul]
    · have hrow : lastRow g ∈ B := by
        intro i _
        apply T.mem_additiveLattice_of_forall_mul_eq_one ψ m
        intro x hx
        let z : Fin (n + 1) → F.Carrier := g.val *ᵥ Pi.single i x
        have hU : zeroRowColumnUnipotent n (0 + k) (Pi.single i x) ∈ K :=
          Set.mem_iInter.mp (hm hx) i
        have hkey := appendIdentity_mul_zeroRowColumnUnipotent n (0 + k) g (Pi.single i x)
        have hact : π (zeroRowColumnUnipotent n (0 + k) z) (π h v) = π h v := by
          calc
            π (zeroRowColumnUnipotent n (0 + k) z) (π h v) =
                π (zeroRowColumnUnipotent n (0 + k) z * h) v := by
              rw [map_mul, Module.End.mul_apply]
            _ = π (appendIdentity n (0 + k + 1) g *
                zeroRowColumnUnipotent n (0 + k) (Pi.single i x)) v := by
              rw [hkey]
            _ = π h v := by
              rw [map_mul, Module.End.mul_apply, hfix _ hU]
        have heq := ℓ.property
          ⟨zeroRowColumnUnipotent n (0 + k) z,
            zeroRowColumnUnipotent_mem_upperUnipotent n (0 + k) z⟩ (π h v)
        change ℓ.val (π (zeroRowColumnUnipotent n (0 + k) z) (π h v)) = _ at heq
        rw [hact, standardCharacter_zeroRowColumnUnipotent] at heq
        have hone : ψ.complex (z (Fin.last n)) = 1 :=
          mul_right_cancel₀ hz (heq.symm.trans (one_mul _).symm)
        have hzlast : z (Fin.last n) = lastRow g i * x := by
          simp [z, Matrix.mulVec_single, lastRow, mul_comm]
        rw [hzlast] at hone
        apply Subtype.ext
        simpa using hone
      rw [coe_compactOpenIndicator, Set.indicator_of_mem hrow, mul_one]

end Langlands.RankinSelberg
