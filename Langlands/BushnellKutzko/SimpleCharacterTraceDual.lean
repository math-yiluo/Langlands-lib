import Langlands.BushnellKutzko.SimpleCharacterTraceDualStep
import Langlands.BushnellKutzko.CentralizerCharacterDual
import Langlands.BushnellKutzko.SimpleStratumLatticeInduction

/-! # Trace dual of a simple-character layer -/

noncomputable section

open ValuativeRel
open scoped Classical Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "P" => LatticeChain.endFiltration
local notation "Q" => centralizerLattice
local notation "D" => traceDualLattice

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Trace duality exchanges a sum with an intersection. -/
theorem traceDualLattice_sup (ψF : AddChar F ℂ) (M N : Submodule O A) :
    D ψF (M ⊔ N) = D ψF M ⊓ D ψF N :=
  traceDualLattice_sup_aux ψF (D ψF) (fun _ _ => Iff.rfl) M N

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugating the lattice conjugates its trace dual by the same unit. -/
theorem traceDualLattice_map_conj (ψF : AddChar F ℂ) (x : Aˣ) (M : Submodule O A) :
    D ψF (M.map (endUnitConjugation x).toLinearMap) = (D ψF M).map (endUnitConjugation x).toLinearMap :=
  traceDualLattice_map_conj_aux ψF (D ψF) (fun _ _ => Iff.rfl) x M

/-- Trace duality exchanges the intersection with the sum of the two duals
for filtrationally bounded lattices. -/
theorem traceDualLattice_inf_of_bounds (L : LatticeChain O F V) (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) {M N : Submodule O A} (hM : ∃ i j : ℤ, P L i ≤ M ∧ M ≤ P L j)
    (hN : ∃ i j : ℤ, P L i ≤ N ∧ N ≤ P L j) : D ψF (M ⊓ N) = D ψF M ⊔ D ψF N := by
  let := L.finiteDimensional
  obtain ⟨i, j, hi, hj⟩ := hM
  obtain ⟨k, l, hk, hl⟩ := hN
  have hFgd {X : Submodule O A} (i : ℤ) (h : P L i ≤ X) : (D ψF X).FG := by
    have h' := traceDualLattice_antitone ψF h
    rw [traceDualLattice_endFiltration L ψF hψ i] at h'
    exact (L.fg_endFiltration (1 - i)).of_le h'
  exact traceDualLattice_inf_aux ψF (D ψF) (fun _ _ => Iff.rfl) (mem_additiveDual_iff_trace ψF hψ)
    ((L.fg_endFiltration j).of_le hj) ((L.fg_endFiltration l).of_le hl) (hFgd i hi) (hFgd k hk)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The recursive lattice is the relative order plus a term contained in the
ambient filtration at its cutoff. -/
theorem SimpleStratumLattice.Sequence.exists_lattice_eq_relative_sup {L : LatticeChain O F V}
    {n : ℤ} {b : A} {tail : List A} (hseq : SimpleStratumLattice.Sequence L n b tail)
    (i : SimpleStratumLattice.Kind) :
    ∃ W : Submodule O A, SimpleStratumLattice.lattice L n i b tail = Q L b 0 ⊔ W ∧
      W ≤ P L (SimpleStratumLattice.cutoff i (finiteCriticalDepth L n b)) := by
  cases hseq with
  | terminal hb hcrit =>
    have hf : finiteCriticalDepth L n b = n := by
      rcases hcrit with h | h <;> simp [finiteCriticalDepth, simpleCriticalDepth, h]
    rw [hf]
    cases i
    · exact ⟨P L (simpleHCutoff n), rfl, le_rfl⟩
    · exact ⟨P L (simpleJCutoff n), rfl, le_rfl⟩
  | step hb hr hrn hcrit hcrit' hsub next =>
    cases i
    · exact ⟨_, rfl, inf_le_right⟩
    · exact ⟨_, rfl, inf_le_right⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem adjointImage_simpleJLayer_eq_cutoff {L : LatticeChain O F V} {n : ℤ} {b : A} {tail : List A}
    (hseq : SimpleStratumLattice.Sequence L n b tail) {k : ℕ}
    (hk : (k : ℤ) ≤ simpleJCutoff (finiteCriticalDepth L n b)) :
    (simpleJLayer L n b tail k).map (adjointMap O b) =
      (simpleJLayer L n b tail (simpleJCutoff (finiteCriticalDepth L n b)).toNat).map (adjointMap O b) := by
  let j := simpleJCutoff (finiteCriticalDepth L n b)
  have hj : 0 ≤ j := (Int.natCast_nonneg k).trans hk
  obtain ⟨W, hW, hdeep⟩ := hseq.exists_lattice_eq_relative_sup .J
  change simpleJLattice L n b tail = Q L b 0 ⊔ W at hW
  have he : simpleJLayer L n b tail k = Q L b k ⊔ simpleJLayer L n b tail j.toNat := by
    simp only [simpleJLayer, hW, Int.toNat_of_nonneg hj]
    exact layer_eq_relative_sup_deep_of_le L b W (Int.natCast_nonneg k) hk hdeep
  have hzero : (Q L b k).map (adjointMap O b) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    rw [Submodule.mem_bot]
    exact hx.2
  rw [he, Submodule.map_sup, hzero, bot_sup_eq]

/-- At every nonnegative depth the H lattice lies between two ambient
filtration steps. -/
theorem SimpleStratumLattice.Sequence.simpleHLayer_bounds {L : LatticeChain O F V} {n : ℤ} {b : A}
    {tail : List A} (hseq : SimpleStratumLattice.Sequence L n b tail) (hn : 0 < n) (k : ℕ) :
    P L (max n (k : ℤ)) ≤ simpleHLayer L n b tail k ∧ simpleHLayer L n b tail k ≤ P L k :=
  ⟨le_inf ((L.endFiltration_antitone (le_max_left _ _)).trans (hseq.properties hn .H).full)
    (L.endFiltration_antitone (le_max_right _ _)), inf_le_right⟩

/-- The fractional transport of the adjoint lattice at the J cutoff lies in the J layer. -/
theorem SimpleStratumLattice.Sequence.mixed_le_simpleJLayer_cutoff {L : LatticeChain O F V}
    {n : ℤ} {b : A} {tail : List A} (hseq : SimpleStratumLattice.Sequence L n b tail) (hn : 0 < n)
    {r : ℕ} (hr : criticalExponent L b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    mixedAdjointLattice L b (((r + 1) / 2 : ℕ) : ℤ) (-(r : ℤ)) ≤
      simpleJLayer L n b tail ((r + 1) / 2) := by
  let j := (r + 1) / 2
  let J := simpleJLayer L n b tail j
  have ha := (hseq.properties hn .J).adjoint (r : ℤ) (by omega) hr.le (j : ℤ)
    (by change ((r : ℤ) + 1) / 2 ≤ (j : ℤ); dsimp [j]; omega)
  have hJN : J * adjointLattice L b (-(r : ℤ)) ≤ J := ha.2
  have hQ : Q L b j ≤ J :=
    le_inf ((inf_le_inf_right _ (L.endFiltration_antitone (Int.natCast_nonneg j))).trans
      (SimpleStratumLattice.centralizer_le_lattice L .J b tail)) inf_le_left
  have he := centralizerLattice_mul_mixedAdjointLattice L b hseq.parameter.inverse (j : ℤ) 0 (-(r : ℤ))
  simp only [mixedAdjointLattice_zero, add_zero] at he
  rw [← he]
  exact (mul_le_mul_left hQ _).trans hJN

private theorem traceDual_simpleHLayer_from_cutoff {L : LatticeChain O F V} {n : ℤ} {b : A}
    {tail : List A} (hseq : SimpleStratumLattice.Sequence L n b tail) (hn : 0 < n)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {r : ℕ}
    (hr : criticalExponent L b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hcut : D ψF (simpleHLayer L n b tail (r / 2 + 1)) =
      (simpleJLayer L n b tail ((r + 1) / 2)).map (adjointMap O b) ⊔ P L (-((r / 2 : ℕ) : ℤ)))
    (m : ℕ) : D ψF (simpleHLayer L n b tail (m + 1)) =
      (simpleJLayer L n b tail ((r + 1) / 2)).map (adjointMap O b) ⊔ P L (-(m : ℤ)) := by
  let j := (r + 1) / 2
  let J := simpleJLayer L n b tail j
  have hdepth : finiteCriticalDepth L n b = (r : ℤ) := by
    rw [finiteCriticalDepth, SimpleStratumLattice.simpleCriticalDepth_eq L hr, WithTop.untopD_coe]
  obtain ⟨W, hW, hw⟩ := hseq.exists_lattice_eq_relative_sup .H
  change simpleHLattice L n b tail = Q L b 0 ⊔ W at hW
  change W ≤ P L (simpleHCutoff (finiteCriticalDepth L n b)) at hw
  rw [hdepth, show simpleHCutoff (r : ℤ) = ((r / 2 + 1 : ℕ) : ℤ) by unfold simpleHCutoff; omega] at hw
  have hCrit (i : ℤ) (hi : -(r : ℤ) < i) : i ∉ criticalIndexSet L b := by
    have hb : elementAlgebra b ≠ ⊥ := by
      intro h
      rw [criticalExponent, ite_eq_left h] at hr
      exact WithBot.bot_ne_coe hr
    have hs : sSup (criticalIndexSet L b) = -(r : ℤ) := WithBot.coe_injective (by
      rwa [criticalExponent, ite_eq_right hb] at hr)
    intro hx
    have h := le_csSup (hseq.parameter.criticalSet.resolve_left hb).2 hx
    rw [hs] at h
    omega
  have hM : mixedAdjointLattice L b j (-(r : ℤ)) ≤ J := hseq.mixed_le_simpleJLayer_cutoff hn hr
  have hCover := inf_adjointRange_le_image_of_mixed_le L b (j : ℤ) (-(r : ℤ)) J hseq.parameter.inverse hCrit hM
  have hj : (j : ℤ) + -(r : ℤ) = -((r / 2 : ℕ) : ℤ) := by dsimp [j]; omega
  rw [hj] at hCover
  refine traceDual_simpleHLayer_of_cutoff L b n tail r m (D ψF) J W hW hw
    (traceDualLattice_sup ψF) ?_ ?_ ?_ hcut hCover
  · exact traceDualLattice_inf_of_bounds L ψF hψ
      ⟨_, _, (hseq.simpleHLayer_bounds hn _).1, (hseq.simpleHLayer_bounds hn _).2⟩ ⟨_, _, le_rfl, le_rfl⟩
  · rw [traceDualLattice_endFiltration L ψF hψ, show 1 - ((m + 1 : ℕ) : ℤ) = -(m : ℤ) by omega]
  · rw [traceDualLattice_centralizerLattice L ψF hψ, show 1 - ((m + 1 : ℕ) : ℤ) = -(m : ℤ) by omega]

/-- The trace dual of the character domain lattice is the adjoint image of
J at the cutoff plus the complementary ambient step. This is BK93 (3.1.19). -/
theorem SimpleStratumLattice.Sequence.traceDual_simpleHLayer {L : LatticeChain O F V} {n : ℤ} {b : A}
    {tail : List A} (hseq : SimpleStratumLattice.Sequence L n b tail) (hn : 0 < n)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (m : ℕ) :
    D ψF (simpleHLayer L n b tail (m + 1)) =
      (simpleJLayer L n b tail (simpleJCutoff (finiteCriticalDepth L n b)).toNat).map (adjointMap O b) ⊔
        P L (-(m : ℤ)) := by
  induction hseq generalizing m with
  | terminal hb hcrit =>
    rename_i b
    rcases hcrit with hr | hr
    · let r := n.toNat
      have hnr : (r : ℤ) = n := Int.toNat_of_nonneg hn.le
      have hr' : criticalExponent L b = ((-(r : ℤ) : ℤ) : WithBot ℤ) := hnr.symm ▸ hr
      have hj : (simpleJCutoff (finiteCriticalDepth L n b)).toNat = (r + 1) / 2 := by
        have hf : finiteCriticalDepth L n b = n := by simp [finiteCriticalDepth, simpleCriticalDepth, hr]
        rw [hf, ← hnr]; unfold simpleJCutoff; omega
      rw [hj]
      apply traceDual_simpleHLayer_from_cutoff (SimpleStratumLattice.Sequence.terminal hb (Or.inl hr)) hn ψF hψ hr' _ m
      have hH : simpleHLayer L n b [] (r / 2 + 1) = P L ((r / 2 + 1 : ℕ) : ℤ) := by
        unfold simpleHLayer simpleHLattice simpleStratumLattices
        refine inf_eq_right.mpr ?_
        exact (show simpleHCutoff n = ((r / 2 + 1 : ℕ) : ℤ) by rw [← hnr]; unfold simpleHCutoff; omega) ▸ le_sup_right
      have hJ : simpleJLayer L n b [] ((r + 1) / 2) = P L (((r + 1) / 2 : ℕ) : ℤ) := by
        unfold simpleJLayer simpleJLattice simpleStratumLattices
        refine inf_eq_right.mpr ?_
        exact (show simpleJCutoff n = (((r + 1) / 2 : ℕ) : ℤ) by rw [← hnr]; unfold simpleJCutoff; omega) ▸ le_sup_right
      rw [hH, hJ, traceDualLattice_endFiltration L ψF hψ,
        show 1 - ((r / 2 + 1 : ℕ) : ℤ) = -((r / 2 : ℕ) : ℤ) by omega]
      apply (sup_eq_right.mpr ?_).symm
      rintro _ ⟨x, hx, rfl⟩
      have h := commutator_mem_endFiltration L hb.mem hx
      rw [show -n + (((r + 1) / 2 : ℕ) : ℤ) = -((r / 2 : ℕ) : ℤ) by omega] at h
      exact h
    · let := L.finiteDimensional
      have hscalar := SimpleStratumLattice.scalar_of_criticalExponent_bot L hr
      have hz : adjointMap O b = 0 :=
        LinearMap.ext fun x => commute_of_elementAlgebra_eq_bot b hscalar x
      have hH : simpleHLayer L n b [] (m + 1) = P L ((m + 1 : ℕ) : ℤ) := by
        unfold simpleHLayer simpleHLattice simpleStratumLattices
        rw [SimpleStratumLattice.centralizer_eq_filtration L hr 0,
          sup_eq_left.mpr (L.endFiltration_antitone (by unfold simpleHCutoff; omega)),
          inf_eq_right.mpr (L.endFiltration_antitone (by omega))]
      rw [hH, hz, Submodule.map_zero, bot_sup_eq, traceDualLattice_endFiltration L ψF hψ]
      congr 1
      omega
  | step hb hr hrn hcrit hcrit' hsub next ih =>
    rename_i b c tail t
    let r := t.toNat
    have htr : (r : ℤ) = t := Int.toNat_of_nonneg hr.le
    have hcr : criticalExponent L b = ((-(r : ℤ) : ℤ) : WithBot ℤ) := htr.symm ▸ hcrit
    have hs := SimpleStratumLattice.Sequence.step hb hr hrn hcrit hcrit' hsub next
    have hj : (simpleJCutoff (finiteCriticalDepth L n b)).toNat = (r + 1) / 2 := by
      simp only [finiteCriticalDepth, simpleCriticalDepth, hcr, neg_neg, WithTop.untopD_coe]
      unfold simpleJCutoff
      omega
    rw [hj]
    apply traceDual_simpleHLayer_from_cutoff hs hn ψF hψ hcr _ m
    let j := (r + 1) / 2
    let d := r / 2
    have hH := hs.high_eq hn hcr .H (k := ((d + 1 : ℕ) : ℤ))
      (by change (r : ℤ) / 2 + 1 ≤ _; dsimp [d]; omega)
    have hJ := hs.high_eq hn hcr .J (k := (j : ℤ))
      (by change ((r : ℤ) + 1) / 2 ≤ _; dsimp [j]; omega)
    change simpleHLayer L n b (c :: tail) (d + 1) = simpleHLayer L n c tail (d + 1) at hH
    change simpleJLayer L n b (c :: tail) j = simpleJLayer L n c tail j at hJ
    have hb_c : b - c ∈ P L (-t) := by simpa only [neg_sub] using neg_mem hsub
    have hJadj := adjointMap_image_sup_eq_of_sub_mem L b c hb_c (simpleJLayer L n c tail j) inf_le_right
    have hjt : -t + (j : ℤ) = -(d : ℤ) := by dsimp [j, d]; omega
    rw [hjt] at hJadj
    have hle : (j : ℤ) ≤ simpleJCutoff (finiteCriticalDepth L n c) := by
      have hc : t ≤ finiteCriticalDepth L n c := by
        cases he : criticalExponent L c using WithBot.recBotCoe with
        | bot => simpa [finiteCriticalDepth, simpleCriticalDepth, he] using hrn.le
        | coe s =>
          rw [he, WithBot.coe_lt_coe] at hcrit'
          simp only [finiteCriticalDepth, simpleCriticalDepth, he, WithTop.untopD_coe]
          omega
      unfold simpleJCutoff
      dsimp [j]
      omega
    rw [hH, ih d, hJ, hJadj, adjointImage_simpleJLayer_eq_cutoff next hle]

end Langlands.BushnellKutzko
