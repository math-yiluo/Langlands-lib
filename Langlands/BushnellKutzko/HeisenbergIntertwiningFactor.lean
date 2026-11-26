import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.StratumEquivalenceProof

/-! # The level-zero simple character double coset -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

open StratumEquivalence

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finiteCriticalDepth_of_eq (L : LatticeChain 𝒪[F] F V) (n d : ℤ) (b : A)
    (h : criticalExponent L b = ((-d : ℤ) : WithBot ℤ)) : finiteCriticalDepth L n b = d := by
  simp [finiteCriticalDepth, simpleCriticalDepth, h]

private theorem split_integral_commutator (L : LatticeChain 𝒪[F] F V) {b : A}
    (hf : IsField (elementAlgebra b))
    (hu : letI := hf.toField
      ∀ a : (elementAlgebra b)ˣ, subfieldUnits F (elementAlgebra b) V a ∈ L.stabilizer)
    {d : ℤ} (hd : 0 < d) (hc : criticalExponent L b = ((-d : ℤ) : WithBot ℤ))
    {x : A} (hx : x ∈ L.endFiltration 0) (ha : adjointMap 𝒪[F] b x ∈ L.endFiltration 0) :
    ∃ y ∈ centralizerLattice L b 0, ∃ z ∈ L.endFiltration d,
      adjointMap 𝒪[F] b z = adjointMap 𝒪[F] b x ∧ y + z = x := by
  have := L.finiteDimensional
  obtain ⟨y, hy, hz⟩ := exists_commute_sub_mem L b hf hu (k := -d) hc.le d x (by
    simpa only [add_neg_cancel, adjointMap_apply] using ha)
  refine ⟨y, ⟨?_, hy⟩, x - y, hz, ?_, by abel⟩
  · have h := sub_mem hx (L.endFiltration_antitone hd.le hz)
    rwa [sub_sub_cancel] at h
  · rw [map_sub, show adjointMap 𝒪[F] b y = 0 from hy, sub_zero]

private theorem mem_simpleJLattice_of_adjoint (L : LatticeChain 𝒪[F] F V) (n : ℤ) (hn : 0 < n)
    {s : ℕ} (b : Fin (s + 1) → A)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hnegative : ∀ i, criticalExponent L (b i) < (0 : WithBot ℤ))
    (hstep : ∀ i : Fin s, ∃ d : ℤ,
      criticalExponent L (b i.castSucc) = ((-d : ℤ) : WithBot ℤ) ∧
        b i.succ - b i.castSucc ∈ L.endFiltration (-d))
    (hlast : criticalExponent L (b (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last s)) = ⊥)
    {x : A} (hx : x ∈ L.endFiltration 0) (ha : adjointMap 𝒪[F] (b 0) x ∈ L.endFiltration 0) :
    x ∈ simpleJLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) := by
  induction s generalizing x with
  | zero =>
    rw [List.ofFn_zero]
    change x ∈ centralizerLattice L (b 0) 0 ⊔ L.endFiltration (simpleJCutoff n)
    have h := hlast
    rw [Fin.last_zero] at h
    rcases h with hc | hc
    · obtain ⟨hf, hu⟩ := hfield 0
      obtain ⟨y, hy, z, hz, -, rfl⟩ := split_integral_commutator L hf hu hn hc hx ha
      exact Submodule.mem_sup.mpr
        ⟨y, hy, z, L.endFiltration_antitone (by unfold simpleJCutoff; omega) hz, rfl⟩
    · rw [centralizerLattice_zero_of_bot L hc]
      exact Submodule.mem_sup.mpr ⟨x, hx, 0, zero_mem _, add_zero _⟩
  | succ s ih =>
    rw [List.ofFn_succ]
    let i : Fin (s + 1) := 0
    let b' : Fin (s + 1) → A := fun j => b j.succ
    obtain ⟨d, hc, hdiff⟩ := hstep i
    change criticalExponent L (b 0) = ((-d : ℤ) : WithBot ℤ) at hc
    change b' 0 - b 0 ∈ L.endFiltration (-d) at hdiff
    have hd : 0 < d := by
      have h := hnegative 0
      rw [hc] at h
      have : -d < (0 : ℤ) := WithBot.coe_lt_coe.mp h
      omega
    obtain ⟨hf, hu⟩ := hfield 0
    obtain ⟨y, hy, z, hz, hza, rfl⟩ := split_integral_commutator L hf hu hd hc hx ha
    have hz0 : z ∈ L.endFiltration 0 := L.endFiltration_antitone hd.le hz
    have hza' : adjointMap 𝒪[F] (b' 0) z ∈ L.endFiltration 0 := by
      have he : adjointMap 𝒪[F] (b' 0) z =
          (b' 0 - b 0) * z - z * (b' 0 - b 0) + adjointMap 𝒪[F] (b 0) z := by
        simp only [adjointMap_apply]
        noncomm_ring
      rw [he]
      refine add_mem (sub_mem ?_ ?_) (hza ▸ ha)
      · simpa using L.mul_mem_endFiltration hdiff hz
      · simpa using L.mul_mem_endFiltration hz hdiff
    have hstep' : ∀ j : Fin s, ∃ d : ℤ,
        criticalExponent L (b' j.castSucc) = ((-d : ℤ) : WithBot ℤ) ∧
          b' j.succ - b' j.castSucc ∈ L.endFiltration (-d) := by
      intro j
      simpa only [b', Fin.castSucc_succ] using hstep j.succ
    have hlast' : criticalExponent L (b' (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
        elementAlgebra (b' (Fin.last s)) = ⊥ := by
      simpa only [b', Fin.succ_last] using hlast
    have hzJ := ih b' (fun j => hfield j.succ) (fun j => hnegative j.succ) hstep' hlast' hz0 hza'
    change y + z ∈ centralizerLattice L (b 0) 0 ⊔
      (simpleJLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
        L.endFiltration (simpleJCutoff (finiteCriticalDepth L n (b 0))))
    rw [finiteCriticalDepth_of_eq L n d _ hc]
    exact Submodule.mem_sup.mpr
      ⟨y, hy, z, ⟨hzJ, L.endFiltration_antitone (by unfold simpleJCutoff; omega) hz⟩, rfl⟩

private theorem adjointLattice_zero_le_simpleJLattice (S : Stratum 𝒪[F] F V)
    (h0 : S.r = 0) (q : S.DefiningSequenceChoice) :
    adjointLattice S.chain S.b 0 ≤ simpleJLattice S.chain S.n S.b q.tail := by
  obtain ⟨-, hs, -, hr, hmono, hstep, hlast, -⟩ := q.isDefiningSequence
  let b : Fin (q.steps + 1) → A := fun i => (q.terms i).b
  have hfield (i : Fin (q.steps + 1)) : ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ S.chain.stabilizer := by
    obtain ⟨hf, hu⟩ := (hs i).2.2.1.1
    let := hf.toField
    refine ⟨hf, fun a => ?_⟩
    rw [(normalizer F V S.chain).2.1, ← (hs i).1, ← (normalizer F V (q.terms i).chain).2.1]
    exact hu a
  have hnegative (i : Fin (q.steps + 1)) : criticalExponent S.chain (b i) < (0 : WithBot ℤ) := by
    have hP : (q.terms i).chain.endFiltration = S.chain.endFiltration :=
      StratumEquivalence.endFiltration_eq_of_eq (by
        rw [← (q.terms i).chain.toSubmodule_order, ← S.chain.toSubmodule_order, (hs i).1])
    rw [← StratumEquivalence.criticalExponent_congr hP]
    have hi := (hs i).2.2.2
    have hr' : 0 ≤ (q.terms i).r := by simpa [hr, h0] using hmono.monotone (Fin.zero_le i)
    exact hi.trans_le (by exact_mod_cast (show -(q.terms i).r ≤ (0 : ℤ) by omega))
  have hlast' : criticalExponent S.chain (b (Fin.last q.steps)) = ((-S.n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last q.steps)) = ⊥ := by
    rcases hlast with h | h
    · exact Or.inl h
    · right
      by_contra hb
      apply hb
      simpa [criticalExponent] using h
  have hfirst : b 0 = S.b := q.firstElement
  have hn : 0 < S.n := by simpa [h0] using S.r_lt_n
  intro x hx
  change x ∈ simpleJLattice S.chain S.n S.b (List.ofFn fun i : Fin q.steps => b i.succ)
  rw [← hfirst]
  have hx' : x ∈ adjointLattice S.chain (b 0) 0 := hfirst.symm ▸ hx
  exact mem_simpleJLattice_of_adjoint S.chain S.n hn b hfield hnegative
    (fun i => ⟨(q.terms i.succ).r, hstep i⟩) hlast' hx'.1 hx'.2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizerUnitGroup_eq_top_of_scalar {b : A} (hb : elementAlgebra b = ⊥) :
    centralizerUnitGroup b = ⊤ := by
  apply top_unique
  intro g _
  have hb' : b ∈ (⊥ : Subalgebra F A) := hb ▸ Algebra.self_mem_adjoin_singleton F b
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hb'
  exact Algebra.commutes a (g : A)

/-- At level zero the character intertwining factor gives the double coset of `J^1`. -/
theorem simpleCharacterIntertwiningFactor_mul_centralizer_zero
    (hgroups : SimpleStratumGroupPropertiesStatement.{u, v}) (S : Stratum 𝒪[F] F V)
    (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice) :
    let J := simpleJGroup S.chain S.n S.b q.tail 1
    let Y := simpleCharacterIntertwiningFactor S q 0
    let B := centralizerUnitGroup S.b
    (Y * (B : Set G)) * Y = ((J : Set G) * (B : Set G)) * (J : Set G) := by
  classical
  dsimp only
  let J := simpleJGroup S.chain S.n S.b q.tail
  let B := centralizerUnitGroup S.b
  by_cases hb : elementAlgebra S.b = ⊥
  · rw [simpleCharacterIntertwiningFactor, ite_eq_left hb, Set.singleton_one, one_mul, mul_one]
    apply le_antisymm
    · intro g hg
      exact Set.mem_mul.mpr ⟨1 * g, Set.mem_mul.mpr ⟨1, (J 1).one_mem, g, hg, rfl⟩,
        1, (J 1).one_mem, by simp⟩
    · rw [centralizerUnitGroup_eq_top_of_scalar hb, Subgroup.coe_top]
      exact Set.subset_univ _
  · let d := finiteCriticalDepth S.chain S.n S.b
    let c := (simpleJCutoff d).toNat
    have hce : criticalExponent S.chain S.b = ((-d : ℤ) : WithBot ℤ) := by
      have he : criticalExponent S.chain S.b = ((sSup (criticalIndexSet S.chain S.b) : ℤ) : WithBot ℤ) := by
        unfold criticalExponent
        exact ite_eq_right hb
      have hd' : d = -sSup (criticalIndexSet S.chain S.b) :=
        finiteCriticalDepth_of_eq S.chain S.n _ _ (by simpa using he)
      simpa [hd'] using he
    have hd : 0 < d := by
      have h := hs.2
      rw [h0, neg_zero, hce] at h
      have : -d < (0 : ℤ) := WithBot.coe_lt_coe.mp h
      omega
    have hcut : 1 ≤ simpleJCutoff d := by unfold simpleJCutoff; omega
    have hc : (c : ℤ) = simpleJCutoff d := Int.toNat_of_nonneg (by omega)
    have hc1 : 1 ≤ c := by omega
    have hcd : (c : ℤ) ≤ d := by rw [hc]; unfold simpleJCutoff; omega
    have hN : centralizerLattice S.chain S.b d * adjointLattice S.chain S.b (-d) ≤
        simpleJLayer S.chain S.n S.b q.tail c := by
      apply Submodule.mul_le.mpr
      intro a ha z hz
      refine ⟨adjointLattice_zero_le_simpleJLattice S h0 q ⟨?_, ?_⟩, ?_⟩
      · exact S.chain.endFiltration_antitone (by omega) (S.chain.mul_mem_endFiltration ha.1 hz.1)
      · change adjointMap F S.b (a * z) ∈ S.chain.endFiltration 0
        rw [adjointMap_mul_left_of_ker S.b ha.2]
        have hz' : adjointMap F S.b z ∈ S.chain.endFiltration (-d) := hz.2
        simpa using S.chain.mul_mem_endFiltration ha.1 hz'
      · exact S.chain.endFiltration_antitone (by omega) (S.chain.mul_mem_endFiltration ha.1 hz.1)
    have hg := hgroups F V S h0 hs q
    have hone : (1 : A) ∈ simpleJLattice S.chain S.n S.b q.tail := by
      have h : (1 : A) ∈ centralizerLattice S.chain S.b 0 :=
        ⟨S.chain.order.one_mem, by change S.b * 1 - 1 * S.b = 0; simp⟩
      generalize q.tail = tail
      cases tail <;> exact Submodule.mem_sup.mpr ⟨1, h, 0, zero_mem _, add_zero _⟩
    have hy : simpleCharacterIntertwiningFactor S q 0 = (J c : Set G) := by
      unfold simpleCharacterIntertwiningFactor
      rw [ite_eq_right hb]
      simp only [Nat.cast_zero, sub_zero]
      change {g : G | (g : A) - 1 ∈ centralizerLattice S.chain S.b d *
        adjointLattice S.chain S.b (-d) ⊔ simpleJLayer S.chain S.n S.b q.tail c} = (J c : Set G)
      rw [sup_eq_right.mpr hN]
      ext g
      change ((g : A) - 1 ∈ simpleJLayer S.chain S.n S.b q.tail c) ↔ g ∈ J c
      constructor
      · intro hx
        obtain ⟨a, ha, hval⟩ := S.chain.exists_mem_unitFiltration hc1 hx.2
        have heq : a = g := Units.ext (by rw [hval]; abel)
        apply Subgroup.subset_closure
        exact ⟨heq ▸ ha, by simpa using add_mem hx.1 hone⟩
      · intro hx
        have hx' : g ∈ simpleJCarrier S.chain S.n S.b q.tail c := by
          rw [← (hg.1 c).2]
          exact hx
        exact ⟨sub_mem hx'.2 hone, hx'.1.2.2⟩
    have hJ : (J 1 : Set G) = (relativeUnitFiltration S.chain S.b 1 : Set G) * (J c : Set G) :=
      (hg.2.1 hb).2 1 (by exact hcut)
    rw [hy]
    apply le_antisymm
    · have hj : (J c : Set G) ⊆ J 1 := simpleJGroup_antitone S.chain S.n S.b q.tail hc1
      exact Set.mul_subset_mul (Set.mul_subset_mul hj subset_rfl) hj
    · rintro g hg'
      obtain ⟨a, ha, j₂, hj₂, rfl⟩ := Set.mem_mul.mp hg'
      obtain ⟨j₁, hj₁, b, hb', rfl⟩ := Set.mem_mul.mp ha
      obtain ⟨u₂, hu₂, y₂, hy₂, he₂⟩ := Set.mem_mul.mp (hJ ▸ hj₂)
      have hj₁' : j₁⁻¹ ∈ (J 1 : Set G) := (J 1).inv_mem hj₁
      obtain ⟨u₁, hu₁, y₁, hy₁, he₁⟩ := Set.mem_mul.mp (hJ ▸ hj₁')
      have he : j₁ = y₁⁻¹ * u₁⁻¹ := by rw [← mul_inv_rev, he₁, inv_inv]
      exact Set.mem_mul.mpr ⟨y₁⁻¹ * (u₁⁻¹ * b * u₂), Set.mem_mul.mpr
        ⟨y₁⁻¹, (J c).inv_mem hy₁, u₁⁻¹ * b * u₂,
          B.mul_mem (B.mul_mem (B.inv_mem hu₁.1) hb') hu₂.1, rfl⟩,
        y₂, hy₂, by rw [he, ← he₂]; group⟩

end Langlands.BushnellKutzko
