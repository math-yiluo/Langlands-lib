import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.StratumEquivalenceProof

/-! # Adjoint preimages in the `𝔍` lattice of a simple stratum -/

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
private theorem finiteCriticalDepth_of_eq' (L : LatticeChain 𝒪[F] F V) (n d : ℤ) (b : A)
    (h : criticalExponent L b = ((-d : ℤ) : WithBot ℤ)) : finiteCriticalDepth L n b = d := by
  simp [finiteCriticalDepth, simpleCriticalDepth, h]

/-- Split an integral endomorphism whose commutator with `b` lies in `𝔓^{-k}` into a
centralizer element and a term at depth `d - k`, where `-d` is the critical exponent. -/
private theorem split_adjoint_neg (L : LatticeChain 𝒪[F] F V) {b : A}
    (hf : IsField (elementAlgebra b))
    (hu : letI := hf.toField
      ∀ a : (elementAlgebra b)ˣ, subfieldUnits F (elementAlgebra b) V a ∈ L.stabilizer)
    {d k : ℤ} (hkd : k ≤ d) (hc : criticalExponent L b = ((-d : ℤ) : WithBot ℤ))
    {x : A} (hx : x ∈ L.endFiltration 0) (ha : adjointMap 𝒪[F] b x ∈ L.endFiltration (-k)) :
    ∃ y ∈ centralizerLattice L b 0, ∃ z ∈ L.endFiltration (d - k),
      adjointMap 𝒪[F] b z = adjointMap 𝒪[F] b x ∧ y + z = x := by
  have := L.finiteDimensional
  obtain ⟨y, hy, hz⟩ := exists_commute_sub_mem L b hf hu (k := -d) hc.le (d - k) x (by
    have he : d - k + -d = -k := by ring
    rw [he]
    simpa only [adjointMap_apply] using ha)
  refine ⟨y, ⟨?_, hy⟩, x - y, hz, ?_, by abel⟩
  · have h := sub_mem hx (L.endFiltration_antitone (by omega : (0 : ℤ) ≤ d - k) hz)
    rwa [sub_sub_cancel] at h
  · rw [map_sub, show adjointMap 𝒪[F] b y = 0 from hy, sub_zero]

private theorem mem_simpleJLattice_of_adjoint_neg (L : LatticeChain 𝒪[F] F V) (n k : ℤ)
    (hk : 0 ≤ k) (hn : 2 * k ≤ n) {s : ℕ} (b : Fin (s + 1) → A)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hstep : ∀ i : Fin s, ∃ d : ℤ,
      criticalExponent L (b i.castSucc) = ((-d : ℤ) : WithBot ℤ) ∧
        b i.succ - b i.castSucc ∈ L.endFiltration (-d) ∧ 2 * k ≤ d)
    (hlast : criticalExponent L (b (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last s)) = ⊥)
    {x : A} (hx : x ∈ L.endFiltration 0)
    (ha : adjointMap 𝒪[F] (b 0) x ∈ L.endFiltration (-k)) :
    x ∈ simpleJLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) := by
  induction s generalizing x with
  | zero =>
    rw [List.ofFn_zero]
    change x ∈ centralizerLattice L (b 0) 0 ⊔ L.endFiltration (simpleJCutoff n)
    have h := hlast
    rw [Fin.last_zero] at h
    rcases h with hc | hc
    · obtain ⟨hf, hu⟩ := hfield 0
      obtain ⟨y, hy, z, hz, -, rfl⟩ := split_adjoint_neg L hf hu (by omega) hc hx ha
      exact Submodule.mem_sup.mpr
        ⟨y, hy, z, L.endFiltration_antitone (by unfold simpleJCutoff; omega) hz, rfl⟩
    · rw [centralizerLattice_zero_of_bot L hc]
      exact Submodule.mem_sup.mpr ⟨x, hx, 0, zero_mem _, add_zero _⟩
  | succ s ih =>
    rw [List.ofFn_succ]
    let i : Fin (s + 1) := 0
    let b' : Fin (s + 1) → A := fun j => b j.succ
    obtain ⟨d, hc, hdiff, hkd⟩ := hstep i
    change criticalExponent L (b 0) = ((-d : ℤ) : WithBot ℤ) at hc
    change b' 0 - b 0 ∈ L.endFiltration (-d) at hdiff
    obtain ⟨hf, hu⟩ := hfield 0
    obtain ⟨y, hy, z, hz, hza, rfl⟩ := split_adjoint_neg L hf hu (by omega) hc hx ha
    have hz0 : z ∈ L.endFiltration 0 := L.endFiltration_antitone (by omega) hz
    have hza' : adjointMap 𝒪[F] (b' 0) z ∈ L.endFiltration (-k) := by
      have he : adjointMap 𝒪[F] (b' 0) z =
          (b' 0 - b 0) * z - z * (b' 0 - b 0) + adjointMap 𝒪[F] (b 0) z := by
        simp only [adjointMap_apply]
        noncomm_ring
      have hsum : -d + (d - k) = -k := by ring
      have hsum' : d - k + -d = -k := by ring
      rw [he]
      refine add_mem (sub_mem ?_ ?_) (hza ▸ ha)
      · simpa only [hsum] using L.mul_mem_endFiltration hdiff hz
      · simpa only [hsum'] using L.mul_mem_endFiltration hz hdiff
    have hstep' : ∀ j : Fin s, ∃ d : ℤ,
        criticalExponent L (b' j.castSucc) = ((-d : ℤ) : WithBot ℤ) ∧
          b' j.succ - b' j.castSucc ∈ L.endFiltration (-d) ∧ 2 * k ≤ d := by
      intro j
      simpa only [b', Fin.castSucc_succ] using hstep j.succ
    have hlast' : criticalExponent L (b' (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
        elementAlgebra (b' (Fin.last s)) = ⊥ := by
      simpa only [b', Fin.succ_last] using hlast
    have hzJ := ih b' (fun j => hfield j.succ) hstep' hlast' hz0 hza'
    change y + z ∈ centralizerLattice L (b 0) 0 ⊔
      (simpleJLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
        L.endFiltration (simpleJCutoff (finiteCriticalDepth L n (b 0))))
    rw [finiteCriticalDepth_of_eq' L n d _ hc]
    exact Submodule.mem_sup.mpr
      ⟨y, hy, z, ⟨hzJ, L.endFiltration_antitone (by unfold simpleJCutoff; omega) hz⟩, rfl⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The terms of a defining sequence have critical depths at least that of the first
element. -/
private theorem definingSequence_depth_bounds {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) (i : Fin q.steps) :
    finiteCriticalDepth S.chain S.n S.b ≤ (q.terms i.succ).r := by
  obtain ⟨-, -, -, -, hmono, hstep, -, -⟩ := q.isDefiningSequence
  have hpos : 0 < q.steps := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let i₀ : Fin q.steps := ⟨0, hpos⟩
  have h₀ := (hstep i₀).1
  have hi₀ : i₀.castSucc = 0 := Fin.ext rfl
  rw [hi₀, q.firstElement] at h₀
  rw [finiteCriticalDepth_of_eq' S.chain S.n _ _ h₀]
  exact hmono.monotone (Fin.succ_le_succ_iff.mpr (show i₀ ≤ i from Nat.zero_le _))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The finite critical depth of the initial element is at most the level. -/
theorem finiteCriticalDepth_le_level {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) :
    finiteCriticalDepth S.chain S.n S.b ≤ S.n := by
  obtain ⟨-, hs, -, -, -, hstep, hlast, -⟩ := q.isDefiningSequence
  by_cases hpos : 0 < q.steps
  · let i₀ : Fin q.steps := ⟨0, hpos⟩
    have h₀ := (hstep i₀).1
    have hi₀ : i₀.castSucc = 0 := Fin.ext rfl
    rw [hi₀, q.firstElement] at h₀
    rw [finiteCriticalDepth_of_eq' S.chain S.n _ _ h₀]
    have h := (q.terms i₀.succ).r_lt_n
    rw [(hs i₀.succ).2.1] at h
    exact h.le
  · have hz : q.steps = 0 := by omega
    have hl : Fin.last q.steps = 0 := Fin.ext (by simp [hz])
    rw [hl, q.firstElement] at hlast
    rcases hlast with h | h
    · rw [finiteCriticalDepth_of_eq' S.chain S.n _ _ h]
    · simp [finiteCriticalDepth, simpleCriticalDepth, h]

/-- **Adjoint preimages in `𝔍`.** Let `r = finiteCriticalDepth L n β`, which is `−k₀(β,𝔄)`
for nonscalar `β` and the level `n` for scalar `β`. If `2k ≤ r`, every `x ∈ 𝔄` with
`βx − xβ ∈ 𝔓^{−k}` lies in the lattice `𝔍(β,𝔄)` computed from any defining sequence. -/
theorem adjointLattice_le_simpleJLattice (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (k : ℕ)
    (hk : 2 * (k : ℤ) ≤ finiteCriticalDepth S.chain S.n S.b) :
    adjointLattice S.chain S.b (-(k : ℤ)) ≤ simpleJLattice S.chain S.n S.b q.tail := by
  obtain ⟨-, hs, -, -, -, hstep, hlast, -⟩ := q.isDefiningSequence
  let b : Fin (q.steps + 1) → A := fun i => (q.terms i).b
  have hfield (i : Fin (q.steps + 1)) : ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ S.chain.stabilizer := by
    obtain ⟨hf, hu⟩ := (hs i).2.2.1.1
    let := hf.toField
    refine ⟨hf, fun a => ?_⟩
    rw [(normalizer F V S.chain).2.1, ← (hs i).1, ← (normalizer F V (q.terms i).chain).2.1]
    exact hu a
  have hlast' : criticalExponent S.chain (b (Fin.last q.steps)) = ((-S.n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last q.steps)) = ⊥ := by
    rcases hlast with h | h
    · exact Or.inl h
    · right
      by_contra hb
      apply hb
      simpa [criticalExponent] using h
  have hstep' : ∀ i : Fin q.steps, ∃ d : ℤ,
      criticalExponent S.chain (b i.castSucc) = ((-d : ℤ) : WithBot ℤ) ∧
        b i.succ - b i.castSucc ∈ S.chain.endFiltration (-d) ∧ 2 * (k : ℤ) ≤ d :=
    fun i => ⟨(q.terms i.succ).r, (hstep i).1, (hstep i).2,
      hk.trans (definingSequence_depth_bounds q i)⟩
  have hfirst : b 0 = S.b := q.firstElement
  have hn : 2 * (k : ℤ) ≤ S.n := hk.trans (finiteCriticalDepth_le_level q)
  intro x hx
  change x ∈ simpleJLattice S.chain S.n S.b (List.ofFn fun i : Fin q.steps => b i.succ)
  rw [← hfirst]
  have hx' : x ∈ adjointLattice S.chain (b 0) (-(k : ℤ)) := hfirst.symm ▸ hx
  exact mem_simpleJLattice_of_adjoint_neg S.chain S.n k (by positivity) hn b hfield hstep'
    hlast' hx'.1 hx'.2

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizerUnitGroup_eq_top_of_scalar' {b : A} (hb : elementAlgebra b = ⊥) :
    centralizerUnitGroup b = ⊤ := by
  apply top_unique
  intro g _
  have hb' : b ∈ (⊥ : Subalgebra F A) := hb ▸ Algebra.self_mem_adjoin_singleton F b
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hb'
  exact Algebra.commutes a (g : A)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem one_mem_simpleJLattice (L : LatticeChain 𝒪[F] F V) (n : ℤ) (b : A)
    (tail : List A) : (1 : A) ∈ simpleJLattice L n b tail := by
  have h : (1 : A) ∈ centralizerLattice L b 0 :=
    ⟨L.order.one_mem, by change b * 1 - 1 * b = 0; simp⟩
  cases tail <;> exact Submodule.mem_sup.mpr ⟨1, h, 0, zero_mem _, add_zero _⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizerLattice_le_simpleJLattice (L : LatticeChain 𝒪[F] F V) (n : ℤ) (b : A)
    (tail : List A) : centralizerLattice L b 0 ≤ simpleJLattice L n b tail := by
  intro x hx
  cases tail <;> exact Submodule.mem_sup.mpr ⟨x, hx, 0, zero_mem _, add_zero _⟩

/-- At depths with `2m ≤ r = finiteCriticalDepth L n β` (which is `−k₀(β,𝔄)`, as `β` is
nonscalar here), the outer factor of the self-intertwining formula of a
nonscalar simple character is the group `J^t`, `t = ⌊(r+1)/2⌋`: the product
`𝔔^{r−m} 𝔑_{−r}` lies in `𝔍^t` (the Remark after BK93 (3.3.2)). -/
theorem simpleCharacterIntertwiningFactor_eq_simpleJLayer (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (m : ℕ) (hb : elementAlgebra S.b ≠ ⊥)
    (hm : 2 * (m : ℤ) ≤ finiteCriticalDepth S.chain S.n S.b) :
    simpleCharacterIntertwiningFactor S q m =
      {g : G | (g : A) - 1 ∈ simpleJLayer S.chain S.n S.b q.tail
        (simpleJCutoff (finiteCriticalDepth S.chain S.n S.b)).toNat} := by
  set r := finiteCriticalDepth S.chain S.n S.b with hr
  have ht : ((simpleJCutoff r).toNat : ℤ) = simpleJCutoff r :=
    Int.toNat_of_nonneg (by unfold simpleJCutoff; omega)
  have hN : centralizerLattice S.chain S.b (r - m) * adjointLattice S.chain S.b (-r) ≤
      simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat := by
    apply Submodule.mul_le.mpr
    intro a ha z hz
    have haz : a * z ∈ S.chain.endFiltration (r - m) := by
      simpa using S.chain.mul_mem_endFiltration ha.1 hz.1
    refine ⟨adjointLattice_le_simpleJLattice S q m hm ⟨?_, ?_⟩, ?_⟩
    · exact S.chain.endFiltration_antitone (by omega) haz
    · change adjointMap 𝒪[F] S.b (a * z) ∈ S.chain.endFiltration (-(m : ℤ))
      have hka : adjointMap 𝒪[F] S.b (a * z) = a * adjointMap 𝒪[F] S.b z := by
        have hq : S.b * a - a * S.b = 0 := ha.2
        simp only [adjointMap_apply]
        rw [mul_sub, ← mul_assoc, ← mul_assoc, sub_eq_zero.mp hq, mul_assoc, mul_assoc]
      rw [hka]
      have hz' : adjointMap 𝒪[F] S.b z ∈ S.chain.endFiltration (-r) := hz.2
      have h := S.chain.mul_mem_endFiltration ha.1 hz'
      rwa [show r - (m : ℤ) + -r = -(m : ℤ) by ring] at h
    · exact S.chain.endFiltration_antitone (by rw [ht]; unfold simpleJCutoff; omega) haz
  unfold simpleCharacterIntertwiningFactor
  rw [ite_eq_right hb]
  change {g : G | (g : A) - 1 ∈ centralizerLattice S.chain S.b (r - m) *
    adjointLattice S.chain S.b (-r) ⊔ simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat} = _
  rw [sup_eq_right.mpr hN]

/-- **The group `J^m` from intertwining.** Let `[𝔄,n,0,β]` be simple, `1 ≤ m < n` and
`2m ≤ r = finiteCriticalDepth L n β`, which is `−k₀(β,𝔄)` for nonscalar `β` and `n` for
scalar `β`. For every `χ ∈ C(𝔄,m,β)`, the group `J^m(β,𝔄)` is the set of elements of
`U^m(𝔄)` that intertwine `χ`. This uses the exact carriers and product formula of
`SimpleStratumGroupPropertiesStatement` and the intertwining formula of
`SimpleCharacterIntertwiningStatement`. -/
theorem simpleJGroup_eq_selfIntertwining_inter
    (hgroups : SimpleStratumGroupPropertiesStatement.{u, v})
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (m : ℕ) (hm1 : 1 ≤ m) (hmn : (m : ℤ) < S.n)
    (hm : 2 * (m : ℤ) ≤ finiteCriticalDepth S.chain S.n S.b)
    (χ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ)
    (hχ : χ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m) :
    (simpleJGroup S.chain S.n S.b q.tail m : Set G) =
      characterSelfIntertwining χ ∩ (S.chain.unitFiltration m : Set G) := by
  classical
  set r := finiteCriticalDepth S.chain S.n S.b with hr
  let J := simpleJGroup S.chain S.n S.b q.tail
  let B := centralizerUnitGroup S.b
  have hcrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
    cases hd : simpleCriticalDepth S.chain S.b with
    | top => exact WithTop.coe_lt_top _
    | coe d =>
      have hrd : r = d := by simp [hr, finiteCriticalDepth, hd]
      exact WithTop.coe_lt_coe.mpr (by omega)
  have hI := (hint F V ψF hψ S h0 hs q m hmn hcrit χ hχ).1
  have hg := hgroups F V S h0 hs q
  have hJcar (k : ℕ) : (J k : Set G) = simpleJCarrier S.chain S.n S.b q.tail k := (hg.1 k).2
  by_cases hb : elementAlgebra S.b = ⊥
  · have hY : simpleCharacterIntertwiningFactor S q m = {1} := by
      unfold simpleCharacterIntertwiningFactor
      rw [ite_eq_left hb]
    rw [hI, hY, Set.singleton_one, one_mul, mul_one, centralizerUnitGroup_eq_top_of_scalar' hb,
      Subgroup.coe_top, Set.univ_inter, hJcar m]
    ext g
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    apply centralizerLattice_le_simpleJLattice
    rw [centralizerLattice_zero_of_bot S.chain hb]
    exact (S.chain.mem_order_iff_mem_endFiltration).1 h.1
  · set t := (simpleJCutoff r).toNat with htdef
    have ht : (t : ℤ) = simpleJCutoff r := Int.toNat_of_nonneg (by unfold simpleJCutoff; omega)
    have ht1 : 1 ≤ t := by unfold simpleJCutoff at ht; omega
    have hmt : m ≤ t := by unfold simpleJCutoff at ht; omega
    have hY : simpleCharacterIntertwiningFactor S q m = (J t : Set G) := by
      rw [simpleCharacterIntertwiningFactor_eq_simpleJLayer S q m hb hm, hJcar t]
      ext g
      constructor
      · intro hx
        obtain ⟨a, ha, hval⟩ := S.chain.exists_mem_unitFiltration ht1 hx.2
        have heq : a = g := Units.ext (by rw [hval]; abel)
        exact ⟨heq ▸ ha, by simpa using add_mem hx.1 (one_mem_simpleJLattice S.chain S.n S.b q.tail)⟩
      · intro hx
        exact ⟨sub_mem hx.2 (one_mem_simpleJLattice S.chain S.n S.b q.tail), hx.1.2.2⟩
    have hprod : (J m : Set G) = (relativeUnitFiltration S.chain S.b m : Set G) * (J t : Set G) :=
      (hg.2.1 hb).2 m (by rw [← ht]; exact_mod_cast hmt)
    have hJt : J t ≤ S.chain.unitFiltration m :=
      (simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail t).trans
        (S.chain.unitFiltration_antitone hmt)
    rw [hI, hY]
    apply le_antisymm
    · intro g hgJ
      refine ⟨?_, simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail m hgJ⟩
      rw [hprod] at hgJ
      obtain ⟨u, hu, j, hj, rfl⟩ := Set.mem_mul.mp hgJ
      exact Set.mem_mul.mpr ⟨1 * u, Set.mem_mul.mpr ⟨1, (J t).one_mem, u, hu.1, rfl⟩, j, hj, rfl⟩
    · rintro g ⟨hg', hgU⟩
      obtain ⟨a, ha, y₂, hy₂, rfl⟩ := Set.mem_mul.mp hg'
      obtain ⟨y₁, hy₁, b, hbB, rfl⟩ := Set.mem_mul.mp ha
      have hbU : b ∈ S.chain.unitFiltration m := by
        have h := (S.chain.unitFiltration m).mul_mem
          ((S.chain.unitFiltration m).mul_mem ((S.chain.unitFiltration m).inv_mem (hJt hy₁)) hgU)
          ((S.chain.unitFiltration m).inv_mem (hJt hy₂))
        simpa [mul_assoc] using h
      have hbK : b ∈ relativeOrderNormalizer S.chain S.b :=
        ⟨hbB, ((normalizer F V S.chain).1 m).1 hbU⟩
      have hnorm := ((hg.2.2.1 t).2 ((relativeOrderNormalizer S.chain S.b).inv_mem hbK))
      have hy₁' : b⁻¹ * y₁ * b ∈ J t := by
        have h := (Subgroup.mem_normalizer_iff.mp hnorm y₁).mp hy₁
        simpa using h
      rw [hprod]
      exact Set.mem_mul.mpr ⟨b, ⟨hbB, hbU⟩, (b⁻¹ * y₁ * b) * y₂, (J t).mul_mem hy₁' hy₂,
        by group⟩

end Langlands.BushnellKutzko
