import Langlands.BushnellKutzko.SimpleCharacterLoweringLattice

/-! # Adjoint lattices acting on the `ℌ` and `𝔍` lattices of a simple stratum -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

open StratumEquivalence

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finiteCriticalDepth_of_eq'' (L : LatticeChain 𝒪[F] F V) (n d : ℤ) (b : A)
    (h : criticalExponent L b = ((-d : ℤ) : WithBot ℤ)) : finiteCriticalDepth L n b = d := by
  simp [finiteCriticalDepth, simpleCriticalDepth, h]

/-- Splitting at the critical exponent `−d`: an integral `x` with `[b,x] ∈ 𝔓^{−k}` is a
centralizer element plus a term at depth `d − k` with the same commutator. -/
private theorem split_adjoint (L : LatticeChain 𝒪[F] F V) {b : A}
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

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The commutator with the next term of a defining sequence. -/
private theorem adjoint_next_mem (L : LatticeChain 𝒪[F] F V) {b b' x : A} {d e k : ℤ}
    (hdiff : b' - b ∈ L.endFiltration (-d)) (hx : x ∈ L.endFiltration e)
    (hax : adjointMap 𝒪[F] b x ∈ L.endFiltration k) (hk : k ≤ -d + e) :
    adjointMap 𝒪[F] b' x ∈ L.endFiltration k := by
  have he : adjointMap 𝒪[F] b' x = (b' - b) * x - x * (b' - b) + adjointMap 𝒪[F] b x := by
    simp only [adjointMap_apply]
    noncomm_ring
  rw [he]
  refine add_mem (sub_mem ?_ ?_) hax
  · exact L.endFiltration_antitone hk (L.mul_mem_endFiltration hdiff hx)
  · exact L.endFiltration_antitone (by omega) (L.mul_mem_endFiltration hx hdiff)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Commutators with an element of the centralizer move the left factor. -/
private theorem adjoint_mul_right_of_ker (b : A) {x c : A} (hc : b * c - c * b = 0) :
    adjointMap 𝒪[F] b (x * c) = adjointMap 𝒪[F] b x * c := by
  have h : c * b = b * c := (sub_eq_zero.mp hc).symm
  simp only [adjointMap_apply, sub_mul, mul_assoc, h]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem adjoint_mul_left_of_ker (b : A) {x c : A} (hc : b * c - c * b = 0) :
    adjointMap 𝒪[F] b (c * x) = c * adjointMap 𝒪[F] b x := by
  simp only [adjointMap_apply]
  rw [mul_sub, ← mul_assoc, sub_eq_zero.mp hc, mul_assoc, mul_assoc]

/-! ### Recursions along a sequence `b 0, …, b s` with depths `d 0, …, d (s−1)` -/

/-- `x ∈ 𝔄` with `[b 0, x] ∈ 𝔓^{−k}` lies in `ℌ` when `2k` is below all depths and `n`. -/
private theorem mem_simpleHLattice_of_adjoint (L : LatticeChain 𝒪[F] F V) (n k : ℤ)
    (hk : 0 ≤ k) (hn : 2 * k < n) {s : ℕ} (b : Fin (s + 1) → A) (d : Fin s → ℤ)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hstep : ∀ i : Fin s, criticalExponent L (b i.castSucc) = ((-d i : ℤ) : WithBot ℤ) ∧
      b i.succ - b i.castSucc ∈ L.endFiltration (-d i))
    (hd : ∀ i, 2 * k < d i)
    (hlast : criticalExponent L (b (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last s)) = ⊥)
    {x : A} (hx : x ∈ L.endFiltration 0)
    (ha : adjointMap 𝒪[F] (b 0) x ∈ L.endFiltration (-k)) :
    x ∈ simpleHLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) := by
  induction s generalizing x with
  | zero =>
    rw [List.ofFn_zero]
    change x ∈ centralizerLattice L (b 0) 0 ⊔ L.endFiltration (simpleHCutoff n)
    have h := hlast
    rw [Fin.last_zero] at h
    rcases h with hc | hc
    · obtain ⟨hf, hu⟩ := hfield 0
      obtain ⟨y, hy, z, hz, -, rfl⟩ := split_adjoint L hf hu (by omega) hc hx ha
      exact Submodule.mem_sup.mpr
        ⟨y, hy, z, L.endFiltration_antitone (by unfold simpleHCutoff; omega) hz, rfl⟩
    · rw [centralizerLattice_zero_of_bot L hc]
      exact Submodule.mem_sup.mpr ⟨x, hx, 0, zero_mem _, add_zero _⟩
  | succ s ih =>
    rw [List.ofFn_succ]
    let b' : Fin (s + 1) → A := fun j => b j.succ
    obtain ⟨hc, hdiff⟩ := hstep 0
    change criticalExponent L (b 0) = ((-d 0 : ℤ) : WithBot ℤ) at hc
    change b' 0 - b 0 ∈ L.endFiltration (-d 0) at hdiff
    have hk0 := hd 0
    obtain ⟨hf, hu⟩ := hfield 0
    obtain ⟨y, hy, z, hz, hza, rfl⟩ := split_adjoint L hf hu (by omega) hc hx ha
    have hz0 : z ∈ L.endFiltration 0 := L.endFiltration_antitone (by omega) hz
    have hza' : adjointMap 𝒪[F] (b' 0) z ∈ L.endFiltration (-k) :=
      adjoint_next_mem L hdiff hz (by rw [hza]; exact ha) (by omega)
    have hzH := ih b' (fun j => d j.succ) (fun j => hfield j.succ)
      (fun j => by simpa only [b', Fin.succ_castSucc] using hstep j.succ)
      (fun j => hd j.succ) (by simpa only [b', Fin.succ_last] using hlast) hz0 hza'
    change y + z ∈ centralizerLattice L (b 0) 0 ⊔
      (simpleHLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
        L.endFiltration (simpleHCutoff (finiteCriticalDepth L n (b 0))))
    rw [finiteCriticalDepth_of_eq'' L n (d 0) _ hc]
    exact Submodule.mem_sup.mpr
      ⟨y, hy, z, ⟨hzH, L.endFiltration_antitone (by unfold simpleHCutoff; omega) hz⟩, rfl⟩

/-- `x ∈ 𝔄` with `[b 0, x] ∈ 𝔓^{−k}` lies in `𝔍` when `2k` is at most all depths and `n`. -/
private theorem mem_simpleJLattice_of_adjoint (L : LatticeChain 𝒪[F] F V) (n k : ℤ)
    (hk : 0 ≤ k) (hn : 2 * k ≤ n) {s : ℕ} (b : Fin (s + 1) → A) (d : Fin s → ℤ)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hstep : ∀ i : Fin s, criticalExponent L (b i.castSucc) = ((-d i : ℤ) : WithBot ℤ) ∧
      b i.succ - b i.castSucc ∈ L.endFiltration (-d i))
    (hd : ∀ i, 2 * k ≤ d i)
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
      obtain ⟨y, hy, z, hz, -, rfl⟩ := split_adjoint L hf hu (by omega) hc hx ha
      exact Submodule.mem_sup.mpr
        ⟨y, hy, z, L.endFiltration_antitone (by unfold simpleJCutoff; omega) hz, rfl⟩
    · rw [centralizerLattice_zero_of_bot L hc]
      exact Submodule.mem_sup.mpr ⟨x, hx, 0, zero_mem _, add_zero _⟩
  | succ s ih =>
    rw [List.ofFn_succ]
    let b' : Fin (s + 1) → A := fun j => b j.succ
    obtain ⟨hc, hdiff⟩ := hstep 0
    change criticalExponent L (b 0) = ((-d 0 : ℤ) : WithBot ℤ) at hc
    change b' 0 - b 0 ∈ L.endFiltration (-d 0) at hdiff
    have hk0 := hd 0
    obtain ⟨hf, hu⟩ := hfield 0
    obtain ⟨y, hy, z, hz, hza, rfl⟩ := split_adjoint L hf hu (by omega) hc hx ha
    have hz0 : z ∈ L.endFiltration 0 := L.endFiltration_antitone (by omega) hz
    have hza' : adjointMap 𝒪[F] (b' 0) z ∈ L.endFiltration (-k) :=
      adjoint_next_mem L hdiff hz (by rw [hza]; exact ha) (by omega)
    have hzJ := ih b' (fun j => d j.succ) (fun j => hfield j.succ)
      (fun j => by simpa only [b', Fin.succ_castSucc] using hstep j.succ)
      (fun j => hd j.succ) (by simpa only [b', Fin.succ_last] using hlast) hz0 hza'
    change y + z ∈ centralizerLattice L (b 0) 0 ⊔
      (simpleJLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
        L.endFiltration (simpleJCutoff (finiteCriticalDepth L n (b 0))))
    rw [finiteCriticalDepth_of_eq'' L n (d 0) _ hc]
    exact Submodule.mem_sup.mpr
      ⟨y, hy, z, ⟨hzJ, L.endFiltration_antitone (by unfold simpleJCutoff; omega) hz⟩, rfl⟩

/-- Products of `y ∈ 𝔑_{−k}(b 0)` with centralizer elements of `𝔓^{⌊k/2⌋+1}` lie in `ℌ`. -/
private theorem centralizer_mul_mem_simpleHLattice (L : LatticeChain 𝒪[F] F V) (n : ℤ) {s : ℕ}
    (b : Fin (s + 1) → A) (d : Fin s → ℤ)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hstep : ∀ i : Fin s, criticalExponent L (b i.castSucc) = ((-d i : ℤ) : WithBot ℤ) ∧
      b i.succ - b i.castSucc ∈ L.endFiltration (-d i))
    (hlast : criticalExponent L (b (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last s)) = ⊥)
    (k : ℤ) (hk : 0 ≤ k) (hkd : ∀ i, k < d i) (hkn : k < n)
    {y c : A} (hy : y ∈ L.endFiltration 0)
    (hya : adjointMap 𝒪[F] (b 0) y ∈ L.endFiltration (-k))
    (hc : c ∈ centralizerLattice L (b 0) 0) (hck : c ∈ L.endFiltration (k / 2 + 1)) :
    y * c ∈ simpleHLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) ∧
      c * y ∈ simpleHLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) := by
  have hc' : b 0 * c - c * b 0 = 0 := hc.2
  have hd' : ∀ i, 2 * (k / 2) < d i := fun i => by have := hkd i; omega
  have hn' : 2 * (k / 2) < n := by omega
  constructor
  · refine mem_simpleHLattice_of_adjoint L n (k / 2) (by omega) hn' b d hfield hstep hd' hlast
      (by simpa using L.mul_mem_endFiltration hy hc.1) ?_
    rw [adjoint_mul_right_of_ker (b 0) hc']
    exact L.endFiltration_antitone (by omega) (L.mul_mem_endFiltration hya hck)
  · refine mem_simpleHLattice_of_adjoint L n (k / 2) (by omega) hn' b d hfield hstep hd' hlast
      (by simpa using L.mul_mem_endFiltration hc.1 hy) ?_
    rw [adjoint_mul_left_of_ker (b 0) hc']
    exact L.endFiltration_antitone (by omega) (L.mul_mem_endFiltration hck hya)

/-- `y ∈ 𝔑_{−k}(b 0)` multiplies `ℌ ∩ 𝔓^{⌊k/2⌋+1}` into `ℌ` on both sides when `k` is below
all depths and `n`. -/
private theorem mul_mem_simpleHLattice_of_adjoint (L : LatticeChain 𝒪[F] F V) (n : ℤ) {s : ℕ}
    (b : Fin (s + 1) → A) (d : Fin s → ℤ)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hstep : ∀ i : Fin s, criticalExponent L (b i.castSucc) = ((-d i : ℤ) : WithBot ℤ) ∧
      b i.succ - b i.castSucc ∈ L.endFiltration (-d i))
    (hmono : StrictMono d) (hdn : ∀ i, d i < n)
    (hlast : criticalExponent L (b (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last s)) = ⊥)
    (k : ℤ) (hk : 0 ≤ k) (hkd : ∀ i, k < d i) (hkn : k < n)
    {y h : A} (hy : y ∈ L.endFiltration 0)
    (hya : adjointMap 𝒪[F] (b 0) y ∈ L.endFiltration (-k))
    (hh : h ∈ simpleHLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ))
    (hhk : h ∈ L.endFiltration (k / 2 + 1)) :
    y * h ∈ simpleHLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) ∧
      h * y ∈ simpleHLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) := by
  induction s generalizing k y h with
  | zero =>
    have hh' := hh
    rw [List.ofFn_zero] at hh'
    change h ∈ centralizerLattice L (b 0) 0 ⊔ L.endFiltration (simpleHCutoff n) at hh'
    obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hh'
    have hwk : w ∈ L.endFiltration (k / 2 + 1) :=
      L.endFiltration_antitone (by unfold simpleHCutoff; omega) hw
    have hck : c ∈ L.endFiltration (k / 2 + 1) := by simpa using sub_mem hhk hwk
    obtain ⟨hyc, hcy⟩ := centralizer_mul_mem_simpleHLattice L n b d hfield hstep hlast k hk hkd
      hkn hy hya hc hck
    have hR : L.endFiltration (simpleHCutoff n) ≤
        simpleHLattice L n (b 0) (List.ofFn fun i : Fin 0 => b i.succ) := by
      rw [List.ofFn_zero]
      exact le_sup_right
    refine ⟨?_, ?_⟩
    · rw [mul_add]
      exact add_mem hyc (hR (by simpa using L.mul_mem_endFiltration hy hw))
    · rw [add_mul]
      exact add_mem hcy (hR (by simpa using L.mul_mem_endFiltration hw hy))
  | succ s ih =>
    let b' : Fin (s + 1) → A := fun j => b j.succ
    obtain ⟨hc0, hdiff⟩ := hstep 0
    change criticalExponent L (b 0) = ((-d 0 : ℤ) : WithBot ℤ) at hc0
    change b' 0 - b 0 ∈ L.endFiltration (-d 0) at hdiff
    have hk0 := hkd 0
    have hsplit : simpleHLattice L n (b 0) (List.ofFn fun i : Fin (s + 1) => b i.succ) =
        centralizerLattice L (b 0) 0 ⊔
          (simpleHLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
            L.endFiltration (simpleHCutoff (d 0))) := by
      rw [List.ofFn_succ]
      change centralizerLattice L (b 0) 0 ⊔
        (simpleHLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
          L.endFiltration (simpleHCutoff (finiteCriticalDepth L n (b 0)))) = _
      rw [finiteCriticalDepth_of_eq'' L n (d 0) _ hc0]
    have hh' := hh
    rw [hsplit] at hh'
    obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hh'
    have hwk : w ∈ L.endFiltration (k / 2 + 1) :=
      L.endFiltration_antitone (by unfold simpleHCutoff; omega) hw.2
    have hck : c ∈ L.endFiltration (k / 2 + 1) := by simpa using sub_mem hhk hwk
    obtain ⟨hyc, hcy⟩ := centralizer_mul_mem_simpleHLattice L n b d hfield hstep hlast k hk hkd
      hkn hy hya hc hck
    have hya' : adjointMap 𝒪[F] (b' 0) y ∈ L.endFiltration (-d 0) :=
      adjoint_next_mem L hdiff hy (L.endFiltration_antitone (by omega) hya) (by omega)
    obtain ⟨hyw, hwy⟩ := ih b' (fun j => d j.succ) (fun j => hfield j.succ)
      (fun j => by simpa only [b', Fin.succ_castSucc] using hstep j.succ)
      (fun i j hij => hmono (Fin.succ_lt_succ_iff.mpr hij)) (fun j => hdn j.succ)
      (by simpa only [b', Fin.succ_last] using hlast) (d 0) (by omega)
      (fun j => hmono (Fin.succ_pos j)) (hdn 0) hy hya' hw.1 hw.2
    rw [hsplit] at hyc hcy ⊢
    refine ⟨?_, ?_⟩
    · rw [mul_add]
      exact add_mem hyc
        (Submodule.mem_sup_right ⟨hyw, by simpa using L.mul_mem_endFiltration hy hw.2⟩)
    · rw [add_mul]
      exact add_mem hcy
        (Submodule.mem_sup_right ⟨hwy, by simpa using L.mul_mem_endFiltration hw.2 hy⟩)


/-- `y ∈ 𝔅 ∩ 𝔓^u` times `c ∈ 𝔄` with `[b 0, c] ∈ 𝔓^{−ℓ}` lies in `𝔍` when `2(ℓ − u)` is at
most all depths and `n`. -/
private theorem centralizer_mul_mem_simpleJLattice (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (hn0 : 0 ≤ n) {s : ℕ} (b : Fin (s + 1) → A) (d : Fin s → ℤ)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hstep : ∀ i : Fin s, criticalExponent L (b i.castSucc) = ((-d i : ℤ) : WithBot ℤ) ∧
      b i.succ - b i.castSucc ∈ L.endFiltration (-d i))
    (hlast : criticalExponent L (b (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last s)) = ⊥)
    (ℓ u : ℤ) (hu : 0 ≤ u) (hd0 : ∀ i, 0 ≤ d i) (h2d : ∀ i, 2 * (ℓ - u) ≤ d i)
    (h2n : 2 * (ℓ - u) ≤ n) {y c : A} (hy : y ∈ centralizerLattice L (b 0) 0)
    (hyu : y ∈ L.endFiltration u) (hc : c ∈ L.endFiltration 0)
    (hca : adjointMap 𝒪[F] (b 0) c ∈ L.endFiltration (-ℓ)) :
    y * c ∈ simpleJLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) := by
  have hy' : b 0 * y - y * b 0 = 0 := hy.2
  refine mem_simpleJLattice_of_adjoint L n (max (ℓ - u) 0) (le_max_right _ _) (by omega) b d
    hfield hstep (fun i => by have := h2d i; have := hd0 i; omega) hlast
    (by simpa using L.mul_mem_endFiltration (L.endFiltration_antitone hu hyu) hc) ?_
  rw [adjoint_mul_left_of_ker (b 0) hy']
  exact L.endFiltration_antitone (by omega) (L.mul_mem_endFiltration hyu hca)

/-- Right multiplication by `c ∈ 𝔄` with `[b 0, c] ∈ 𝔓^{−ℓ}` maps `𝔍 ∩ 𝔓^u` into `𝔍`, when
`ℓ` is at most all depths, `u` is at most all the `𝔍`-cutoffs, and `2(ℓ − u)` is at most all
depths and `n`. -/
private theorem mul_mem_simpleJLattice_of_adjoint_seq (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (hn0 : 0 ≤ n) {s : ℕ} (b : Fin (s + 1) → A) (d : Fin s → ℤ)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (b i)), letI := hf.toField
      ∀ a : (elementAlgebra (b i))ˣ, subfieldUnits F (elementAlgebra (b i)) V a ∈ L.stabilizer)
    (hstep : ∀ i : Fin s, criticalExponent L (b i.castSucc) = ((-d i : ℤ) : WithBot ℤ) ∧
      b i.succ - b i.castSucc ∈ L.endFiltration (-d i))
    (hmono : StrictMono d) (hdn : ∀ i, d i < n)
    (hlast : criticalExponent L (b (Fin.last s)) = ((-n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (b (Fin.last s)) = ⊥)
    (ℓ u : ℤ) (hℓ : 0 ≤ ℓ) (hu : 0 ≤ u) (hℓd : ∀ i, ℓ ≤ d i) (hun : u ≤ (n + 1) / 2)
    (hud : ∀ i, u ≤ (d i + 1) / 2) (h2d : ∀ i, 2 * (ℓ - u) ≤ d i) (h2n : 2 * (ℓ - u) ≤ n)
    {w c : A} (hw : w ∈ simpleJLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ))
    (hwu : w ∈ L.endFiltration u) (hc : c ∈ L.endFiltration 0)
    (hca : adjointMap 𝒪[F] (b 0) c ∈ L.endFiltration (-ℓ)) :
    w * c ∈ simpleJLattice L n (b 0) (List.ofFn fun i : Fin s => b i.succ) := by
  induction s generalizing ℓ u w c with
  | zero =>
    have hw' := hw
    rw [List.ofFn_zero] at hw'
    change w ∈ centralizerLattice L (b 0) 0 ⊔ L.endFiltration (simpleJCutoff n) at hw'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw'
    have hzu : z ∈ L.endFiltration u :=
      L.endFiltration_antitone (by unfold simpleJCutoff; omega) hz
    have hyu : y ∈ L.endFiltration u := by simpa using sub_mem hwu hzu
    rw [add_mul]
    refine add_mem (centralizer_mul_mem_simpleJLattice L n hn0 b d hfield hstep hlast ℓ u hu
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) h2n hy hyu hc hca) ?_
    rw [List.ofFn_zero]
    exact Submodule.mem_sup_right (by simpa using L.mul_mem_endFiltration hz hc)
  | succ s ih =>
    let b' : Fin (s + 1) → A := fun j => b j.succ
    obtain ⟨hc0, hdiff⟩ := hstep 0
    change criticalExponent L (b 0) = ((-d 0 : ℤ) : WithBot ℤ) at hc0
    change b' 0 - b 0 ∈ L.endFiltration (-d 0) at hdiff
    have hsplit : simpleJLattice L n (b 0) (List.ofFn fun i : Fin (s + 1) => b i.succ) =
        centralizerLattice L (b 0) 0 ⊔
          (simpleJLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
            L.endFiltration (simpleJCutoff (d 0))) := by
      rw [List.ofFn_succ]
      change centralizerLattice L (b 0) 0 ⊔
        (simpleJLattice L n (b' 0) (List.ofFn fun j : Fin s => b' j.succ) ⊓
          L.endFiltration (simpleJCutoff (finiteCriticalDepth L n (b 0)))) = _
      rw [finiteCriticalDepth_of_eq'' L n (d 0) _ hc0]
    have hd0 : ∀ i, 0 ≤ d i := fun i => le_trans hℓ (hℓd i)
    have hw' := hw
    rw [hsplit] at hw'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw'
    have hzu : z ∈ L.endFiltration u :=
      L.endFiltration_antitone (by have := hud 0; unfold simpleJCutoff; omega) hz.2
    have hyu : y ∈ L.endFiltration u := by simpa using sub_mem hwu hzu
    rw [add_mul]
    refine add_mem (centralizer_mul_mem_simpleJLattice L n hn0 b d hfield hstep hlast ℓ u hu hd0
      h2d h2n hy hyu hc hca) ?_
    have hℓ0 := hℓd 0
    have hdn0 := hdn 0
    have hca' : adjointMap 𝒪[F] (b' 0) c ∈ L.endFiltration (-d 0) :=
      adjoint_next_mem L hdiff hc (L.endFiltration_antitone (by omega) hca) (by omega)
    have hzc := ih b' (fun j => d j.succ) (fun j => hfield j.succ)
      (fun j => by simpa only [b', Fin.succ_castSucc] using hstep j.succ)
      (fun i j hij => hmono (Fin.succ_lt_succ_iff.mpr hij)) (fun j => hdn j.succ)
      (by simpa only [b', Fin.succ_last] using hlast) (d 0) ((d 0 + 1) / 2) (by omega)
      (by omega) (fun j => (hmono (Fin.succ_pos j)).le) (by omega)
      (fun j => by have := hmono (Fin.succ_pos j); omega)
      (fun j => by have := hmono (Fin.succ_pos j); omega) (by omega) hz.1
      (by have h := hz.2; unfold simpleJCutoff at h; exact h) hc hca'
    rw [hsplit]
    exact Submodule.mem_sup_right ⟨hzc, by simpa using L.mul_mem_endFiltration hz.2 hc⟩

/-! ### The recursions for a defining sequence -/

/-- The data of a defining sequence in the form used by the recursions above. -/
private theorem definingSequence_recursionData {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) :
    (∀ i, ∃ hf : IsField (elementAlgebra (q.terms i).b), letI := hf.toField
      ∀ a : (elementAlgebra (q.terms i).b)ˣ,
        subfieldUnits F (elementAlgebra (q.terms i).b) V a ∈ S.chain.stabilizer) ∧
    (∀ i : Fin q.steps, criticalExponent S.chain (q.terms i.castSucc).b =
        ((-(q.terms i.succ).r : ℤ) : WithBot ℤ) ∧
      (q.terms i.succ).b - (q.terms i.castSucc).b ∈
        S.chain.endFiltration (-(q.terms i.succ).r)) ∧
    StrictMono (fun i : Fin q.steps => (q.terms i.succ).r) ∧
    (∀ i : Fin q.steps, (q.terms i.succ).r < S.n) ∧
    (criticalExponent S.chain (q.terms (Fin.last q.steps)).b = ((-S.n : ℤ) : WithBot ℤ) ∨
      elementAlgebra (q.terms (Fin.last q.steps)).b = ⊥) ∧
    (∀ i : Fin q.steps, finiteCriticalDepth S.chain S.n S.b ≤ (q.terms i.succ).r) := by
  obtain ⟨-, hs, -, -, hmono, hstep, hlast, -⟩ := q.isDefiningSequence
  refine ⟨fun i => ?_, hstep, fun i j hij => hmono (Fin.succ_lt_succ_iff.mpr hij),
    fun i => ?_, ?_, fun i => ?_⟩
  · obtain ⟨hf, hu⟩ := (hs i).2.2.1.1
    let := hf.toField
    refine ⟨hf, fun a => ?_⟩
    rw [(normalizer F V S.chain).2.1, ← (hs i).1, ← (normalizer F V (q.terms i).chain).2.1]
    exact hu a
  · have h := (q.terms i.succ).r_lt_n
    rwa [(hs i.succ).2.1] at h
  · rcases hlast with h | h
    · exact Or.inl h
    · right
      by_contra hb
      apply hb
      simpa [criticalExponent] using h
  · have hpos : 0 < q.steps := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    let i₀ : Fin q.steps := ⟨0, hpos⟩
    have h₀ := (hstep i₀).1
    have hi₀ : i₀.castSucc = 0 := Fin.ext rfl
    rw [hi₀, q.firstElement] at h₀
    rw [finiteCriticalDepth_of_eq'' S.chain S.n _ _ h₀]
    exact hmono.monotone (Fin.succ_le_succ_iff.mpr (show i₀ ≤ i from Nat.zero_le _))

/-- **Multiplying `ℌ` by adjoint preimages.** Let `k < r = finiteCriticalDepth`, and let `y ∈ 𝔄`
with `βy − yβ ∈ 𝔓^{−k}`. Then `y` multiplies `ℌ(β,𝔄) ∩ 𝔓^{⌊k/2⌋+1}` into `ℌ(β,𝔄)` on both
sides. -/
theorem mul_mem_simpleHLattice_of_mem_adjointLattice (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (k : ℕ)
    (hk : (k : ℤ) < finiteCriticalDepth S.chain S.n S.b) {y h : A}
    (hy : y ∈ adjointLattice S.chain S.b (-(k : ℤ)))
    (hh : h ∈ simpleHLattice S.chain S.n S.b q.tail)
    (hhk : h ∈ S.chain.endFiltration ((k : ℤ) / 2 + 1)) :
    y * h ∈ simpleHLattice S.chain S.n S.b q.tail ∧
      h * y ∈ simpleHLattice S.chain S.n S.b q.tail := by
  obtain ⟨hfield, hstep, hmono, hdn, hlast, hdep⟩ := definingSequence_recursionData q
  have hlev := finiteCriticalDepth_le_level q
  have hfirst : (q.terms 0).b = S.b := q.firstElement
  change y * h ∈ simpleHLattice S.chain S.n S.b
      (List.ofFn fun i : Fin q.steps => (q.terms i.succ).b) ∧
    h * y ∈ simpleHLattice S.chain S.n S.b (List.ofFn fun i : Fin q.steps => (q.terms i.succ).b)
  change h ∈ simpleHLattice S.chain S.n S.b
    (List.ofFn fun i : Fin q.steps => (q.terms i.succ).b) at hh
  rw [← hfirst] at hy hh ⊢
  exact mul_mem_simpleHLattice_of_adjoint S.chain S.n (fun i => (q.terms i).b)
    (fun i => (q.terms i.succ).r) hfield hstep hmono hdn hlast k (by positivity)
    (fun i => by have := hdep i; omega) (by omega) hy.1 hy.2 hh hhk

/-- **Multiplying `𝔍^t` by `𝔑_{−r}`.** Let `r = finiteCriticalDepth ≥ 0` and
`t = ⌊(r+1)/2⌋`. Right multiplication by elements of `𝔑_{−r}(β,𝔄)` maps the lattice
`𝔍^t(β,𝔄) = 𝔍(β,𝔄) ∩ 𝔓^t` into itself. -/
theorem mul_mem_simpleJLayer_of_mem_adjointLattice (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (hr : 0 ≤ finiteCriticalDepth S.chain S.n S.b) {w c : A}
    (hw : w ∈ simpleJLayer S.chain S.n S.b q.tail
      (simpleJCutoff (finiteCriticalDepth S.chain S.n S.b)).toNat)
    (hc : c ∈ adjointLattice S.chain S.b (-finiteCriticalDepth S.chain S.n S.b)) :
    w * c ∈ simpleJLayer S.chain S.n S.b q.tail
      (simpleJCutoff (finiteCriticalDepth S.chain S.n S.b)).toNat := by
  obtain ⟨hfield, hstep, hmono, hdn, hlast, hdep⟩ := definingSequence_recursionData q
  have hlev := finiteCriticalDepth_le_level q
  set r := finiteCriticalDepth S.chain S.n S.b with hr_def
  have ht : (((simpleJCutoff r).toNat : ℕ) : ℤ) = (r + 1) / 2 := by
    unfold simpleJCutoff
    exact Int.toNat_of_nonneg (by omega)
  have hfirst : (q.terms 0).b = S.b := q.firstElement
  obtain ⟨hwJ, hwt⟩ := hw
  rw [ht] at hwt
  refine ⟨?_, ?_⟩
  · change w * c ∈ simpleJLattice S.chain S.n S.b
      (List.ofFn fun i : Fin q.steps => (q.terms i.succ).b)
    change w ∈ simpleJLattice S.chain S.n S.b
      (List.ofFn fun i : Fin q.steps => (q.terms i.succ).b) at hwJ
    have hc' := hc
    rw [← hfirst] at hc' hwJ ⊢
    exact mul_mem_simpleJLattice_of_adjoint_seq S.chain S.n (by omega) (fun i => (q.terms i).b)
      (fun i => (q.terms i.succ).r) hfield hstep hmono hdn hlast r ((r + 1) / 2) hr (by omega)
      hdep (by omega) (fun i => by have := hdep i; omega) (fun i => by have := hdep i; omega)
      (by omega) hwJ hwt hc'.1 hc'.2
  · rw [ht]
    simpa using S.chain.mul_mem_endFiltration hwt hc.1

end Langlands.BushnellKutzko
