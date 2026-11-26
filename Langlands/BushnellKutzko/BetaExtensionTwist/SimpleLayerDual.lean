import Langlands.BushnellKutzko.BetaExtensionTwist.DomainProduct
import Langlands.BushnellKutzko.BetaExtensionTwist.TraceLattice
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.StratumEquivalenceProof

/-! # Adjoint trace duality at level one of a simple stratum -/

noncomputable section
open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "tr" => LinearMap.trace F V

variable (L : LatticeChain 𝒪[F] F V)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem levelOne_sup (β : A) (X : Submodule 𝒪[F] A) (hX : X ≤ L.endFiltration 1) :
    (centralizerLattice L β 0 ⊔ X) ⊓ L.endFiltration 1 = centralizerLattice L β 1 ⊔ X := by
  rw [sup_comm (centralizerLattice L β 0), sup_inf_assoc_of_le _ hX, sup_comm]
  congr 1
  ext z
  constructor
  · intro h
    exact ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨L.endFiltration_antitone (by norm_num) h.1, h.2⟩, h.1⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem levelOne_sup_deep (β : A) (X : Submodule 𝒪[F] A) {d : ℤ} (hd : 1 ≤ d) :
    (centralizerLattice L β 0 ⊔ (X ⊓ L.endFiltration d)) ⊓ L.endFiltration 1 = centralizerLattice L β 1 ⊔ ((X ⊓ L.endFiltration 1) ⊓ L.endFiltration d) := by
  have hle : L.endFiltration d ≤ L.endFiltration 1 := L.endFiltration_antitone hd
  rw [levelOne_sup L β _ (inf_le_right.trans hle)]
  have hX : X ⊓ L.endFiltration 1 ⊓ L.endFiltration d = X ⊓ L.endFiltration d := by
    rw [inf_assoc, inf_eq_right.mpr hle]
  rw [hX]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Both level-one simple-stratum lattices contain the level-one centralizer lattice. -/
theorem centralizer_le_simpleLayers (n : ℤ) (β : A) (tail : List A) :
    centralizerLattice L β 1 ≤ simpleHLayer L n β tail 1 ∧ centralizerLattice L β 1 ≤ simpleJLayer L n β tail 1 := by
  have hQ : centralizerLattice L β 1 ≤ centralizerLattice L β 0 := inf_le_inf_right _ (L.endFiltration_antitone (by norm_num))
  cases tail <;> exact ⟨le_inf (hQ.trans le_sup_left) inf_le_left,
    le_inf (hQ.trans le_sup_left) inf_le_left⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_deep_endFiltration_le_layers (n : ℤ) (β : A) (tail : List A) :
    ∃ m : ℤ, L.endFiltration m ≤ simpleHLayer L n β tail 1 ∧ L.endFiltration m ≤ simpleJLayer L n β tail 1 := by
  induction tail generalizing β with
  | nil =>
    let m := max 1 (max (simpleHCutoff n) (simpleJCutoff n))
    have h1 : L.endFiltration m ≤ L.endFiltration 1 := L.endFiltration_antitone (le_max_left _ _)
    refine ⟨m, le_inf ?_ h1, le_inf ?_ h1⟩
    · exact (L.endFiltration_antitone (by dsimp [m]; omega)).trans le_sup_right
    · exact (L.endFiltration_antitone (by dsimp [m]; omega)).trans le_sup_right
  | cons γ tail ih =>
    obtain ⟨m, hH, hJ⟩ := ih γ
    let d := finiteCriticalDepth L n β
    let k := max (max m 1) (max (simpleHCutoff d) (simpleJCutoff d))
    have h1 : L.endFiltration k ≤ L.endFiltration 1 := L.endFiltration_antitone (by dsimp [k]; omega)
    have hk : L.endFiltration k ≤ L.endFiltration m := L.endFiltration_antitone (by dsimp [k]; omega)
    refine ⟨k, le_inf ?_ h1, le_inf ?_ h1⟩
    · exact (le_inf (hk.trans (hH.trans inf_le_left))
        (L.endFiltration_antitone (by dsimp [k, d]; omega))).trans le_sup_right
    · exact (le_inf (hk.trans (hJ.trans inf_le_left))
        (L.endFiltration_antitone (by dsimp [k, d]; omega))).trans le_sup_right

private theorem traceLatticeDual_H_one_inf (n : ℤ) (β : A) (tail : List A) (d : ℤ) :
    traceLatticeDual (simpleHLayer L n β tail 1 ⊓ L.endFiltration d) =
      traceLatticeDual (simpleHLayer L n β tail 1) ⊔ L.endFiltration (1 - d) := by
  let := L.finiteDimensional
  obtain ⟨m, h, -⟩ := exists_deep_endFiltration_le_layers L n β tail
  have ht : traceLatticeDual (simpleHLayer L n β tail 1) ≤ L.endFiltration (1 - m) := by
    simpa only [traceLatticeDual_endFiltration] using traceLatticeDual_antitone h
  rw [traceLatticeDual_inf_of_fg (P := simpleHLayer L n β tail 1)
    (Q := L.endFiltration d) ((L.fg_endFiltration 1).of_le inf_le_right)
    (L.fg_endFiltration d) ((L.fg_endFiltration (1 - m)).of_le ht)
    (traceLatticeDual_endFiltration L d ▸ L.fg_endFiltration (1 - d)),
    traceLatticeDual_endFiltration]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem adjoint_annihilates_centralizer [FiniteDimensional F V] (β x : A) :
    adjointMap 𝒪[F] β x ∈ traceLatticeDual (centralizerLattice L β 1) := by
  apply mem_traceLatticeDual.mpr
  intro z hz
  have h1 : adjointMap 𝒪[F] β x ∈ (adjointMap F β).range := ⟨x, rfl⟩
  rw [range_adjoint_eq_traceAnnilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator] at h1
  change tr (adjointMap 𝒪[F] β x * z) ∈ maximalIdealInField 𝒪[F] F
  rw [show tr (adjointMap 𝒪[F] β x * z) = 0 from h1 z hz.2]
  exact ⟨0, zero_mem _, map_zero _⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem adjoint_diff_mem {β γ x : A} {c d : ℤ}
    (hε : γ - β ∈ L.endFiltration (-d)) (hx : x ∈ L.endFiltration c) :
    adjointMap 𝒪[F] γ x - adjointMap 𝒪[F] β x ∈ L.endFiltration (c - d) := by
  have h : adjointMap 𝒪[F] γ x - adjointMap 𝒪[F] β x = (γ - β) * x - x * (γ - β) := by
    change (γ * x - x * γ) - (β * x - x * β) = _
    noncomm_ring
  rw [h]
  exact sub_mem (by simpa only [sub_eq_add_neg, add_comm] using L.mul_mem_endFiltration hε hx)
    (by simpa only [sub_eq_add_neg] using L.mul_mem_endFiltration hx hε)

/-- The two forms of level-one adjoint duality used in the induction. -/
private def LevelOneAdjointDual (n : ℤ) (β : A) (tail : List A) : Prop :=
  let H := simpleHLayer L n β tail 1
  let J := simpleJLayer L n β tail 1
  (∀ x, adjointMap 𝒪[F] β x ∈ traceLatticeDual H ↔ adjointMap 𝒪[F] β x ∈ J.map (adjointMap 𝒪[F] β)) ∧
    traceLatticeDual H = J.map (adjointMap 𝒪[F] β) ⊔ L.endFiltration 0

private theorem levelOneAdjointDual_of_reduced (n : ℤ) (β : A) (tail : List A)
    (hf : IsField (elementAlgebra β))
    (hnormal : letI := hf.toField
      ∀ c : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V c ∈ L.stabilizer)
    (h : ∀ x, adjointMap 𝒪[F] β x ∈ traceLatticeDual (simpleHLayer L n β tail 1) ↔
      adjointMap 𝒪[F] β x ∈ (simpleJLayer L n β tail 1).map (adjointMap 𝒪[F] β)) :
    LevelOneAdjointDual L n β tail := by
  refine ⟨h, ?_⟩
  obtain ⟨p, hp, hfix, hP, -⟩ := exists_common_centralizer_projection L β hf hnormal 1
    (centralizerUnitGroup β).one_mem
  rw [traceLatticeDual_eq_sup_adj_range L β (simpleHLayer L n β tail 1) inf_le_right
    (centralizer_le_simpleLayers L n β tail).1 p hp hfix hP]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, x, rfl⟩
    exact (h x).mp hz
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(h x).mpr ⟨x, hx, rfl⟩, x, rfl⟩

private theorem levelOneAdjointDual_nil (n : ℤ) (hn : 0 < n) (β : A)
    (hf : IsField (elementAlgebra β))
    (hnormal : letI := hf.toField
      ∀ c : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V c ∈ L.stabilizer)
    (hc : criticalExponent L β ≤ ((-n : ℤ) : WithBot ℤ)) (hβ : β ∈ L.endFiltration (-n)) :
    LevelOneAdjointDual L n β [] := by
  let := L.finiteDimensional
  let c := simpleJCutoff n
  let d := simpleHCutoff n
  have hc1 : 1 ≤ c := by dsimp [c, simpleJCutoff]; omega
  have hd1 : 1 ≤ d := by dsimp [d, simpleHCutoff]; omega
  have heq : c - n = 1 - d := by dsimp [c, d, simpleJCutoff, simpleHCutoff]; omega
  have hh : simpleHLayer L n β [] 1 = centralizerLattice L β 1 ⊔ L.endFiltration d :=
    levelOne_sup L β _ (L.endFiltration_antitone hd1)
  have hj : simpleJLayer L n β [] 1 = centralizerLattice L β 1 ⊔ L.endFiltration c :=
    levelOne_sup L β _ (L.endFiltration_antitone hc1)
  apply levelOneAdjointDual_of_reduced L n β [] hf hnormal
  intro x
  rw [hh, hj, traceLatticeDual_sup, traceLatticeDual_endFiltration, Submodule.mem_inf,
    and_iff_right (adjoint_annihilates_centralizer L β x)]
  constructor
  · intro hx
    change β * x - x * β ∈ L.endFiltration (1 - d) at hx
    obtain ⟨u, hu, hxu⟩ := exists_commute_sub_mem L β hf hnormal hc c x
      (by simpa only [← heq, sub_eq_add_neg] using hx)
    refine ⟨x - u, Submodule.mem_sup_right hxu, ?_⟩
    rw [map_sub, show adjointMap 𝒪[F] β u = 0 from hu, sub_zero]
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨t, ht, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add, show adjointMap 𝒪[F] β t = 0 from ht.2, zero_add] at hzx
    rw [← hzx, ← heq]
    change β * v - v * β ∈ L.endFiltration (c - n)
    exact sub_mem (by simpa only [sub_eq_add_neg, add_comm] using L.mul_mem_endFiltration hβ hv)
      (by simpa only [sub_eq_add_neg] using L.mul_mem_endFiltration hv hβ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem levelOne_le_centralizer_sup_deeper (n : ℤ) (β : A) (tail : List A)
    (d : ℤ) (hd : 0 < d) (hcut : (if tail.isEmpty then n else finiteCriticalDepth L n β) = d)
    (c b : ℤ) (hc : c ≤ simpleJCutoff d) (hb : b ≤ simpleHCutoff d) :
    let H := simpleHLayer L n β tail 1
    let J := simpleJLayer L n β tail 1
    H ≤ centralizerLattice L β 1 ⊔ (H ⊓ L.endFiltration b) ∧ J ≤ centralizerLattice L β 1 ⊔ (J ⊓ L.endFiltration c) := by
  intro H J
  have hH (X : Submodule 𝒪[F] A) (m e : ℤ) (hm : 1 ≤ m) (he : e ≤ m) :
      (centralizerLattice L β 0 ⊔ X) ⊓ L.endFiltration 1 = centralizerLattice L β 1 ⊔ X → X ≤ L.endFiltration m →
      (centralizerLattice L β 0 ⊔ X) ⊓ L.endFiltration 1 ≤ centralizerLattice L β 1 ⊔ (((centralizerLattice L β 0 ⊔ X) ⊓ L.endFiltration 1) ⊓ L.endFiltration e) := by
    intro hX hXP
    have i : X ≤ ((centralizerLattice L β 0 ⊔ X) ⊓ L.endFiltration 1) ⊓ L.endFiltration e :=
      le_inf (le_inf le_sup_right (hXP.trans (L.endFiltration_antitone hm)))
        (hXP.trans (L.endFiltration_antitone he))
    rw [hX]
    exact sup_le_sup_left (by rw [← hX]; exact i) _
  have hHd : 1 ≤ simpleHCutoff d := by unfold simpleHCutoff; omega
  have hJd : 1 ≤ simpleJCutoff d := by unfold simpleJCutoff; omega
  cases tail with
  | nil =>
    change n = d at hcut
    subst d
    exact ⟨hH (L.endFiltration (simpleHCutoff n)) _ _ hHd hb
        (levelOne_sup L β _ (L.endFiltration_antitone hHd)) le_rfl,
      hH (L.endFiltration (simpleJCutoff n)) _ _ hJd hc
        (levelOne_sup L β _ (L.endFiltration_antitone hJd)) le_rfl⟩
  | cons γ tail =>
    change finiteCriticalDepth L n β = d at hcut
    subst d
    have hHle : simpleHLattice L n γ tail ⊓ L.endFiltration (simpleHCutoff (finiteCriticalDepth L n β)) ≤
        L.endFiltration (simpleHCutoff (finiteCriticalDepth L n β)) := inf_le_right
    have hJle : simpleJLattice L n γ tail ⊓ L.endFiltration (simpleJCutoff (finiteCriticalDepth L n β)) ≤
        L.endFiltration (simpleJCutoff (finiteCriticalDepth L n β)) := inf_le_right
    exact ⟨hH _ _ _ hHd hb (levelOne_sup L β _
        (hHle.trans (L.endFiltration_antitone hHd))) hHle,
      hH _ _ _ hJd hc (levelOne_sup L β _
        (hJle.trans (L.endFiltration_antitone hJd))) hJle⟩

private theorem levelOneAdjointDual_cons (n : ℤ) (β γ : A) (tail : List A)
    (hf : IsField (elementAlgebra β))
    (hnormal : letI := hf.toField
      ∀ z : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V z ∈ L.stabilizer)
    (hd : 0 < finiteCriticalDepth L n β)
    (hcrit : criticalExponent L β ≤ ((-finiteCriticalDepth L n β : ℤ) : WithBot ℤ))
    (hε : γ - β ∈ L.endFiltration (-finiteCriticalDepth L n β))
    (hdepth : finiteCriticalDepth L n β ≤ (if tail.isEmpty then n else finiteCriticalDepth L n γ))
    (ih : LevelOneAdjointDual L n γ tail) : LevelOneAdjointDual L n β (γ :: tail) := by
  let := L.finiteDimensional
  let r := finiteCriticalDepth L n β
  let c := simpleJCutoff r
  let b := simpleHCutoff r
  let H := simpleHLayer L n γ tail 1
  let J := simpleJLayer L n γ tail 1
  let E := H ⊓ L.endFiltration b
  let D := J ⊓ L.endFiltration c
  have hc1 : 1 ≤ c := by dsimp [c, simpleJCutoff]; omega
  have hb1 : 1 ≤ b := by dsimp [b, simpleHCutoff]; omega
  have heq : c - r = 1 - b := by dsimp [c, b, simpleJCutoff, simpleHCutoff]; omega
  have ha (x : A) (hx : x ∈ L.endFiltration c) : adjointMap 𝒪[F] γ x - adjointMap 𝒪[F] β x ∈ traceLatticeDual E := by
    apply traceLatticeDual_antitone (inf_le_right : E ≤ L.endFiltration b)
    rw [traceLatticeDual_endFiltration, ← heq]
    exact adjoint_diff_mem L hε hx
  have hH : simpleHLayer L n β (γ :: tail) 1 = centralizerLattice L β 1 ⊔ E :=
    levelOne_sup_deep L β _ hb1
  have hJ : simpleJLayer L n β (γ :: tail) 1 = centralizerLattice L β 1 ⊔ D :=
    levelOne_sup_deep L β _ hc1
  have hb : b ≤ simpleHCutoff (if tail.isEmpty then n else finiteCriticalDepth L n γ) := by
    change simpleHCutoff (finiteCriticalDepth L n β) ≤ _
    unfold simpleHCutoff
    omega
  have hc : c ≤ simpleJCutoff (if tail.isEmpty then n else finiteCriticalDepth L n γ) := by
    change simpleJCutoff (finiteCriticalDepth L n β) ≤ _
    unfold simpleJCutoff
    omega
  obtain ⟨hHle, hJle⟩ := levelOne_le_centralizer_sup_deeper L n γ tail _
    (hd.trans_le hdepth) rfl c b hc hb
  have hJQ : centralizerLattice L γ 1 ≤ J := (centralizer_le_simpleLayers L n γ tail).2
  apply levelOneAdjointDual_of_reduced L n β (γ :: tail) hf hnormal
  intro x
  rw [hH, hJ, traceLatticeDual_sup, Submodule.mem_inf,
    and_iff_right (adjoint_annihilates_centralizer L β x)]
  constructor
  · intro hx
    have hdE : traceLatticeDual E = J.map (adjointMap 𝒪[F] γ) ⊔ L.endFiltration (1 - b) := by
      change traceLatticeDual (H ⊓ L.endFiltration b) = _
      rw [traceLatticeDual_H_one_inf, ih.2, sup_assoc,
        sup_eq_right.mpr (L.endFiltration_antitone (by omega))]
    obtain ⟨z, ⟨t, ht, rfl⟩, v, hv, he⟩ := Submodule.mem_sup.mp (hdE ▸ hx)
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp (hJle ht)
    rw [map_add, show adjointMap 𝒪[F] γ u = 0 from hu.2, zero_add] at he
    have he' : adjointMap 𝒪[F] β (x - w) ∈ L.endFiltration (c + -r) := by
      rw [map_sub, ← he, show c + -r = 1 - b by omega]
      rw [show adjointMap 𝒪[F] γ w + v - adjointMap 𝒪[F] β w =
        v + (adjointMap 𝒪[F] γ w - adjointMap 𝒪[F] β w) by abel]
      exact add_mem hv (heq ▸ adjoint_diff_mem L hε hw.2)
    obtain ⟨q, hq, hsmall⟩ := exists_commute_sub_mem L β hf hnormal hcrit c (x - w) he'
    let f := x - w - q + w
    have hf : f ∈ L.endFiltration c := add_mem hsmall hw.2
    have hfx : adjointMap 𝒪[F] β f = adjointMap 𝒪[F] β x := by
      dsimp [f]
      rw [map_add, map_sub, map_sub, show adjointMap 𝒪[F] β q = 0 from hq, sub_zero, sub_add_cancel]
    have hfγ : adjointMap 𝒪[F] γ f ∈ traceLatticeDual E := by
      have h := add_mem (ha f hf) (hfx.symm ▸ hx)
      rwa [sub_add_cancel] at h
    have hfH : adjointMap 𝒪[F] γ f ∈ traceLatticeDual H := by
      apply traceLatticeDual_antitone hHle
      rw [traceLatticeDual_sup]
      exact ⟨adjoint_annihilates_centralizer L γ f, hfγ⟩
    obtain ⟨j, hj, hja⟩ := (ih.1 f).mp hfH
    have hfq : f - j ∈ centralizerLattice L γ 1 := by
      refine ⟨sub_mem (L.endFiltration_antitone hc1 hf) hj.2, ?_⟩
      change adjointMap 𝒪[F] γ (f - j) = 0
      rw [map_sub, hja, sub_self]
    have hfJ : f ∈ J := by
      have h := add_mem (hJQ hfq) hj
      rwa [sub_add_cancel] at h
    exact ⟨f, Submodule.mem_sup_right ⟨hfJ, hf⟩, hfx⟩
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx]
    obtain ⟨q, hq, f, hf, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add, show adjointMap 𝒪[F] β q = 0 from hq.2, zero_add]
    have hfγ : adjointMap 𝒪[F] γ f ∈ traceLatticeDual H := (ih.1 f).mpr ⟨f, hf.1, rfl⟩
    have hfγ' := traceLatticeDual_antitone (inf_le_left : E ≤ H) hfγ
    have h := sub_mem hfγ' (ha f hf.2)
    rwa [sub_sub_cancel] at h

private theorem levelOneAdjointDual_of_sequence (n : ℤ) (hn : 0 < n) {s : ℕ}
    (β : Fin (s + 1) → A)
    (hfield : ∀ i, ∃ hf : IsField (elementAlgebra (β i)), letI := hf.toField
      ∀ z : (elementAlgebra (β i))ˣ, subfieldUnits F (elementAlgebra (β i)) V z ∈ L.stabilizer)
    (hpos : ∀ i, 0 < finiteCriticalDepth L n (β i))
    (hmono : Monotone fun i => finiteCriticalDepth L n (β i))
    (hcrit : ∀ i, criticalExponent L (β i) ≤ ((-finiteCriticalDepth L n (β i) : ℤ) : WithBot ℤ))
    (hstep : ∀ i : Fin s,
      β i.succ - β i.castSucc ∈ L.endFiltration (-finiteCriticalDepth L n (β i.castSucc)))
    (hterminal : finiteCriticalDepth L n (β (Fin.last s)) = n ∧
      β (Fin.last s) ∈ L.endFiltration (-n)) :
    LevelOneAdjointDual L n (β 0) (List.ofFn fun i : Fin s => β i.succ) := by
  induction s with
  | zero =>
    rw [List.ofFn_zero]
    obtain ⟨h, hβ⟩ := hterminal
    rw [Fin.last_zero] at h hβ
    obtain ⟨hf, hnrm⟩ := hfield 0
    exact levelOneAdjointDual_nil L n hn (β 0) hf hnrm
      (by simpa only [h] using hcrit 0) hβ
  | succ s ih =>
    rw [List.ofFn_succ]
    let β' : Fin (s + 1) → A := fun i => β i.succ
    let tail := List.ofFn fun i : Fin s => β' i.succ
    change LevelOneAdjointDual L n (β 0) (β' 0 :: tail)
    have hterminal' : finiteCriticalDepth L n (β' (Fin.last s)) = n ∧
        β' (Fin.last s) ∈ L.endFiltration (-n) := by
      simpa only [β', Fin.succ_last] using hterminal
    have hstep' (i : Fin s) : β' i.succ - β' i.castSucc ∈
        L.endFiltration (-finiteCriticalDepth L n (β' i.castSucc)) := by
      simpa only [β', Fin.castSucc_succ] using hstep i.succ
    have htail : LevelOneAdjointDual L n (β' 0) tail :=
      ih β' (fun i => hfield i.succ) (fun i => hpos i.succ)
        (fun _ _ hij => hmono (Fin.succ_le_succ_iff.mpr hij)) (fun i => hcrit i.succ) hstep' hterminal'
    have hdepth : (if tail.isEmpty then n else finiteCriticalDepth L n (β' 0)) =
        finiteCriticalDepth L n (β' 0) := by
      by_cases h : tail.isEmpty = true
      · have hs : s = 0 := by
          have he : tail.length = 0 := List.length_eq_zero_iff.mpr (List.isEmpty_iff.mp h)
          simpa only [tail, List.length_ofFn] using he
        subst s
        simpa only [Fin.last_zero, ite_eq_left h] using hterminal'.1.symm
      · exact ite_eq_right h
    obtain ⟨hf, hnrm⟩ := hfield 0
    refine levelOneAdjointDual_cons L n (β 0) (β' 0) tail hf hnrm (hpos 0) (hcrit 0)
      (hstep 0) ?_ htail
    rw [hdepth]
    exact hmono (Fin.zero_le (0 : Fin (s + 1)).succ)

/-- The intersection of the level-one `H` lattice's trace dual with the full
range of the commutator `a_β = [β, -]` equals the image `a_β(J)` of the
level-one `J` lattice. The first conclusion tests this equality on elements
`a_β x`. The trace dual is the sum of `a_β(J)` and the order. -/
theorem simpleLayer_traceDual_adjoint (S : Stratum 𝒪[F] F V)
    (hr : S.r = 0) (q : S.DefiningSequenceChoice) :
    let H := simpleHLayer S.chain S.n S.b q.tail 1
    let J := simpleJLayer S.chain S.n S.b q.tail 1
    (∀ x, adjointMap 𝒪[F] S.b x ∈ traceLatticeDual H ↔
      adjointMap 𝒪[F] S.b x ∈ J.map (adjointMap 𝒪[F] S.b)) ∧
    traceLatticeDual H = J.map (adjointMap 𝒪[F] S.b) ⊔ S.chain.endFiltration 0 := by
  obtain ⟨-, hsimple, -, hfirstR, hlevels, hsteps, hlast, -⟩ := q.isDefiningSequence
  let β : Fin (q.steps + 1) → A := fun i => (q.terms i).b
  let depth := fun i => finiteCriticalDepth S.chain S.n (β i)
  have hn : 0 < S.n := hr ▸ S.r_lt_n
  have hfinite (i : Fin q.steps) : depth i.castSucc = (q.terms i.succ).r := by
    simp only [depth, β, finiteCriticalDepth, simpleCriticalDepth, (hsteps i).1,
      WithTop.untopD_coe, neg_neg]
  have hlastD : depth (Fin.last q.steps) = S.n := by
    rcases hlast with h | h
    · simp only [depth, β, finiteCriticalDepth, simpleCriticalDepth, h,
        WithTop.untopD_coe, neg_neg]
    · simp only [depth, β, finiteCriticalDepth, simpleCriticalDepth, h, WithTop.untopD_top]
  have hfield (i : Fin (q.steps + 1)) : ∃ hf : IsField (elementAlgebra (β i)), letI := hf.toField
      ∀ z : (elementAlgebra (β i))ˣ, subfieldUnits F (elementAlgebra (β i)) V z ∈ S.chain.stabilizer := by
    obtain ⟨hf, h⟩ := (hsimple i).2.2.1.1
    let := hf.toField
    refine ⟨hf, fun z => ?_⟩
    rw [(normalizer F V S.chain).2.1, ← (hsimple i).1, ← (normalizer F V (q.terms i).chain).2.1]
    exact h z
  have hpos (i : Fin (q.steps + 1)) : 0 < depth i := by
    cases i using Fin.lastCases with
    | last => rwa [hlastD]
    | cast i =>
      rw [hfinite i]
      have h : (q.terms 0).r < (q.terms i.succ).r := hlevels (Fin.succ_pos i)
      rwa [hfirstR, hr] at h
  have hmono : Monotone depth := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      have heq : j = Fin.last q.steps := le_antisymm (Fin.le_last j) hij
      exact heq ▸ le_rfl
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [hfinite i, hlastD, ← (hsimple i.succ).2.1]
        exact (q.terms i.succ).r_lt_n.le
      | cast j =>
        rw [hfinite i, hfinite j]
        exact hlevels.monotone (Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hij))
  have hcrit (i : Fin (q.steps + 1)) : criticalExponent S.chain (β i) ≤ ((-depth i : ℤ) : WithBot ℤ) := by
    cases i using Fin.lastCases with
    | last =>
      rw [hlastD]
      rcases hlast with h | h
      · exact h.le
      · exact h.trans_le bot_le
    | cast i => rw [hfinite i]; exact (hsteps i).1.le
  have hstep (i : Fin q.steps) : β i.succ - β i.castSucc ∈ S.chain.endFiltration (-depth i.castSucc) := by
    rw [hfinite i]
    exact (hsteps i).2
  have hlastB : β (Fin.last q.steps) ∈ S.chain.endFiltration (-S.n) := by
    let T := q.terms (Fin.last q.steps)
    have heq : T.chain.endFiltration = S.chain.endFiltration :=
      StratumEquivalence.endFiltration_eq_of_eq (a := 0) (c := 0) (by
        rw [← T.chain.toSubmodule_order, ← S.chain.toSubmodule_order, (hsimple _).1])
    have hm := (StratumEquivalence.mem_of_valuation_eq (hsimple (Fin.last q.steps)).2.2.1.2).1
    rw [heq, (hsimple (Fin.last q.steps)).2.1] at hm
    exact hm
  have hfirst : β 0 = S.b := q.firstElement
  have hmain := levelOneAdjointDual_of_sequence S.chain S.n hn β hfield hpos hmono hcrit
    hstep ⟨hlastD, hlastB⟩
  change LevelOneAdjointDual S.chain S.n (β 0) q.tail at hmain
  rw [hfirst] at hmain
  exact hmain

end Langlands.BushnellKutzko
