import Langlands.BushnellKutzko.UnequalSplitTypeAdjust
import Langlands.BushnellKutzko.SimpleCharacterFormalIntertwining
import Langlands.BushnellKutzko.TraceDualLatticeCalculus

/-! # Trace duality for the centralizer and the next H layer (BK93 (3.1.16), (8.2.17)) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- **BK93 (3.1.16), dual form.** Let `[𝔄, n, 0, β]` be simple with finite critical depth parameter
`r`, and `m = i + 1 < r`. If `x ∈ 𝔥^m` satisfies `ψ_A(a_β(y) x) = 1` for every
`y ∈ 𝔔^{r−m} 𝔑_{−r}`, then `x ∈ 𝔔^m + 𝔥^{m+1}`. -/
theorem mem_centralizer_sup_of_adjoint_orthogonal {E : Type*} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple)
    (q : S.DefiningSequenceChoice) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    (i : ℕ) {x : A} (hx : x ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1))
    (horth : ∀ y ∈ centralizerLattice S.chain S.b
        (finiteCriticalDepth S.chain S.n S.b - ((i + 1 : ℕ) : ℤ)) *
        adjointLattice S.chain S.b (-finiteCriticalDepth S.chain S.n S.b),
      traceCharacter ψF ((S.b * y - y * S.b) * x) = 1) :
    x ∈ centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ) ⊔
      simpleHLayer S.chain S.n S.b q.tail (i + 1 + 1) := by
  by_cases hb : elementAlgebra S.b = ⊥
  · apply Submodule.mem_sup_left
    refine ⟨hx.2, ?_⟩
    change S.b * x - x * S.b = 0
    rw [(commute_of_elementAlgebra_eq_bot hb x).eq, sub_self]
  have := S.chain.finiteDimensional
  set L := centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ) ⊔
    simpleHLayer S.chain S.n S.b q.tail (i + 1 + 1) with hL
  have hLfg : L.FG := by
    refine Submodule.FG.sup ?_ ?_
    · exact (S.chain.fg_endFiltration _).of_le inf_le_left
    · exact (S.chain.fg_endFiltration _).of_le inf_le_right
  have hDD := traceDualLattice_traceDualLattice_aux (traceDualLattice ψF)
    (fun M y => mem_additiveDual_iff_trace ψF hψ M y) hLfg
  rw [← hDD]
  intro w hw
  rw [traceDualLattice_sup] at hw
  obtain ⟨hwQ, hwH⟩ := hw
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hseq := sequence_for_simple S h0 hs q
  rw [traceDualLattice_centralizerLattice S.chain ψF hψ S.b] at hwQ
  rw [hseq.traceDual_simpleHLayer hn ψF hψ (i + 1)] at hwH
  have hDm := hseq.traceDual_simpleHLayer hn ψF hψ i
  obtain ⟨a, ha, p, hp, hap⟩ := Submodule.mem_sup.mp hwH
  obtain ⟨p', hp', ρ, hρ, hpρ⟩ := Submodule.mem_sup.mp hwQ
  obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.mp ha
  -- `ρ − a_β(j)` lies in the range of `a_β` and in `𝔓^{−m}`
  set ρ' := ρ - adjointMap 𝒪[F] S.b j with hρ'
  have hρ'P : ρ' ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) := by
    have : ρ' = p - p' := by
      rw [← hap] at hpρ
      calc ρ' = (p' + ρ) - adjointMap 𝒪[F] S.b j - p' := by rw [hρ']; abel
        _ = p - p' := by rw [hpρ]; abel
    rw [this]
    refine sub_mem (by simpa using hp) (S.chain.endFiltration_antitone (by omega) hp')
  have hρ's : s ρ' = 0 := by
    obtain ⟨u, hu⟩ := hρ
    have hρ'u : ρ' = adjointMap F (subfieldEmbedding F E V βE) (u - j) := by
      rw [map_sub, hβES, hu, hρ']
      rfl
    rw [hρ'u]
    exact s.adjointMap_eq_zero βE (u - j)
  obtain ⟨y, hy, hyρ⟩ := exists_mem_centralizer_mul_adjoint_of_corestriction_eq_zero S hs hβES
    hβE hb s hρ'P hρ's
  -- now `w = p' + a_β(j) + a_β(y)`
  have hw : w = p' + adjointMap 𝒪[F] S.b j + (S.b * y - y * S.b) := by
    rw [hyρ, hρ', ← hpρ]
    abel
  have hxP : x ∈ S.chain.endFiltration ((i + 1 : ℕ) : ℤ) := hx.2
  have h1 : traceCharacter ψF (x * p') = 1 := traceCharacter_eq_one S.chain hψ (by
    simpa only [show ((i + 1 : ℕ) : ℤ) + (1 - ((i + 1 : ℕ) : ℤ)) = 1 by ring] using
      S.chain.mul_mem_endFiltration hxP hp')
  have h2 : traceCharacter ψF (x * adjointMap 𝒪[F] S.b j) = 1 := by
    have hmem : adjointMap 𝒪[F] S.b j ∈ traceDualLattice ψF
        (simpleHLayer S.chain S.n S.b q.tail (i + 1)) := by
      rw [hDm]
      exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hj)
    have := hmem x hx
    rwa [traceCharacter_apply, LinearMap.trace_mul_comm, ← traceCharacter_apply]
  have h3 : traceCharacter ψF (x * (S.b * y - y * S.b)) = 1 := by
    have := horth y hy
    rwa [traceCharacter_apply, LinearMap.trace_mul_comm, ← traceCharacter_apply]
  rw [hw, mul_add, mul_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, h2, h3,
    one_mul, one_mul]

end Langlands.BushnellKutzko.SplitBlocks
