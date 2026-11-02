import Langlands.Global.Arithmetic.RamifiedTwistIsolationReductionStatement

noncomputable section

universe u

namespace Langlands.Global

/-- The two arithmetic existence inputs imply the existing isolation target. -/
theorem ramifiedTwistIsolationOfInputs :
    RamifiedTwistIsolationOfInputsStatement.{u} := by
  intro hGlobal hLocal K _ _ S T hST η r hη
  classical
  choose ζ hζorder hζdeep using fun w : {w // w ∈ T} => hLocal K w.1 (r w)
  let U := S ∪ T
  let θ : (w : {w // w ∈ U}) → (FiniteCompletion K w.1)ˣ →ₜ* ℂˣ :=
    fun w => if hw : w.1 ∈ S then η ⟨w.1, hw⟩
      else ζ ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩
  have hθorder (w : {w // w ∈ U}) :
      ∃ n : ℕ, 0 < n ∧ θ w ^ n = 1 := by
    dsimp [θ]
    split_ifs with hw
    · exact hη ⟨w.1, hw⟩
    · exact hζorder ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩
  choose n hn hθn using hθorder
  let N : ℕ := ∏ w : {w // w ∈ U}, n w
  have hN : 0 < N := Finset.prod_pos fun w _ => hn w
  have hθN (w : {w // w ∈ U}) : θ w ^ N = 1 := by
    have hd : n w ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ w)
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hθn w]
    ext x
    simp
  obtain ⟨χ, hχorder, hχfin, hχinf⟩ :=
    hGlobal K U N hN θ 1 hθN (by ext x; simp)
  refine ⟨χ, ⟨2 * N, by omega, hχorder⟩, ?_, hχinf, ?_⟩
  · intro w
    have hwU : w.1 ∈ U := Finset.mem_union_left _ w.2
    simpa only [θ, dite_eq_left w.2] using hχfin ⟨w.1, hwU⟩
  · intro w
    have hwNotS : w.1 ∉ S := fun hw => Finset.disjoint_left.mp hST hw w.2
    have hwU : w.1 ∈ U := Finset.mem_union_right _ w.2
    have hComponent : χ.finiteComponent w.1 = ζ w := by
      simpa only [θ, dite_eq_right hwNotS] using hχfin ⟨w.1, hwU⟩
    rw [hComponent]
    exact hζdeep w

end Langlands.Global
