import Langlands.BushnellKutzko.SimpleHLayerProducts
import Langlands.BushnellKutzko.SimpleCharacterFormalIntertwining

/-! # Integral and fractional centralizer products for H layers -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The layers `𝔥^k = 𝔥 ∩ 𝔓^k` of a simple stratum are stable under multiplication on either
side by elements of `𝔅 = 𝔄 ∩ B`. -/
theorem mul_mem_simpleHLayer_of_mem_centralizer (S : Stratum 𝒪[F] F V) (hS0 : S.r = 0)
    (hS : S.IsSimple) (q : S.DefiningSequenceChoice) (k : ℕ) {e x : A}
    (he : e ∈ centralizerLattice S.chain S.b 0)
    (hx : x ∈ simpleHLayer S.chain S.n S.b q.tail k) :
    e * x ∈ simpleHLayer S.chain S.n S.b q.tail k ∧
      x * e ∈ simpleHLayer S.chain S.n S.b q.tail k := by
  obtain ⟨-, ⟨-, -, -, -, hQH, -, -, hk⟩, -⟩ := simpleStratumLatticeProperties F V S hS0 hS q
  obtain ⟨⟨-, hleft, hright⟩, -⟩ := hk k
  exact ⟨hleft (Submodule.mul_mem_mul (hQH he) hx), hright (Submodule.mul_mem_mul hx (hQH he))⟩

/-- **Consequences of BK93 (8.2.13).** For `[𝔄, n, 0, β]` simple, `m ≥ 1`, `x, y ∈ 𝔥^m` and
`a ∈ 𝔔^{−1}`, the products `a x y`, `x a y` and `x y a` lie in `𝔥^m`. -/
theorem mul_mul_mem_simpleHLayer_of_inv (S : Stratum 𝒪[F] F V) (hS0 : S.r = 0)
    (hS : S.IsSimple) (q : S.DefiningSequenceChoice) {m : ℕ} (hm : 1 ≤ m) {a x y : A}
    (ha : a ∈ centralizerLattice S.chain S.b (-1))
    (hx : x ∈ simpleHLayer S.chain S.n S.b q.tail m)
    (hy : y ∈ simpleHLayer S.chain S.n S.b q.tail m) :
    a * x * y ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
      x * a * y ∈ simpleHLayer S.chain S.n S.b q.tail m ∧
      x * y * a ∈ simpleHLayer S.chain S.n S.b q.tail m := by
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hseq := sequence_for_simple S hS0 hS q
  have hprop := hseq.properties hn .H
  set X := simpleHLayer S.chain S.n S.b q.tail m with hX
  have hXl : X = SimpleStratumLattice.layer S.chain S.n .H S.b q.tail (m : ℤ) := rfl
  have hsq : X * X ≤ centralizerLattice S.chain S.b 1 * X := by
    rw [hXl]
    exact hseq.layer_mul_layer_le hn m (by exact_mod_cast hm)
  have hfr1 : centralizerLattice S.chain S.b 1 * X = X * centralizerLattice S.chain S.b 1 := by
    rw [hXl]; exact hprop.fractional m (by omega) 1
  have hfrm : centralizerLattice S.chain S.b (-1) * X = X * centralizerLattice S.chain S.b (-1) := by
    rw [hXl]; exact hprop.fractional m (by omega) (-1)
  have hQX : centralizerLattice S.chain S.b 0 * X ≤ X := by
    rw [hXl]; exact SimpleStratumLattice.centralizer_mul_layer_le .H hprop m
  have hXQ : X * centralizerLattice S.chain S.b 0 ≤ X := by
    rw [hXl, ← hprop.fractional m (by omega) 0, ← hXl]; exact hQX
  have hQQ : centralizerLattice S.chain S.b (-1) * centralizerLattice S.chain S.b 1 ≤
      centralizerLattice S.chain S.b 0 := by
    simpa using SimpleStratumLattice.centralizer_mul_le S.chain S.b (-1) 1
  have hQQ' : centralizerLattice S.chain S.b 1 * centralizerLattice S.chain S.b (-1) ≤
      centralizerLattice S.chain S.b 0 := by
    simpa using SimpleStratumLattice.centralizer_mul_le S.chain S.b 1 (-1)
  -- `a X X ⊆ X`
  have h1 : centralizerLattice S.chain S.b (-1) * (X * X) ≤ X := by
    calc centralizerLattice S.chain S.b (-1) * (X * X) ≤
        centralizerLattice S.chain S.b (-1) * (centralizerLattice S.chain S.b 1 * X) :=
          mul_le_mul_right hsq _
      _ = centralizerLattice S.chain S.b (-1) * centralizerLattice S.chain S.b 1 * X := by
          rw [mul_assoc]
      _ ≤ centralizerLattice S.chain S.b 0 * X := mul_le_mul_left hQQ _
      _ ≤ X := hQX
  -- `X X a ⊆ X`
  have h3 : X * X * centralizerLattice S.chain S.b (-1) ≤ X := by
    calc X * X * centralizerLattice S.chain S.b (-1) ≤
        centralizerLattice S.chain S.b 1 * X * centralizerLattice S.chain S.b (-1) :=
          mul_le_mul_left hsq _
      _ = X * (centralizerLattice S.chain S.b 1 * centralizerLattice S.chain S.b (-1)) := by
          rw [hfr1, mul_assoc]
      _ ≤ X * centralizerLattice S.chain S.b 0 := mul_le_mul_right hQQ' _
      _ ≤ X := hXQ
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc]
    exact h1 (Submodule.mul_mem_mul ha (Submodule.mul_mem_mul hx hy))
  · have : X * centralizerLattice S.chain S.b (-1) * X ≤ X := by
      rw [← hfrm, mul_assoc]
      exact h1
    exact this (Submodule.mul_mem_mul (Submodule.mul_mem_mul hx ha) hy)
  · exact h3 (Submodule.mul_mem_mul (Submodule.mul_mem_mul hx hy) ha)

end Langlands.BushnellKutzko.SplitBlocks
