import Langlands.BushnellKutzko.LowerCornerTracePairing
import Langlands.BushnellKutzko.SimpleCharacterForwardRestriction
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof

/-! # Covariance on an intermediate subgroup with a deeper lower corner -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Addition of upper block entries is multiplication of the associated units. -/
theorem blockUnit_add {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0) (y y' : A) :
    blockUnit e₁ e₂ h₂₁ (y + y') = blockUnit e₁ e₂ h₂₁ y * blockUnit e₁ e₂ h₂₁ y' := by
  apply Units.ext
  have hzero : e₁ * y * e₂ * (e₁ * y' * e₂) = 0 := by
    calc
      _ = e₁ * y * (e₂ * e₁) * y' * e₂ := by noncomm_ring
      _ = _ := by rw [h₂₁]; simp
  simp only [Units.val_mul, blockUnit_val, mul_add, add_mul, one_mul, mul_one, hzero, add_zero]
  abel

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The conjugation difference by an upper block unit is the adjoint of its
off-diagonal part. -/
theorem blockUnit_conjugationDifference {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0)
    (β y : A) (he₁ : Commute β e₁) :
    (↑(blockUnit e₁ e₂ h₂₁ y)⁻¹ : A) * β * (blockUnit e₁ e₂ h₂₁ y : A) - β =
      adjointMap 𝒪[F] β (e₁ * y * e₂) := by
  let w := e₁ * y * e₂
  change (1 - w) * β * (1 + w) - β = β * w - w * β
  have hzero : w * β * w = 0 := by
    calc
      w * β * w = e₁ * y * e₂ * (β * e₁) * y * e₂ := by dsimp [w]; noncomm_ring
      _ = e₁ * y * (e₂ * e₁) * β * y * e₂ := by rw [he₁.eq]; noncomm_ring
      _ = 0 := by rw [h₂₁]; simp
  calc
    _ = β * w - w * β - w * β * w := by noncomm_ring
    _ = _ := by rw [hzero, sub_zero]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Upper block conjugation leaves the lower corner unchanged. -/
theorem blockUnit_conj_lowerCorner {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0) (y : A) (k : G) :
    e₂ * (((blockUnit e₁ e₂ h₂₁ y * k * (blockUnit e₁ e₂ h₂₁ y)⁻¹ : G) : A) - 1) * e₁ =
      e₂ * ((k : A) - 1) * e₁ := by
  have hleft : e₂ * (blockUnit e₁ e₂ h₂₁ y : A) = e₂ := by
    rw [blockUnit_val, mul_add, mul_one, ← mul_assoc, ← mul_assoc, h₂₁]
    simp
  have hright : (↑(blockUnit e₁ e₂ h₂₁ y)⁻¹ : A) * e₁ = e₁ := by
    rw [blockUnit_inv_val, sub_mul, one_mul, mul_assoc, h₂₁]
    simp
  let g := blockUnit e₁ e₂ h₂₁ y
  have hproduct : e₂ * ((g : A) * (k : A) * (↑g⁻¹ : A)) * e₁ = e₂ * (k : A) * e₁ := by
    calc
      _ = (e₂ * (g : A)) * (k : A) * ((↑g⁻¹ : A) * e₁) := by noncomm_ring
      _ = _ := by rw [hleft, hright]
  change e₂ * (((g * k * g⁻¹ : G) : A) - 1) * e₁ = e₂ * ((k : A) - 1) * e₁
  simp only [Units.val_mul, mul_sub, sub_mul, mul_one, hproduct]

/-- A depth-`−m` diagonal twist is preserved by integral upper conjugation
on elements with lower corner of depth `m+1`. -/
theorem blockUnit_elementCharacter_conj_eq (L : LatticeChain 𝒪[F] F V)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0) {c y : A} (hc₁ : Commute c e₁) (hc₂ : Commute c e₂)
    (m : ℤ) (hc : c ∈ L.endFiltration (-m)) (hy : y ∈ L.endFiltration 0)
    (k : G) (hk : e₂ * ((k : A) - 1) * e₁ ∈ L.endFiltration (m + 1)) :
    elementCharacter (traceCharacter ψF) c (blockUnit e₁ e₂ h₂₁ y * k *
        (blockUnit e₁ e₂ h₂₁ y)⁻¹) =
      elementCharacter (traceCharacter ψF) c k := by
  let d := c * y - y * c
  have hd : d ∈ L.endFiltration (-m) := by
    exact sub_mem (by simpa using L.mul_mem_endFiltration hc hy)
      (by simpa using L.mul_mem_endFiltration hy hc)
  have hadj : adjointMap 𝒪[F] c (e₁ * y * e₂) = e₁ * d * e₂ := by
    change c * (e₁ * y * e₂) - (e₁ * y * e₂) * c = e₁ * d * e₂
    rw [← mul_assoc c, ← mul_assoc c, hc₁.eq, mul_assoc (e₁ * y) e₂ c, ← hc₂.eq]
    dsimp [d]
    noncomm_ring
  have htr : elementCharacter (traceCharacter ψF) (e₁ * d * e₂) k = 1 := by
    rw [elementCharacter_apply, traceCharacter_apply]
    rw [show e₁ * d * e₂ * ((k : A) - 1) = e₁ * (d * e₂ * ((k : A) - 1)) by noncomm_ring,
      LinearMap.trace_mul_comm, show d * e₂ * ((k : A) - 1) * e₁ = d * (e₂ * ((k : A) - 1) * e₁)
        by noncomm_ring, ← traceCharacter_apply]
    exact traceCharacter_eq_one L hψ (by simpa using L.mul_mem_endFiltration hd hk)
  have hdiff := blockUnit_conjugationDifference h₂₁ c y hc₁
  have heq : (↑(blockUnit e₁ e₂ h₂₁ y)⁻¹ : A) * c * (blockUnit e₁ e₂ h₂₁ y : A) =
      c + e₁ * d * e₂ := by
    rw [hadj] at hdiff
    rw [← hdiff]
    abel
  rw [elementCharacter_conj, heq, elementCharacter_add, htr, mul_one]

/-- The next H group is the intersection of the preceding H group with the
next ambient unit group. -/
theorem simpleHGroup_succ_eq_inf (S : Stratum 𝒪[F] F V) (h0 : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice) {m : ℕ} (hm : 1 ≤ m) :
    H[S,q] (m + 1) = H[S,q] m ⊓ S.chain.unitFiltration (m + 1) := by
  ext g
  constructor
  · intro hg
    exact ⟨simpleHGroup_antitone _ _ _ _ (Nat.le_succ _) hg,
      simpleHGroup_le_unitFiltration _ _ _ _ _ hg⟩
  · rintro ⟨hg, hg'⟩
    exact (simpleHGroup_mem_iff_of_pos S h0 hs q (by omega)).mpr
      ⟨((simpleHGroup_mem_iff_of_pos S h0 hs q hm).mp hg).1, hg'.2.2⟩

/-- A simple character fixed by a unit normalizing its domain has the
conjugation difference of its parameter in the trace dual of that domain. -/
theorem conjugationDifference_mem_traceDual_of_fixed
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF) (m : ℕ)
    (hn : (m : ℤ) < S.n) (hcrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m)
    {g : G} (hg : ∀ k ∈ H[S,q] (m + 1), g * k * g⁻¹ ∈ H[S,q] (m + 1))
    (hfix : g ∈ characterSelfIntertwining θ) :
    (↑g⁻¹ : A) * S.b * (g : A) - S.b ∈ traceDualLattice ψF (Hₗ[S,q] (m + 1)) := by
  have hI := (simpleCharacterIntertwining F V ψF hψ S h0 hs q m hn hcrit θ hθ).1
  have hcov := simpleCharacterCovariance F V ψF hψ S h0 hs q m m hn hn hcrit hcrit
    (by omega) θ hθ g (hI ▸ hfix)
  intro x hx
  obtain ⟨k, _, hkval⟩ := S.chain.exists_mem_unitFiltration (n := m + 1) (by omega) hx.2
  have hkval' : (k : A) - 1 = x := by rw [hkval]; abel
  have hk := (simpleHGroup_mem_iff_of_pos S h0 hs q (m := m + 1) (by omega)).mpr (hkval' ▸ hx)
  have heq := hcov ⟨k, hk⟩ (hg k hk)
  rw [hfix ⟨k, hk⟩ (hg k hk), elementCharacter_apply, hkval'] at heq
  exact mul_left_cancel₀ (Units.ne_zero (θ ⟨k, hk⟩)) (by simpa only [mul_one] using heq.symm)

end Langlands.BushnellKutzko.SplitBlocks
