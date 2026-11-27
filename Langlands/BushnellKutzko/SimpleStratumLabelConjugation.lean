import Langlands.BushnellKutzko.PureStratumApproximationConjugation
import Langlands.BushnellKutzko.TameCorestrictionProof

/-! # Conjugating perturbations with corestriction in the next filtration step -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SimpleStratumLabel

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

/-- Let `[𝔄,n,r,β]` be simple with `E = F[β]`, let `c, b ∈ 𝔓^{−r}` and suppose that
`s(b) ∈ 𝔓^{1−r}`. Then some `g ∈ U¹(𝔄)` satisfies
`g(β + c + b)g⁻¹ ≡ β + c (mod 𝔓^{1−r})`. -/
theorem exists_unit_conj_add_sub_mem (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {c b : Module.End F V}
    (hc : c ∈ S.chain.endFiltration (-S.r)) (hb : b ∈ S.chain.endFiltration (-S.r))
    (hsb : (s b).restrictScalars F ∈ S.chain.endFiltration (1 - S.r)) :
    ∃ g : (Module.End F V)ˣ, g ∈ S.chain.unitFiltration 1 ∧
      (g : Module.End F V) * (S.b + c + b) * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) -
        (S.b + c) ∈ S.chain.endFiltration (1 - S.r) := by
  have := S.chain.finiteDimensional
  have hE := PureApproximation.normalized_of_generated S hS.1 hβES hβE
  obtain ⟨p, hp, hsp⟩ : ∃ p ∈ S.chain.endFiltration (1 - S.r), s p = s b := by
    have h := (tameCorestriction F V E).2.2 s S.chain hE (1 - S.r)
    have hmem : s b ∈ s '' (S.chain.endFiltration (1 - S.r) : Set (Module.End F V)) := by
      rw [h]
      exact hsb
    obtain ⟨p, hp, hpb⟩ := hmem
    exact ⟨p, hp, hpb⟩
  have hp' : p ∈ S.chain.endFiltration (-S.r) :=
    S.chain.endFiltration_antitone (by omega) hp
  have hz : b - p ∈ S.chain.endFiltration (-S.r) := sub_mem hb hp'
  have hsz : s (b - p) = 0 := by
    rw [map_sub]
    change s b - s p = 0
    rw [hsp, sub_self]
  obtain ⟨y, hy, hyz⟩ :=
    PureApproximation.exists_adjoint_eq_of_corestriction_eq_zero S hS hβES hβE s hz hsz
  obtain ⟨g, hg, hgy⟩ := S.chain.exists_mem_unitFiltration (n := 1) le_rfl hy
  refine ⟨g, hg, ?_⟩
  have hgi0 : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ S.chain.endFiltration 0 := hg.2.1
  have hkey : (g : Module.End F V) * (S.b + c + b) - (S.b + c) * g =
      p + ((b - p) - (S.b * y - y * S.b)) + (y * c - c * y) + y * b := by
    rw [hgy]
    noncomm_ring
  have hmem : (g : Module.End F V) * (S.b + c + b) - (S.b + c) * g ∈
      S.chain.endFiltration (1 - S.r) := by
    rw [hkey, ← hyz, sub_self, add_zero]
    have hyc := S.chain.mul_mem_endFiltration hy hc
    have hcy := S.chain.mul_mem_endFiltration hc hy
    have hyb := S.chain.mul_mem_endFiltration hy hb
    rw [show (1 : ℤ) + -S.r = 1 - S.r by ring] at hyc hyb
    rw [show -S.r + (1 : ℤ) = 1 - S.r by ring] at hcy
    exact add_mem (add_mem hp (sub_mem hyc hcy)) hyb
  have h2 := S.chain.mul_mem_endFiltration hmem hgi0
  rw [add_zero, sub_mul, mul_assoc (S.b + c), Units.mul_inv, mul_one] at h2
  exact h2

end Langlands.BushnellKutzko.SimpleStratumLabel
