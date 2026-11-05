import Langlands.Representation.Category.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! # Regularity of prescribed scalar characters and compact quotient unitarity -/

noncomputable section

namespace Langlands

universe uR uG uH uV

section Scalar

variable {R : Type uR} [Field R]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V : Type uV} [AddCommGroup V] [Module R V] [Nontrivial V]

/-- A prescribed scalar character pulled back along a continuous group map has
open kernel whenever the representation is nonzero and smooth. -/
theorem isOpen_ker_of_scalar_action (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (f : H →* G) (hf : Continuous f) (χ : H →* Rˣ)
    (hχ : ∀ h v, ρ (f h) v = (χ h : R) • v) :
    IsOpen (χ.ker : Set H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, hK⟩ := hρ v
  apply χ.ker.isOpen_of_openSubgroup (U := K.comap f hf)
  intro h hh
  apply Units.ext
  apply smul_left_injective R hv
  change (χ h : R) • v = (1 : R) • v
  rw [← hχ, one_smul]
  exact hK ⟨f h, hh⟩

/-- Open kernel gives local constancy of a group homomorphism. The codomain
requires no topology. -/
theorem isLocallyConstant_of_isOpen_character_ker
    (χ : H →* Rˣ) (hχ : IsOpen (χ.ker : Set H)) :
    IsLocallyConstant (χ : H → Rˣ) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro h
  refine ⟨(fun t : H => h⁻¹ * t) ⁻¹' (χ.ker : Set H),
    hχ.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro t ht
    have ht' : (χ h)⁻¹ * χ t = 1 := by
      change χ (h⁻¹ * t) = 1 at ht
      simpa only [map_mul, map_inv] using ht
    exact (inv_mul_eq_one.mp ht').symm

end Scalar

namespace SmoothRep

variable {R : Type uR} [Field R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (π : SmoothRep.{uR, uG, uV} R G) [Nontrivial π]
  {ω : Subgroup.center G →* Rˣ}

/-- A supplied central character of a nonzero smooth representation is smooth,
without irreducibility or admissibility. -/
theorem HasCentralCharacter.isOpen_ker (hω : π.HasCentralCharacter ω) :
    IsOpen (ω.ker : Set (Subgroup.center G)) :=
  isOpen_ker_of_scalar_action π.representation π.isSmooth
    (Subgroup.center G).subtype continuous_subtype_val ω hω

/-- The given scalar character is locally constant on the full group center. -/
theorem HasCentralCharacter.isLocallyConstant (hω : π.HasCentralCharacter ω) :
    IsLocallyConstant (ω : Subgroup.center G → Rˣ) :=
  isLocallyConstant_of_isOpen_character_ker ω (hω.isOpen_ker π)

end SmoothRep

section Norm

variable {H : Type uH} [Group H]

/-- The real multiplicative norm of a complex character. -/
def complexCharacterNorm (χ : H →* ℂˣ) : H →* ℝ where
  toFun h := ‖(χ h : ℂ)‖
  map_one' := by simp
  map_mul' h t := by simp

@[simp] theorem complexCharacterNorm_apply (χ : H →* ℂˣ) (h : H) :
    complexCharacterNorm χ h = ‖(χ h : ℂ)‖ := rfl

variable [TopologicalSpace H]

/-- A continuous complex character unitary on a normal subgroup is unitary
everywhere when the actual group quotient is compact. -/
theorem norm_eq_one_of_compact_quotient
    (χ : H →* ℂˣ) (hχ : Continuous χ)
    (N : Subgroup H) [N.Normal] [CompactSpace (H ⧸ N)]
    (hN : ∀ n ∈ N, ‖(χ n : ℂ)‖ = 1) (h : H) :
    ‖(χ h : ℂ)‖ = 1 := by
  let f : H ⧸ N →* ℝ := QuotientGroup.lift N (complexCharacterNorm χ) hN
  have hf : Continuous f :=
    (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (Units.continuous_val.comp hχ).norm
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (H ⧸ N)).Nonempty) hf.continuousOn
  have hqpos : 0 < f q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change 0 < ‖(χ x : ℂ)‖
    exact norm_pos_iff.mpr (Units.ne_zero _)
  have hsq : f q * f q ≤ f q := by
    have hmax : f (q * q) ≤ f q := hq (Set.mem_univ (q * q))
    simpa only [map_mul] using hmax
  have hqle : f q ≤ 1 := by
    nlinarith
  have hle (x : H) : ‖(χ x : ℂ)‖ ≤ 1 :=
    (hq (Set.mem_univ (QuotientGroup.mk x))).trans hqle
  have hinv := hle h⁻¹
  have hpos : 0 < ‖(χ h : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hinv' : ‖(χ h : ℂ)‖⁻¹ ≤ 1 := by
    simpa only [map_inv, Units.val_inv_eq_inv_val, norm_inv] using hinv
  exact le_antisymm (hle h) ((inv_le_one₀ hpos).mp hinv')

end Norm

end Langlands
