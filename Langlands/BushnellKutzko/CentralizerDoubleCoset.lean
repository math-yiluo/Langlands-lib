import Langlands.BushnellKutzko.SimpleStratumGroups
import Langlands.BushnellKutzko.SplittingBasis

/-! # Centralizer filtrations from a double coset `J B_β^× J`

For `β ∈ A = End_F(V)` write `B_β^×` for the units commuting with `β` and
`𝔔^t = 𝔓^t ∩ B_β` (`centralizerLattice`). If a set of units is `J B_β^× J` for a subgroup
`J ⊆ U¹(𝔄)`, then `𝔔^t + 𝔓^{t+1}` is recovered from that set as the additive span of its
elements lying in `𝔓^t`, plus `𝔓^{t+1}`.
-/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem commute_of_mem_centralizerLattice {L : LatticeChain 𝒪[F] F V} {β x : A} {t : ℤ}
    (hx : x ∈ centralizerLattice L β t) : β * x = x * β := by
  have h := hx.2
  rw [SetLike.mem_coe, LinearMap.mem_ker] at h
  change β * x - x * β = 0 at h
  exact sub_eq_zero.mp h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_centralizerLattice_of_commute {L : LatticeChain 𝒪[F] F V} {β x : A} {t : ℤ}
    (hx : x ∈ L.endFiltration t) (hc : β * x = x * β) : x ∈ centralizerLattice L β t := by
  refine ⟨hx, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  change β * x - x * β = 0
  rw [hc, sub_self]

/-- Every element of `𝔓^t ∩ B_β` is the difference of two units of `B_β` lying in `𝔓^t`:
`x = (x + ϖ^l) − ϖ^l` for a power `ϖ^l` of a uniformizer of `F` in `𝔓^t` with `−ϖ^l` not an
eigenvalue of `x`. -/
theorem exists_units_sub_eq_of_mem_centralizerLattice [FiniteDimensional F V]
    (L : LatticeChain 𝒪[F] F V) (β : A) {t : ℤ} {x : A}
    (hx : x ∈ centralizerLattice L β t) :
    ∃ g h : G, g ∈ centralizerUnitGroup β ∧ h ∈ centralizerUnitGroup β ∧
      (g : A) ∈ L.endFiltration t ∧ (h : A) ∈ L.endFiltration t ∧ x = g - h := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let l₀ : ℕ := t.toNat
  let c : ℕ → F := fun l => (algebraMap 𝒪[F] F ϖ) ^ (l₀ + l)
  have hcinj : Function.Injective c := by
    intro a b hab
    have h : ϖ ^ (l₀ + a) = ϖ ^ (l₀ + b) := by
      apply IsFractionRing.injective 𝒪[F] F
      simpa [c, map_pow] using hab
    have := pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero h
    omega
  have hfin : Set.Finite {l : ℕ | x.HasEigenvalue (-c l)} := by
    refine (x.finite_hasEigenvalue.preimage ?_).subset fun l hl => hl
    intro a _ b _ hab
    exact hcinj (neg_injective hab)
  obtain ⟨l, hl⟩ := hfin.infinite_compl.nonempty
  have hc0 : c l ≠ 0 := by
    simp only [c]
    exact pow_ne_zero _ (fun h => hϖ.ne_zero (IsFractionRing.injective 𝒪[F] F (by simpa using h)))
  have hunit : IsUnit (x + c l • (1 : A)) := by
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    apply hl
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at hv
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hv
  have hscal : c l • (1 : A) ∈ L.endFiltration t := by
    have h : c l • (1 : A) ∈ L.endFiltration (L.period * ((l₀ + l : ℕ) : ℤ)) := by
      intro i v hv
      rw [LinearMap.smul_apply, Module.End.one_apply,
        show c l = (ϖ : F) ^ (((l₀ + l : ℕ) : ℤ)) from (zpow_natCast (ϖ : F) (l₀ + l)).symm,
        L.zpow_smul_mem_iff hϖ]
      simpa using hv
    have hle : t ≤ L.period * ((l₀ + l : ℕ) : ℤ) := by
      have hp : (1 : ℤ) ≤ L.period := by exact_mod_cast L.period_pos
      have : t ≤ (l₀ : ℤ) := Int.self_le_toNat t
      push_cast
      nlinarith
    exact L.endFiltration_antitone hle h
  have hcomm_scal : β * (c l • (1 : A)) = (c l • (1 : A)) * β := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hunit' : IsUnit (c l • (1 : A)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr hc0).map _
  refine ⟨hunit.unit, hunit'.unit, ?_, ?_, ?_, ?_, ?_⟩
  · change β * (x + c l • (1 : A)) = (x + c l • (1 : A)) * β
    rw [mul_add, add_mul, commute_of_mem_centralizerLattice hx, hcomm_scal]
  · exact hcomm_scal
  · exact add_mem hx.1 hscal
  · exact hscal
  · simp

/-- If `I = J B_β^× J` with `J ⊆ U¹(𝔄)`, then `𝔔^t + 𝔓^{t+1}` is the additive span of the
elements of `I` lying in `𝔓^t`, plus `𝔓^{t+1}`. -/
theorem centralizerLattice_sup_eq_span [FiniteDimensional F V] (L : LatticeChain 𝒪[F] F V)
    (β : A) (J : Subgroup G) (hJ : J ≤ L.unitFiltration 1) {I : Set G}
    (hI : I = (J : Set G) * (centralizerUnitGroup β : Set G) * (J : Set G)) (t : ℤ) :
    centralizerLattice L β t ⊔ L.endFiltration (t + 1) =
      Submodule.span 𝒪[F] {x : A | ∃ g ∈ I, (g : A) = x ∧ x ∈ L.endFiltration t} ⊔
        L.endFiltration (t + 1) := by
  apply le_antisymm
  · refine sup_le (fun x hx => ?_) le_sup_right
    obtain ⟨g, h, hg, hh, hgt, hht, rfl⟩ := exists_units_sub_eq_of_mem_centralizerLattice L β hx
    have hmem (k : G) (hk : k ∈ centralizerUnitGroup β) (hkt : (k : A) ∈ L.endFiltration t) :
        (k : A) ∈ Submodule.span 𝒪[F] {x : A | ∃ g ∈ I, (g : A) = x ∧ x ∈ L.endFiltration t} := by
      apply Submodule.subset_span
      refine ⟨k, ?_, rfl, hkt⟩
      rw [hI]
      exact Set.mem_mul.mpr ⟨k, Set.mem_mul.mpr ⟨1, J.one_mem, k, hk, one_mul k⟩, 1, J.one_mem,
        mul_one k⟩
    exact Submodule.mem_sup_left (sub_mem (hmem g hg hgt) (hmem h hh hht))
  · refine sup_le (Submodule.span_le.mpr ?_) le_sup_right
    rintro _ ⟨g, hgI, rfl, hgt⟩
    rw [hI] at hgI
    obtain ⟨jb, hjb, j₂, hj₂, rfl⟩ := Set.mem_mul.mp hgI
    obtain ⟨j₁, hj₁, b, hb, rfl⟩ := Set.mem_mul.mp hjb
    have h₁ := hJ hj₁
    have h₂ := hJ hj₂
    have hbt : (b : A) ∈ L.endFiltration t := by
      have hb' : (b : A) = ((j₁⁻¹ : G) : A) * (((j₁ * b * j₂ : G)) : A) * ((j₂⁻¹ : G) : A) := by
        simp only [Units.val_mul]
        rw [show ((j₁⁻¹ : G) : A) * ((j₁ : A) * (b : A) * (j₂ : A)) * ((j₂⁻¹ : G) : A) =
            (((j₁⁻¹ : G) : A) * (j₁ : A)) * (b : A) * ((j₂ : A) * ((j₂⁻¹ : G) : A)) by
          noncomm_ring]
        rw [Units.inv_mul, Units.mul_inv, one_mul, mul_one]
      rw [hb']
      have h := L.mul_mem_endFiltration (L.mul_mem_endFiltration h₁.2.1 hgt) h₂.2.1
      simpa using h
    have hbB : (b : A) ∈ centralizerLattice L β t := mem_centralizerLattice_of_commute hbt hb
    have hdiff : (((j₁ * b * j₂ : G)) : A) - b ∈ L.endFiltration (t + 1) := by
      simp only [Units.val_mul]
      rw [show (j₁ : A) * (b : A) * (j₂ : A) - (b : A) =
          ((j₁ : A) - 1) * ((b : A) * (j₂ : A)) + (b : A) * ((j₂ : A) - 1) by noncomm_ring]
      refine add_mem ?_ ?_
      · have h := L.mul_mem_endFiltration h₁.2.2 (L.mul_mem_endFiltration hbt h₂.1)
        rwa [add_zero, add_comm] at h
      · exact L.mul_mem_endFiltration hbt h₂.2.2
    rw [show (((j₁ * b * j₂ : G)) : A) = (b : A) + ((((j₁ * b * j₂ : G)) : A) - b) by abel]
    exact add_mem (Submodule.mem_sup_left hbB) (Submodule.mem_sup_right hdiff)

/-- Two elements whose centralizer double cosets `J₁ B_{β₁}^× J₁` and `J₂ B_{β₂}^× J₂`, with
`J₁, J₂ ⊆ U¹(𝔄)`, coincide have `𝔔₁^t + 𝔓^{t+1} = 𝔔₂^t + 𝔓^{t+1}` for every `t ∈ ℤ`. -/
theorem centralizerLattice_sup_eq_of_doubleCoset_eq [FiniteDimensional F V]
    (L : LatticeChain 𝒪[F] F V) (β₁ β₂ : A) (J₁ J₂ : Subgroup G)
    (hJ₁ : J₁ ≤ L.unitFiltration 1) (hJ₂ : J₂ ≤ L.unitFiltration 1)
    (h : (J₁ : Set G) * (centralizerUnitGroup β₁ : Set G) * (J₁ : Set G) =
      (J₂ : Set G) * (centralizerUnitGroup β₂ : Set G) * (J₂ : Set G)) (t : ℤ) :
    centralizerLattice L β₁ t ⊔ L.endFiltration (t + 1) =
      centralizerLattice L β₂ t ⊔ L.endFiltration (t + 1) := by
  rw [centralizerLattice_sup_eq_span L β₁ J₁ hJ₁ rfl t,
    centralizerLattice_sup_eq_span L β₂ J₂ hJ₂ rfl t, h]

end Langlands.BushnellKutzko
