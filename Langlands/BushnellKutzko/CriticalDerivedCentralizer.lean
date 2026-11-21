import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.StratumEquivalenceResidue

/-! # The centralizer comparison for the critical derived stratum -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

namespace CriticalDerived

universe uF uV uE uK

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "[" x "," y "]ₐ" => x * y - y * x

section Corestriction

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (s : TameCorestriction 𝒪[F] F E V)

/-- A corestriction, with its values viewed in the ambient endomorphism space. -/
def ambientCorestriction : Module.End F V →+ Module.End F V where
  toFun x := (s x).restrictScalars F
  map_zero' := by change (s.toAddMonoidHom 0).restrictScalars F = _; rw [map_zero]; rfl
  map_add' x y := by
    change (s.toAddMonoidHom (x + y)).restrictScalars F = _
    rw [map_add]
    rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
@[simp] theorem ambientCorestriction_apply (x : Module.End F V) :
    ambientCorestriction s x = (s x).restrictScalars F := rfl

variable (hE : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer)
  {γE : E} (hγE : Algebra.adjoin F ({γE} : Set E) = ⊤)

local notation "γ" => subfieldEmbedding F E V γE
local notation "t" => ambientCorestriction s

include hE in
 theorem ambientCorestriction_mem {m : ℤ} {x : Module.End F V} (hx : x ∈ P m) : t x ∈ P m := by
  have h : s x ∈ s '' (P m : Set (Module.End F V)) := ⟨x, hx, rfl⟩
  rw [(tameCorestriction F V E).2.2 s 𝓛 hE m] at h
  exact h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
theorem ambientCorestriction_adjoint (x : Module.End F V) : t [γ, x]ₐ = 0 := by
  change (s (adjointMap F γ x)).restrictScalars F = 0
  rw [s.adjointMap_eq_zero]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
include hγE in
theorem ambientCorestriction_commutator {x y : Module.End F V} (hy : Commute y γ) :
    t [x, y]ₐ = [t x, y]ₐ := by
  obtain ⟨Y, rfl⟩ := exists_restrictScalars_of_commute hγE hy
  rw [map_sub]
  have h1 : s (x * Y.restrictScalars F) = s x * Y := s.map_mul_right x Y
  have h2 : s (Y.restrictScalars F * x) = Y * s x := s.map_mul_left Y x
  rw [ambientCorestriction_apply, ambientCorestriction_apply, h1, h2]
  rfl

include hE hγE in
/-- Fourth adjoint sequence, with one degree of error, including the scalar case. -/
theorem exists_adjoint_correction (d j : ℤ)
    (hk : criticalExponent 𝓛 γ ≤ ((d - 1 : ℤ) : WithBot ℤ))
    {z : Module.End F V} (hz : z ∈ P (d + j)) (hsz : t z ∈ P (d + j + 1)) :
    ∃ u ∈ P (j + 1), z - [γ, u]ₐ ∈ P (d + j + 1) := by
  by_cases hscalar : ∃ a : F, algebraMap F E a = γE
  · obtain ⟨a, ha⟩ := hscalar
    have hγ : γ = algebraMap F (Module.End F V) a := by rw [← ha, AlgHom.commutes]
    have heq := (tameCorestriction F V E).2.2 s 𝓛 hE (d + j + 1)
    have h1 : s z ∈ s '' (P (d + j + 1) : Set (Module.End F V)) := heq ▸ hsz
    obtain ⟨z', hz', hzz'⟩ := h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have hsurj := s.surjective_of_clearing 𝓛 hE hϖ0
      (fun x => 𝓛.exists_uniformizer_pow_mem_endFiltration hϖ x 0)
    have hker : z' - z ∈ LinearMap.ker s.toLinearMap := by
      rw [LinearMap.mem_ker, map_sub, s.toLinearMap_apply, s.toLinearMap_apply, hzz', sub_self]
    rw [← s.range_adjointMap_eq_ker γE hγE hsurj] at hker
    obtain ⟨x, hx⟩ := hker
    have h0 : adjointMap F γ x = 0 := by
      rw [hγ]
      change [algebraMap F (Module.End F V) a, x]ₐ = 0
      rw [Algebra.commutes, sub_self]
    rw [h0, eq_comm, sub_eq_zero] at hx
    refine ⟨0, zero_mem _, ?_⟩
    rw [mul_zero, zero_mul, sub_zero, sub_zero, ← hx]
    exact hz'
  · have h := adjointExactness F V E 𝓛 γE hγE hscalar hE
    have h4 := (h.2.2.2.2 s (j + 1) (d - 1) 1 hk le_rfl).2.2.2
    obtain ⟨-, -, -, -, -, -, -, -, -, hmid⟩ := h4
    have hm : j + 1 + (d - 1) = d + j := by omega
    have hsz' : (s z).restrictScalars F ∈
        (centralizerLattice 𝓛 γ (j + 1 + (d - 1) + 1)).toAddSubgroup := by
      rw [hm]
      refine ⟨hsz, ?_⟩
      change [γ, (s z).restrictScalars F]ₐ = 0
      exact sub_eq_zero.mpr (restrictScalars_commute (s z) γE).eq.symm
    obtain ⟨u, hu, hzu⟩ := (hmid z (hm.symm ▸ hz)).mp hsz'
    refine ⟨u, centralizerLattice_mul_adjointLattice_le 𝓛 γ _ _ hu, ?_⟩
    change z - [γ, u]ₐ ∈ P (j + 1 + (d - 1) + 1) at hzu
    rwa [hm] at hzu

end Corestriction

section Comparison

variable {β γ b a : Module.End F V} {d : ℤ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
/-- Transport from the perturbed centralizer to the original one, followed by corestriction. -/
theorem approx_original_centralizer
    (hb : b ∈ P d) (hβγ : β = γ + b)
    (s : Module.End F V →+ Module.End F V) (ha : a = s b)
    (hs_mem : ∀ {n : ℤ} {x : Module.End F V}, x ∈ P n → s x ∈ P n)
    (hs_adj : ∀ x, s [γ, x]ₐ = 0)
    (hs_comm : ∀ (x y : Module.End F V), Commute y γ → s [x, y]ₐ = [s x, y]ₐ)
    (hγ : ∀ j (x : Module.End F V), [γ, x]ₐ ∈ P (d + j) →
      ∃ y, Commute y γ ∧ x - y ∈ P (j + 1))
    {j : ℤ} {x : Module.End F V} (hx : x ∈ P j) (hxc : Commute x β) :
    ∃ y ∈ P j, Commute y γ ∧ x - y ∈ P (j + 1) ∧ [a, y]ₐ ∈ P (d + j + 1) := by
  have h1 : [γ, x]ₐ = -[b, x]ₐ := by
    calc
      _ = [β, x]ₐ - [b, x]ₐ := by rw [hβγ]; noncomm_ring
      _ = _ := by rw [hxc.eq, sub_self, zero_sub]
  obtain ⟨y, hyγ, hxy⟩ := hγ j x (by rw [h1]; exact neg_mem (commutator_mem_endFiltration 𝓛 hb hx))
  have hy : y ∈ P j := by
    have h := sub_mem hx (𝓛.endFiltration_antitone (show j ≤ j + 1 by omega) hxy)
    rwa [sub_sub_cancel] at h
  have h2 : [β, x]ₐ = [γ, x]ₐ + [b, y]ₐ + [b, x - y]ₐ := by
    rw [hβγ]
    noncomm_ring
  have h3 : [a, y]ₐ = -s [b, x - y]ₐ := by
    have h := congrArg s h2
    rw [sub_eq_zero.mpr hxc.eq.symm, map_zero, map_add, map_add, hs_adj, zero_add,
      hs_comm _ _ hyγ, ← ha] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  refine ⟨y, hy, hyγ, hxy, ?_⟩
  rw [h3, add_assoc]
  exact neg_mem (hs_mem (commutator_mem_endFiltration 𝓛 hb hxy))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
/-- If the derived commutator vanishes on the graded piece, the symbol is in the perturbed
centralizer. The two corrections use adjoint exactness at different critical depths. -/
theorem approx_perturbed_centralizer
    (hb : b ∈ P d) (hβγ : β = γ + b)
    (s : Module.End F V →+ Module.End F V) (ha : a = s b)
    (hs_comm : ∀ (x y : Module.End F V), Commute y γ → s [x, y]ₐ = [s x, y]ₐ)
    (hU : ∀ j (z : Module.End F V), z ∈ P (d + j) → s z ∈ P (d + j + 1) →
      ∃ u ∈ P (j + 1), z - [γ, u]ₐ ∈ P (d + j + 1))
    (hβ : ∀ j (x : Module.End F V), [β, x]ₐ ∈ P (d + j + 1) →
      ∃ y, Commute y β ∧ x - y ∈ P (j + 1))
    {j : ℤ} {x : Module.End F V} (hx : x ∈ P j) (hxc : Commute x γ)
    (hxa : [a, x]ₐ ∈ P (d + j + 1)) : ∃ y ∈ P j, Commute y β ∧ x - y ∈ P (j + 1) := by
  obtain ⟨u, hu, hzu⟩ := hU j [b, x]ₐ (commutator_mem_endFiltration 𝓛 hb hx)
    (by rwa [hs_comm _ _ hxc, ← ha])
  have h1 : [β, x - u]ₐ = ([b, x]ₐ - [γ, u]ₐ) - [b, u]ₐ := by
    calc
      _ = [γ, x]ₐ + (([b, x]ₐ - [γ, u]ₐ) - [b, u]ₐ) := by rw [hβγ]; noncomm_ring
      _ = _ := by rw [hxc.eq, sub_self, zero_add]
  have h2 : [β, x - u]ₐ ∈ P (d + j + 1) := by
    rw [h1]
    exact sub_mem hzu (by rw [add_assoc]; exact commutator_mem_endFiltration 𝓛 hb hu)
  obtain ⟨y, hyβ, hxy⟩ := hβ j (x - u) h2
  have hxy' : x - y ∈ P (j + 1) := by
    have h := add_mem hxy hu
    rwa [show x - u - y + u = x - y by abel] at h
  have hy := sub_mem hx (𝓛.endFiltration_antitone (show j ≤ j + 1 by omega) hxy')
  rw [sub_sub_cancel] at hy
  exact ⟨y, hy, hyβ, hxy'⟩

end Comparison

end CriticalDerived

end Langlands.BushnellKutzko
