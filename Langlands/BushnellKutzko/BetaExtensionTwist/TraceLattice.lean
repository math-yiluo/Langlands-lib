import Langlands.BushnellKutzko.AdjointLatticeBounds
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Maximal-ideal trace duals of endomorphism lattices -/

noncomputable section
open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "tr" => LinearMap.trace F V

/-- The trace pairing on the algebra of endomorphisms. -/
def endTracePairing : LinearMap.BilinForm F A :=
  LinearMap.mk₂ F (fun x y => tr (x * y))
    (fun x z y => by rw [add_mul, map_add])
    (fun c x y => by rw [smul_mul_assoc, map_smul])
    (fun x y z => by rw [mul_add, map_add])
    (fun c x y => by rw [mul_smul_comm, map_smul])

@[simp] theorem endTracePairing_apply (x y : A) : endTracePairing x y = tr (x * y) := rfl

theorem endTracePairing_nondegenerate [FiniteDimensional F V] :
    (endTracePairing (F := F) (V := V)).Nondegenerate := by
  have hs : (endTracePairing (F := F) (V := V)).IsSymm :=
    ⟨fun x y => LinearMap.trace_mul_comm F x y⟩
  refine hs.isRefl.nondegenerate_iff_separatingLeft.mpr fun x hx => ?_
  ext v
  by_contra! hv
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one F hv
  have hm : x * ℓ.smulRight v = ℓ.smulRight (x v) := by
    apply LinearMap.ext
    intro w
    simp [Module.End.mul_apply]
  have htr := hx (ℓ.smulRight v)
  rw [endTracePairing_apply, hm, LinearMap.trace_smulRight, hℓ] at htr
  exact one_ne_zero htr

variable [ValuativeRel F]

private def maximalIdealSubmodule : Submodule 𝒪[F] F :=
  Submodule.map (Algebra.linearMap 𝒪[F] F) (𝓂[F] : Submodule 𝒪[F] 𝒪[F])

/-- The dual lattice with respect to the trace and the maximal ideal. -/
def traceLatticeDual (P : Submodule 𝒪[F] A) : Submodule 𝒪[F] A :=
  ⨅ y : P, maximalIdealSubmodule.comap ((endTracePairing.flip (y : A)).restrictScalars 𝒪[F])

theorem mem_traceLatticeDual {P : Submodule 𝒪[F] A} {x : A} :
    x ∈ traceLatticeDual P ↔ ∀ y ∈ P, tr (x * y) ∈ maximalIdealInField 𝒪[F] F := by
  rw [traceLatticeDual, Submodule.mem_iInf]
  exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y y.property⟩

theorem traceLatticeDual_antitone : Antitone (traceLatticeDual (F := F) (V := V)) :=
  fun _ _ h _ hx => mem_traceLatticeDual.mpr fun _ hy => mem_traceLatticeDual.mp hx _ (h hy)

theorem traceLatticeDual_sup (P Q : Submodule 𝒪[F] A) :
    traceLatticeDual (P ⊔ Q) = traceLatticeDual P ⊓ traceLatticeDual Q := by
  apply le_antisymm
  · exact le_inf (traceLatticeDual_antitone le_sup_left) (traceLatticeDual_antitone le_sup_right)
  · intro x hx
    apply mem_traceLatticeDual.mpr
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha' := mem_traceLatticeDual.mp hx.1 _ ha
    have hb' := mem_traceLatticeDual.mp hx.2 _ hb
    rw [mul_add, map_add]
    exact maximalIdealSubmodule.add_mem ha' hb'

theorem le_traceLatticeDual_dual (P : Submodule 𝒪[F] A) :
    P ≤ traceLatticeDual (traceLatticeDual P) := by
  intro x hx
  apply mem_traceLatticeDual.mpr
  intro y hy
  rw [LinearMap.trace_mul_comm]
  exact mem_traceLatticeDual.mp hy x hx

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem trace_adjoint_mul_swap (β x y : A) :
    tr (adjointMap F β x * y) = -tr (x * adjointMap F β y) := by
  change tr ((β * x - x * β) * y) = -tr (x * (β * y - y * β))
  rw [sub_mul, mul_sub, map_sub, map_sub, neg_sub,
    LinearMap.trace_mul_comm F (β * x) y, ← mul_assoc y β x,
    LinearMap.trace_mul_comm F (y * β) x, mul_assoc x β y]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The commutator image is the trace-annihilator of the commutator kernel. -/
theorem range_adjoint_eq_traceAnnilator [FiniteDimensional F V] (β : A) :
    (adjointMap F β).range =
      (adjointMap F β).ker.dualAnnihilator.comap (endTracePairing (F := F) (V := V)) := by
  let a := adjointMap F β
  let e := endTracePairing.toDual (endTracePairing_nondegenerate (F := F) (V := V))
  change a.range = a.ker.dualAnnihilator.comap e.toLinearMap
  have hle : a.range ≤ a.ker.dualAnnihilator.comap e.toLinearMap := by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    intro z hz
    change tr (a x * z) = 0
    rw [trace_adjoint_mul_swap, (LinearMap.mem_ker.mp hz : a z = 0), mul_zero, map_zero, neg_zero]
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq a.ker
  have h' := a.finrank_range_add_finrank_ker
  omega

/-- Double trace duality for a finitely generated submodule. -/
theorem traceLatticeDual_dual_of_fg [FiniteDimensional F V] {P : Submodule 𝒪[F] A}
    (hP : P.FG) : traceLatticeDual (traceLatticeDual P) = P := by
  refine le_antisymm ?_ (le_traceLatticeDual_dual P)
  intro x hx
  by_contra h
  obtain ⟨φ, hφ, hxφ⟩ := separates_fg_submodule (K := F) P hP h
  let e := endTracePairing.toDual (endTracePairing_nondegenerate (F := F) (V := V))
  let y := e.symm φ
  have hy (z : A) : tr (y * z) = φ z := by
    change e (e.symm φ) z = φ z
    rw [e.apply_symm_apply]
  have hy' : y ∈ traceLatticeDual P := mem_traceLatticeDual.mpr fun z hz => by
    rw [hy]
    exact hφ z hz
  apply hxφ
  rw [← hy, LinearMap.trace_mul_comm]
  exact mem_traceLatticeDual.mp hx y hy'

/-- Intersections of bounded finitely generated lattices dualize to sums. -/
theorem traceLatticeDual_inf_of_fg [FiniteDimensional F V] {P Q : Submodule 𝒪[F] A}
    (hP : P.FG) (hQ : Q.FG) (hP' : (traceLatticeDual P).FG) (hQ' : (traceLatticeDual Q).FG) :
    traceLatticeDual (P ⊓ Q) = traceLatticeDual P ⊔ traceLatticeDual Q := by
  have h : traceLatticeDual (traceLatticeDual P ⊔ traceLatticeDual Q) = P ⊓ Q := by
    rw [traceLatticeDual_sup, traceLatticeDual_dual_of_fg hP, traceLatticeDual_dual_of_fg hQ]
  rw [← h, traceLatticeDual_dual_of_fg (hP'.sup hQ')]

/-- Trace duality for any step of a lattice chain. -/
theorem traceLatticeDual_endFiltration (L : LatticeChain 𝒪[F] F V) (n : ℤ) :
    traceLatticeDual (L.endFiltration n) = L.endFiltration (1 - n) := by
  let := L.finiteDimensional
  ext x
  exact mem_traceLatticeDual.trans (L.mem_endFiltration_iff_trace_mul n x).symm

/-- When the centralizer projection preserves the radical, the dual of a
sublattice of the radical containing its centralizer part is the sum of the
order and its part in the commutator image. -/
theorem traceLatticeDual_eq_sup_adj_range (L : LatticeChain 𝒪[F] F V)
    (β : A) (H : Submodule 𝒪[F] A) (hH : H ≤ L.endFiltration 1)
    (hQ : centralizerLattice L β 1 ≤ H) (p : A →ₗ[F] A)
    (hp : ∀ x, adjointMap F β (p x) = 0)
    (hfix : ∀ x, adjointMap F β x = 0 → p x = x)
    (hP : ∀ x ∈ L.endFiltration 1, p x ∈ L.endFiltration 1) :
    traceLatticeDual H =
      (traceLatticeDual H ⊓ (adjointMap F β).range.restrictScalars 𝒪[F]) ⊔ L.endFiltration 0 := by
  let := L.finiteDimensional
  let e := endTracePairing.toDual (endTracePairing_nondegenerate (F := F) (V := V))
  have h0 : L.endFiltration 0 ≤ traceLatticeDual H := by
    have h := traceLatticeDual_antitone hH
    simpa only [traceLatticeDual_endFiltration, sub_self] using h
  refine le_antisymm ?_ (sup_le inf_le_left h0)
  intro x hx
  let b := e.symm ((endTracePairing x).comp p)
  have hb (y : A) : tr (b * y) = tr (x * p y) := by
    change e (e.symm ((endTracePairing x).comp p)) y = tr (x * p y)
    rw [e.apply_symm_apply]
    rfl
  have hb0 : b ∈ L.endFiltration 0 := by
    rw [← sub_self (1 : ℤ), ← traceLatticeDual_endFiltration]
    apply mem_traceLatticeDual.mpr
    intro y hy
    rw [hb]
    exact mem_traceLatticeDual.mp hx _ (hQ ⟨hP y hy, hp y⟩)
  refine Submodule.mem_sup.mpr ⟨x - b, ⟨sub_mem hx (h0 hb0), ?_⟩, b, hb0, sub_add_cancel _ _⟩
  change x - b ∈ (adjointMap F β).range
  rw [range_adjoint_eq_traceAnnilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  intro y hy
  change tr ((x - b) * y) = 0
  rw [sub_mul, map_sub, hb, hfix y (LinearMap.mem_ker.mp hy), sub_self]

end Langlands.BushnellKutzko
