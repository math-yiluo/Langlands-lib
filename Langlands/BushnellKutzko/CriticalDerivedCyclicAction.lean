import Langlands.BushnellKutzko.CriticalDerivedCyclicAlgebra
import Langlands.BushnellKutzko.CriticalDerivedCyclicBasis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Transport of the free cyclic action -/

noncomputable section

open ValuativeRel Polynomial

namespace Langlands.BushnellKutzko.CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- A field unit acting as an endomorphism unit. -/
abbrev scalarEndUnit (π : Fˣ) : (Module.End F V)ˣ :=
  Units.map (algebraMap F (Module.End F V)).toMonoidHom π

theorem scalarEndUnit_commutes (π : Fˣ) (x : (Module.End F V)ˣ) :
    Commute (scalarEndUnit π) x := by
  apply Units.ext
  exact Algebra.commutes (π : F) (x : Module.End F V)

section Transport

variable [ValuativeRel F]
  {C : LatticeChain 𝒪[F] F V} {Q : F[X]} {g h f : ℕ} {π : Fˣ} {a : ℤ}
  (M : CyclicAlgebra Q h f π a) {z τ : Module.End F V} (B : CyclicBasis C g h f z τ)

namespace CyclicBasis

/-- The free module over the root algebra, with one copy per cyclic generator. -/
abbrev Free := (Σ i : Fin g, Fin (B.count i)) →₀ M.A

/-- Transport the rectangular power bases on all summands to the cyclic splitting basis. -/
def transport : B.Free M ≃ₗ[F] V :=
  (M.basis.smulTower' Finsupp.basisSingleOne).equiv B.basis (Equiv.refl _)

theorem transport_single (t : CyclicIndex B.count h f) :
    B.transport M (Finsupp.single t.1 ((M.T : M.A) ^ (t.2.1 : ℕ) * (M.U : M.A) ^ (t.2.2 : ℕ))) =
      B.basis t := by
  have h := (M.basis.smulTower' Finsupp.basisSingleOne).equiv_apply t B.basis (Equiv.refl _)
  simpa only [transport, Module.Basis.smulTower'_apply, Finsupp.coe_basisSingleOne,
    Finsupp.smul_single, smul_eq_mul, mul_one, M.basis_apply, Equiv.refl_apply] using h

/-- The scalar action of the root algebra on the free module, transported to `V`. -/
def action : M.A →ₐ[F] Module.End F V :=
  ((B.transport M).conjAlgEquiv F).toAlgHom.comp (Algebra.lsmul F F (B.Free M))

/-- The two operators obtained from the transported unit roots. -/
abbrev actionU : (Module.End F V)ˣ := Units.map (B.action M).toMonoidHom M.U

abbrev actionT : (Module.End F V)ˣ := Units.map (B.action M).toMonoidHom M.T

theorem action_apply (x : M.A) (w : B.Free M) :
    B.action M x (B.transport M w) = B.transport M (x • w) := by
  change B.transport M (x • (B.transport M).symm (B.transport M w)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem actionU_eval_zero : aeval (B.actionU M : Module.End F V) Q = 0 := by
  change aeval (B.action M (M.U : M.A)) Q = 0
  rw [aeval_algHom_apply, M.eval_zero, map_zero]

theorem actionT_carry : B.actionT M ^ h = scalarEndUnit π * B.actionU M ^ a := by
  let φ := Units.map (B.action M).toMonoidHom
  have h := congrArg φ M.carry
  rw [map_pow, map_mul, map_zpow] at h
  apply h.trans
  congr 1
  apply Units.ext
  exact (B.action M).commutes _

theorem action_commutes : Commute (B.actionT M) (B.actionU M) :=
  ((Commute.all M.T M.U).map (Units.map (B.action M).toMonoidHom))

/-- The lifted operators agree with the original short iterates on every generator. -/
theorem action_basis (hh : 0 < h) (hf : 0 < f) (t : CyclicIndex B.count h f) :
    B.basis t = ((B.actionT M : Module.End F V) ^ (t.2.1 : ℕ))
      (((B.actionU M : Module.End F V) ^ (t.2.2 : ℕ)) (B.generators t.1.1 t.1.2)) := by
  let t₀ : CyclicIndex B.count h f := (t.1, ⟨0, hh⟩, ⟨0, hf⟩)
  have hv : B.transport M (Finsupp.single t.1 (1 : M.A)) = B.generators t.1.1 t.1.2 := by
    have h := (B.transport_single M t₀).trans (B.basis_apply t₀)
    simpa only [t₀, pow_zero, mul_one, Module.End.one_apply] using h
  change B.basis t = ((B.action M (M.T : M.A)) ^ (t.2.1 : ℕ))
    (((B.action M (M.U : M.A)) ^ (t.2.2 : ℕ)) (B.generators t.1.1 t.1.2))
  rw [← map_pow, ← map_pow, ← Module.End.mul_apply, ← map_mul, ← hv, action_apply,
    Finsupp.smul_single, smul_eq_mul, mul_one, transport_single]

end CyclicBasis

end Transport

end Langlands.BushnellKutzko.CriticalDerived
