import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Smooth.Schur.Proof

/-! # Twisted character lines and central characters under transport -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

universe uG uV uW

section Algebraic

variable {G : Type uG} [Group G] {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An equivalence with a twist of a nonzero representation of central character `χ`
having the same central character forces the twisting character to be trivial on the centre. -/
theorem center_le_ker_of_equiv_twist_same_centralCharacter [Nontrivial V]
    {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    {χ : Subgroup.center G →* ℂˣ} (hρ : HasCentralCharacterRep ρ χ)
    (hπ : HasCentralCharacterRep π χ) {ψ : G →* ℂˣ} (e : π.Equiv (twist ψ ρ)) :
    Subgroup.center G ≤ ψ.ker := by
  intro g hg
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let z : Subgroup.center G := ⟨g, hg⟩
  have h := (hπ.of_equiv e) z v
  change (ψ g : ℂ) • ρ g v = (χ z : ℂ) • v at h
  have h' := hρ z v
  change ρ g v = (χ z : ℂ) • v at h'
  rw [h', smul_smul] at h
  have hc := smul_left_injective ℂ hv h
  exact MonoidHom.mem_ker.mpr (Units.ext (mul_right_cancel₀ (χ z).ne_zero
    (hc.trans (one_mul _).symm)))

private def equivCompAut (θ : G ≃* G) {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} (e : ρ.Equiv π) :
    Representation.Equiv (ρ.comp θ.toMonoidHom) (π.comp θ.toMonoidHom) :=
  Representation.Equiv.mk e.toLinearEquiv (fun g => e.isIntertwining' (θ g))

end Algebraic

section Line

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant] {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- On equivalent irreducible admissible representations, arbitrary twisting isomorphisms
produce proportional twisted distributions. The equivalence need not intertwine the
chosen twisting operators. -/
theorem exists_twistedDistribution_eq_smul_of_equiv (θ : G ≃* G)
    {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible) (hπ : IsAdmissible π) (e : ρ.Equiv π)
    (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) (A' : π.Equiv (π.comp θ.toMonoidHom)) :
    ∃ a : ℂ, twistedDistribution μ π hπ A'.toLinearMap =
      a • twistedDistribution μ ρ hρ A.toLinearMap := by
  let B : ρ.Equiv (ρ.comp θ.toMonoidHom) := (e.trans A').trans (equivCompAut θ e.symm)
  let T : ρ.IntertwiningMap ρ := A.symm.toIntertwiningMap.comp B.toIntertwiningMap
  obtain ⟨a, ha, _⟩ := admissibleSchur_scalarEndomorphism ρ hρ hirr T
  have hB : B.toLinearMap = a • A.toLinearMap := by
    ext v
    have h := congrArg (fun f : ρ.IntertwiningMap ρ => f v) ha
    change A.symm (B v) = a • v at h
    change B v = a • A v
    exact (A.apply_symm_apply _).symm.trans ((congrArg A h).trans (map_smul A.toLinearEquiv a v))
  have he := twistedDistribution_eq_of_equivariant μ π hπ ρ hρ A'.toLinearMap B.toLinearMap
    e.symm.toLinearEquiv (fun g w => e.symm.toIntertwiningMap.isIntertwining _ _ g w) (by
      intro w
      change e.symm (A' w) = e.symm (A' (e (e.symm w)))
      rw [e.apply_symm_apply])
  rw [hB, twistedDistribution_smul] at he
  exact ⟨a, he⟩

end Line

end Langlands.BaseChange
