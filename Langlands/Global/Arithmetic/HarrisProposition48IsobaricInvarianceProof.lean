import Langlands.Global.Arithmetic.HarrisProposition48IsobaricInvarianceStatement

/-! # The isobaric invariance step in Harris's Proposition 4.8

A proof of `Proposition48IsobaricInvarianceStatement` from the Euler constituent-recovery
clause of the supplied `CuspidalSpectralRigidityStatement`.
-/

noncomputable section

universe uV

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Unramified

/-- Two finite enumerations related by a bijection of their index sets enumerate the same
multiset, with multiplicities. -/
private theorem univ_map_eq_of_equiv {α : Type*} {p q : ℕ} (c : Fin p → α) (d : Fin q → α)
    (e : Fin p ≃ Fin q) (h : ∀ i, c i = d (e i)) :
    Finset.univ.val.map c = Finset.univ.val.map d := by
  have hc : c = d ∘ e := funext h
  subst hc
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Harris's Proposition 4.8, isobaric invariance step: the Euler constituent-recovery clause of
cuspidal spectral rigidity turns spectral systems attached to `D` and to `D.galoisConj σ`
with equal Euler polynomials outside a finite set into the multiset equality
`D.galoisConj σ = D`. -/
theorem proposition48IsobaricInvariance : Proposition48IsobaricInvarianceStatement.{uV} := by
  intro hR F K _ _ _ _ _ σ D s t hs ht hst
  obtain ⟨p, c, hc, s₀, hs₀, hs₀s⟩ := hs
  obtain ⟨q, d, hd, t₀, ht₀, ht₀t⟩ := ht
  obtain ⟨e, he⟩ :=
    hR.2.2 K p q c d s₀ t₀ hs₀ ht₀ ((hs₀s.trans hst).trans ht₀t.symm)
  exact hd.symm.trans ((univ_map_eq_of_equiv c d e he).symm.trans hc)

end Langlands.Global.Harris
