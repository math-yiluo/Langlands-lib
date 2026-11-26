import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences

/-! # Changing the ambient character in a twisted induced trace -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

section InductionTwist

variable {G M X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [Group M] [AddCommGroup X] [Module ℂ X]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : G ≃* G) (hθ : Continuous θ) (hθ' : Continuous θ.symm)
  (P : Subgroup G) (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (p : P →* M) (θM : M ≃* M)
  (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x))
  (Ξ : Representation ℂ M X) (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom))

/-- An ambient invariant character that restricts through the Levi projection moves inside
smooth induction, with its induced twisting operator transported by the same equivalence. -/
theorem characterTwistDistribution_induced (ψ : G →* ℂˣ) (hψ : IsOpen (ψ.ker : Set G))
    (hψθ : ∀ g, ψ (θ g) = ψ g) (η : M →* ℂˣ) (hηθ : ∀ m, η (θM m) = η m)
    (hη : ∀ x : P, ψ x = η (p x))
    (h : IsAdmissible (Induction.smoothInduced P (Ξ.comp p))) :
    ∃ h' : IsAdmissible (Induction.smoothInduced P ((twist η Ξ).comp p)),
      characterTwistDistribution ψ hψ
        (twistedDistribution μ _ h (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B).toLinearMap) =
      twistedDistribution μ _ h'
        (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp (twist η Ξ)
          (twistTwistedIntertwiner θM η hηθ B)).toLinearMap := by
  let τ := Induction.smoothInduced P (Ξ.comp p)
  let σ := (twist η Ξ).comp p
  let χ : Induction.SmoothCharacter ℂ G := ⟨ψ, hψ⟩
  let e₀ : (twist (ψ.comp P.subtype) (Ξ.comp p)).Equiv σ :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ X) (fun q => by
      ext x
      change (ψ (q : G) : ℂ) • Ξ (p q) x = (η (p q) : ℂ) • Ξ (p q) x
      rw [hη q])
  let e : (twist ψ τ).Equiv (Induction.smoothInduced P σ) :=
    (Induction.smoothInductionTwistEquiv P χ (Ξ.comp p)).trans (Induction.smoothInducedEquiv P e₀)
  have he (f : Induction.SmoothFunctions P (Ξ.comp p)) (g : G) :
      Induction.eval P σ (e f) g = (ψ g : ℂ) • Induction.eval P (Ξ.comp p) f g := rfl
  have htw : IsAdmissible (twist ψ τ) := (isAdmissible_twist_iff ψ τ hψ).mpr h
  have h' := isAdmissible_of_equiv e htw
  let A := inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B
  let A' := inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp (twist η Ξ)
    (twistTwistedIntertwiner θM η hηθ B)
  refine ⟨h', ?_⟩
  change (twistedDistribution μ τ h A.toLinearMap).comp (characterMultiplyTest ψ hψ) =
    twistedDistribution μ _ h' A'.toLinearMap
  rw [← twistedDistribution_twist_eq_comp μ τ h A.toLinearMap ψ hψ htw]
  refine twistedDistribution_eq_of_equivariant μ _ htw _ h' _ _ e.toLinearEquiv
    (fun g f => e.toIntertwiningMap.isIntertwining _ _ g f) ?_
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change Induction.eval P σ (e (A f)) g = Induction.eval P σ (A' (e f)) g
  rw [he, eval_inducedTwistedIntertwiner, eval_inducedTwistedIntertwiner, he]
  change (ψ g : ℂ) • B (Induction.eval P (Ξ.comp p) f (θ.symm g)) =
    B ((ψ (θ.symm g) : ℂ) • Induction.eval P (Ξ.comp p) f (θ.symm g))
  rw [map_smul, ← hψθ (θ.symm g), MulEquiv.apply_symm_apply]

end InductionTwist

end Langlands.BaseChange
