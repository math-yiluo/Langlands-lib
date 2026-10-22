import Langlands.Weil.Representation.Operations
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # Invariants of exact sequences of complex representations -/

noncomputable section

namespace Langlands.Weil

universe uG uV uU uT

section Helpers

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {U : Type uU} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  {T : Type uT} [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G U}
  {τ : Representation ℂ G T}

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ T] in
/-- Rank additivity for the actual linear maps in a short exact sequence. -/
theorem exactSequence_finrank
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap) :
    Module.finrank ℂ U = Module.finrank ℂ V + Module.finrank ℂ T := by
  let eV := (LinearEquiv.ofInjective f.toLinearMap hf).trans
    (LinearEquiv.ofEq _ _ hfg)
  let eT := g.toLinearMap.quotKerEquivOfSurjective hg
  have hV := eV.finrank_eq
  have hT := eT.finrank_eq
  have hdim := (LinearMap.ker g.toLinearMap).finrank_quotient_add_finrank
  rw [hT, ← hV] at hdim
  exact hdim.symm.trans (Nat.add_comm _ _)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ T] in
/-- Determinant multiplicativity, using the invariant kernel and its quotient. -/
theorem exactSequence_det
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    (w : G) :
    LinearMap.det (σ w) = LinearMap.det (ρ w) * LinearMap.det (τ w) := by
  let W := LinearMap.ker g.toLinearMap
  have hW : W ≤ W.comap (σ w) := by
    intro u hu
    change g (σ w u) = 0
    change g u = 0 at hu
    rw [g.isIntertwining, hu, map_zero]
  let eV : V ≃ₗ[ℂ] W := (LinearEquiv.ofInjective f.toLinearMap hf).trans
    (LinearEquiv.ofEq _ _ hfg)
  have eV_apply (v : V) : (eV v : U) = f v := rfl
  have hconjV :
      eV.toLinearMap ∘ₗ ρ w ∘ₗ eV.symm.toLinearMap = (σ w).restrict hW := by
    ext x
    change (eV (ρ w (eV.symm x)) : U) = σ w (x : U)
    rw [eV_apply, f.isIntertwining, ← eV_apply, eV.apply_symm_apply]
  have hdetV : LinearMap.det ((σ w).restrict hW) = LinearMap.det (ρ w) := by
    rw [← hconjV, LinearMap.det_conj]
  let eT : (U ⧸ W) ≃ₗ[ℂ] T := g.toLinearMap.quotKerEquivOfSurjective hg
  have hconjT :
      eT.toLinearMap ∘ₗ W.mapQ W (σ w) hW ∘ₗ eT.symm.toLinearMap = τ w := by
    ext t
    obtain ⟨u, rfl⟩ := hg t
    change eT (W.mapQ W (σ w) hW (eT.symm (g u))) = τ w (g u)
    have heT : eT.symm (g u) = W.mkQ u :=
      g.toLinearMap.quotKerEquivOfSurjective_symm_apply hg u
    rw [heT]
    exact Representation.IntertwiningMap.isIntertwining σ τ g w u
  have hdetT : LinearMap.det (W.mapQ W (σ w) hW) = LinearMap.det (τ w) := by
    rw [← hconjT, LinearMap.det_conj]
  rw [LinearMap.det_eq_det_mul_det W (σ w) hW, hdetV, hdetT]

end Helpers

/-- The complete published exact-sequence target, with independent universes. -/
theorem representationExactSequenceInvariants :
    RepresentationExactSequenceInvariants.{uG, uV, uU, uT} := by
  intro G _ V _ _ _ U _ _ _ T _ _ _ ρ σ τ f g hf hg hfg
  exact ⟨exactSequence_finrank f g hf hg hfg, exactSequence_det f g hf hg hfg⟩

end Langlands.Weil
