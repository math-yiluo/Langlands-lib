import Langlands.Representation.Filtration.HomBounds
import Langlands.Representation.Schur.TwistedHom

/-! Hom length and inverse covariance for a supplied twisted piece. -/

noncomputable section

namespace Langlands.Schur

universe uH uV uW

variable {H : Type uH} [Group H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Interpret the covariance of a geometric piece as an actual representation equivalence. -/
def twistedPieceEquiv (τ : Representation ℂ H W) (ρ : Representation ℂ H V)
    (α : H →* H) (T : W ≃ₗ[ℂ] V)
    (hT : ∀ m x, T (τ m x) = ρ (α m) (T x)) : τ.Equiv (ρ.comp α) :=
  Representation.Equiv.mk T (fun m => LinearMap.ext (hT m))

/-- A piece equivalent to a surjective twist of an irreducible has Hom length at most
one into that irreducible when its endomorphisms are scalar. -/
theorem length_hom_le_one_of_twistedPiece
    (τ : Representation ℂ H W) (ρ : Representation ℂ H V) [ρ.IsIrreducible]
    (α : H →* H) (hα : Function.Surjective α) (T : W ≃ₗ[ℂ] V)
    (hT : ∀ m x, T (τ m x) = ρ (α m) (T x))
    (hscalar : ∀ f : ρ.IntertwiningMap ρ,
      ∃ c : ℂ, f = c • Representation.IntertwiningMap.id ρ) :
    HomSpace.length τ ρ ≤ 1 := by
  classical
  let E := twistedPieceEquiv τ ρ α T hT
  let : Representation.IsIrreducible (ρ.comp α) :=
    CuspidalSupport.isIrreducible_comp_of_surjective ρ α hα
  let : τ.IsIrreducible := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    have hsimple := (Representation.irreducible_iff_isSimpleModule_asModule
      (ρ := ρ.comp α)).mp inferInstance
    exact (LinearMap.isSimpleModule_iff_of_bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule τ (ρ.comp α)
        E.toIntertwiningMap) E.bijective).mpr hsimple
  by_cases hz : ∀ f : τ.IntertwiningMap ρ, f = 0
  · have : Subsingleton (τ.IntertwiningMap ρ) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    change Module.length ℂ (τ.IntertwiningMap ρ) ≤ 1
    simp only [Module.length_eq_zero, zero_le]
  · push Not at hz
    obtain ⟨f, hf⟩ := hz
    let e := f.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)
    calc
      HomSpace.length τ ρ = HomSpace.length ρ ρ := HomSpace.length_congr_left ρ e
      _ ≤ 1 := length_end_le_one_of_scalar ρ hscalar

/-- A nonzero map from a twisted piece produces the inverse-direction equivalence
required by the endomorphism dichotomy. -/
def inverseTwistedPieceEquiv
    (τ : Representation ℂ H W) (ρ : Representation ℂ H V) [ρ.IsIrreducible]
    (α : H →* H) (hα : Function.Surjective α) (T : W ≃ₗ[ℂ] V)
    (hT : ∀ m x, T (τ m x) = ρ (α m) (T x))
    (f : τ.IntertwiningMap ρ) (hf : f ≠ 0) : ρ.Equiv (ρ.comp α) := by
  let S : V →ₗ[ℂ] V := f.toLinearMap.comp T.symm.toLinearMap
  have hS : S ≠ 0 := by
    intro h
    apply hf
    ext x
    change f.toLinearMap x = 0
    have hx := LinearMap.congr_fun h (T x)
    simpa only [S, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.zero_apply] using hx
  have hcov : ∀ m y, S (ρ (α m) y) = ρ m (S y) := by
    intro m y
    have hinv : T.symm (ρ (α m) y) = τ m (T.symm y) := by
      apply T.injective
      rw [T.apply_symm_apply, hT, T.apply_symm_apply]
    change f (T.symm (ρ (α m) y)) = ρ m (f (T.symm y))
    rw [hinv]
    exact Representation.IntertwiningMap.isIntertwining τ ρ f m (T.symm y)
  exact (twistedIntertwinerEquiv ρ ρ α hα S hS hcov).symm

end Langlands.Schur
