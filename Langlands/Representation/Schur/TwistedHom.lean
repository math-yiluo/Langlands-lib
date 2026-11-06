import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Mathlib.RingTheory.Length

/-! Twisted intertwiners and Hom length consequences of scalar Schur. -/

noncomputable section

namespace Langlands.Schur

universe uK uH uV uW

variable {k : Type uK} [Field k] {H : Type uH} [Group H]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A nonzero intertwiner between irreducibles stays bijective when the source
action is pulled back along a surjective group homomorphism. -/
theorem twistedIntertwiner_bijective
    (ρ : Representation k H V) (σ : Representation k H W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (α : H →* H) (hα : Function.Surjective α)
    (S : V →ₗ[k] W) (hS : S ≠ 0)
    (hcov : ∀ h v, S (ρ (α h) v) = σ h (S v)) :
    Function.Bijective S := by
  let : Representation.IsIrreducible (ρ.comp α) :=
    CuspidalSupport.isIrreducible_comp_of_surjective ρ α hα
  let f : Representation.IntertwiningMap (ρ.comp α) σ :=
    S.intertwiningMap_of_isIntertwiningMap (ρ.comp α) σ hcov
  have hf : f ≠ 0 := by
    intro hz
    exact hS (congrArg Representation.IntertwiningMap.toLinearMap hz)
  exact (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf

/-- The actual representation equivalence obtained from a nonzero twisted map. -/
def twistedIntertwinerEquiv
    (ρ : Representation k H V) (σ : Representation k H W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (α : H →* H) (hα : Function.Surjective α)
    (S : V →ₗ[k] W) (hS : S ≠ 0)
    (hcov : ∀ h v, S (ρ (α h) v) = σ h (S v)) :
    Representation.Equiv (ρ.comp α) σ :=
  (S.intertwiningMap_of_isIntertwiningMap (ρ.comp α) σ hcov).ofBijective
    (twistedIntertwiner_bijective ρ σ α hα S hS hcov)

@[simp] theorem twistedIntertwinerEquiv_apply
    (ρ : Representation k H V) (σ : Representation k H W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (α : H →* H) (hα : Function.Surjective α)
    (S : V →ₗ[k] W) (hS : S ≠ 0)
    (hcov : ∀ h v, S (ρ (α h) v) = σ h (S v)) (v : V) :
    twistedIntertwinerEquiv ρ σ α hα S hS hcov v = S v := rfl

/-- Postcomposing with the inverse of a fixed equivalence identifies the
intertwining space with the source endomorphism space. -/
def intertwiningMapEquivEnd
    {ρ : Representation k H V} {σ : Representation k H W} (e : ρ.Equiv σ) :
    ρ.IntertwiningMap σ ≃ₗ[k] ρ.IntertwiningMap ρ where
  toFun f := e.symm.toIntertwiningMap.comp f
  invFun f := e.toIntertwiningMap.comp f
  left_inv f := by
    ext v
    exact e.apply_symm_apply (f v)
  right_inv f := by
    ext v
    exact e.symm_apply_apply (f v)
  map_add' f g := by
    ext v
    exact map_add e.symm (f v) (g v)
  map_smul' a f := by
    ext v
    exact map_smul e.symm a (f v)

/-- Scalar endomorphisms imply that the endomorphism space has length at most one. -/
theorem length_end_le_one_of_scalar
    (ρ : Representation k H V)
    (hscalar : ∀ f : ρ.IntertwiningMap ρ,
      ∃ c : k, f = c • Representation.IntertwiningMap.id ρ) :
    Module.length k (ρ.IntertwiningMap ρ) ≤ 1 := by
  let L : k →ₗ[k] ρ.IntertwiningMap ρ :=
    LinearMap.toSpanSingleton k _ (Representation.IntertwiningMap.id ρ)
  have hL : Function.Surjective L := by
    intro f
    obtain ⟨c, hc⟩ := hscalar f
    exact ⟨c, hc.symm⟩
  have h := Module.length_le_of_surjective L hL
  simpa only [Module.length_eq_one] using h

/-- Between two irreducibles, scalar Schur on the source bounds Hom length by one.
No finite-dimensionality or algebraic-closure assumption is needed. -/
theorem length_hom_le_one_of_scalar
    (ρ : Representation k H V) (σ : Representation k H W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hscalar : ∀ f : ρ.IntertwiningMap ρ,
      ∃ c : k, f = c • Representation.IntertwiningMap.id ρ) :
    Module.length k (ρ.IntertwiningMap σ) ≤ 1 := by
  classical
  by_cases hz : ∀ f : ρ.IntertwiningMap σ, f = 0
  · have : Subsingleton (ρ.IntertwiningMap σ) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    simp only [Module.length_eq_zero, zero_le]
  · push Not at hz
    obtain ⟨f, hf⟩ := hz
    let e := f.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)
    rw [(intertwiningMapEquivEnd e).length_eq]
    exact length_end_le_one_of_scalar ρ hscalar

/-- A specified nonzero intertwiner forces equivalence of two irreducibles. -/
theorem intertwiningMap_eq_zero_of_not_equiv
    (ρ : Representation k H V) (σ : Representation k H W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hne : ¬ Nonempty (ρ.Equiv σ)) (f : ρ.IntertwiningMap σ) : f = 0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
  · exact (hne ⟨f.ofBijective hf⟩).elim
  · exact hf

/-- Inequivalent irreducibles have a Hom space of length zero. -/
theorem length_hom_eq_zero_of_not_equiv
    (ρ : Representation k H V) (σ : Representation k H W)
    [ρ.IsIrreducible] [σ.IsIrreducible]
    (hne : ¬ Nonempty (ρ.Equiv σ)) :
    Module.length k (ρ.IntertwiningMap σ) = 0 := by
  apply Module.length_eq_zero_iff.mpr
  exact ⟨fun f g => (intertwiningMap_eq_zero_of_not_equiv ρ σ hne f).trans
    (intertwiningMap_eq_zero_of_not_equiv ρ σ hne g).symm⟩

end Langlands.Schur
