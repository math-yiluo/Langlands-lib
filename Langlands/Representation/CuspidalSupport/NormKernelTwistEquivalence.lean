import Langlands.Representation.CuspidalSupport.NormKernelTwistAlgebra
import Langlands.Representation.CuspidalSupport.NormKernelTwistElementary

/-!
# Generic norm-kernel twist equivalence

This internal assembly has explicit finite-index and scalar-centre assumptions.
The actual rational-point theorem must establish these assumptions separately.
-/

noncomputable section

open scoped NNReal

namespace Langlands.CuspidalSupport

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The unramified character and twist equivalence obtained from a nonzero
restricted intertwiner under the finite-index scalar-centre hypotheses. -/
def unramifiedTwistEquivOfRestrictedIntertwiner
    {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
    (hH : IsOpen (Plancherel.commonNormKernel ν : Set G))
    [(Plancherel.commonNormKernel ν ⊔ Subgroup.center G : Subgroup G).FiniteIndex]
    (hcomm : commutator G ≤ Plancherel.commonNormKernel ν)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hρz : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v, ρ z v = c • v)
    (hσz : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ w, σ z w = c • w)
    (f : Representation.IntertwiningMap
      (ρ.comp (Plancherel.commonNormKernel ν).subtype)
      (σ.comp (Plancherel.commonNormKernel ν).subtype)) (hf : f ≠ 0) :
    Σ χ : Plancherel.unramifiedCharacters ν,
      Representation.Equiv (Langlands.twist χ.val.toMonoidHom ρ) σ := by
  apply Classical.choice
  obtain ⟨χ, hχ, t, ht⟩ :=
    exists_twistIntertwiningMap_of_restrictedHom_nonzero
      ρ σ (Plancherel.commonNormKernel ν) hcomm hρz hσz f hf
  refine ⟨⟨unramifiedCharacterOfTrivialOnOpenKernel ν hH χ hχ, ?_⟩⟩
  have hchar :
      (unramifiedCharacterOfTrivialOnOpenKernel ν hH χ hχ).val.toMonoidHom = χ := by
    ext g
    rfl
  rw [hchar]
  exact twistEquivOfNonzeroIntertwiner ρ σ hρ hσ χ t ht

/-- A finite-index scalar-centre input makes isomorphic norm-kernel restrictions,
an unramified twist equivalence, and a nonzero restricted intertwiner equivalent. -/
theorem normKernelTwistEquivalence_of_finiteIndex_scalar
    {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
    (hH : IsOpen (Plancherel.commonNormKernel ν : Set G))
    [(Plancherel.commonNormKernel ν ⊔ Subgroup.center G : Subgroup G).FiniteIndex]
    (hcomm : commutator G ≤ Plancherel.commonNormKernel ν)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hρz : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v, ρ z v = c • v)
    (hσz : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ w, σ z w = c • w) :
    (Nonempty (Representation.Equiv
        (ρ.comp (Plancherel.commonNormKernel ν).subtype)
        (σ.comp (Plancherel.commonNormKernel ν).subtype)) ↔
      ∃ χ : Plancherel.unramifiedCharacters ν,
        Nonempty (Representation.Equiv (Langlands.twist χ.val.toMonoidHom ρ) σ)) ∧
    (Nonempty (Representation.Equiv
        (ρ.comp (Plancherel.commonNormKernel ν).subtype)
        (σ.comp (Plancherel.commonNormKernel ν).subtype)) ↔
      ∃ f : Representation.IntertwiningMap
        (ρ.comp (Plancherel.commonNormKernel ν).subtype)
        (σ.comp (Plancherel.commonNormKernel ν).subtype), f ≠ 0) := by
  have := hρ
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  apply normKernelTwistEquivalence_of_nonzeroIntertwiner ν ρ σ
  rintro ⟨f, hf⟩
  let e := unramifiedTwistEquivOfRestrictedIntertwiner
    ν hH hcomm ρ σ hρ hσ hρz hσz f hf
  exact ⟨e.1, ⟨e.2⟩⟩

end Langlands.CuspidalSupport
