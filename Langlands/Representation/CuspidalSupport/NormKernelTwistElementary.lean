import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Representation.Twist.SubquotientProof
import Mathlib.RepresentationTheory.Irreducible

/-!
# Elementary implications and the character endpoint for norm-kernel twists

These derived constructions isolate the formal endpoint of Renard VI.3.2(iii).
They do not assume any finite-dimensionality or prove existence of eigenvectors.
-/

noncomputable section

open scoped NNReal

namespace Langlands.CuspidalSupport

universe uG uI uV uW

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A character trivial on an open common norm kernel is a continuous
unramified character. Continuity is obtained through the discrete quotient. -/
def unramifiedCharacterOfTrivialOnOpenKernel [TopologicalSpace G]
    [IsTopologicalGroup G] {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
    (hH : IsOpen (Plancherel.commonNormKernel ν : Set G))
    (χ : G →* ℂˣ) (hχ : Plancherel.commonNormKernel ν ≤ χ.ker) :
    Plancherel.unramifiedCharacters ν := by
  letI := QuotientGroup.discreteTopology hH
  let ψ : (G ⧸ Plancherel.commonNormKernel ν) →ₜ* ℂˣ :=
    { toMonoidHom := QuotientGroup.lift (Plancherel.commonNormKernel ν) χ hχ
      continuous_toFun := continuous_of_discreteTopology }
  exact Plancherel.quotientCharacterPullback ν ψ

@[simp]
theorem unramifiedCharacterOfTrivialOnOpenKernel_apply [TopologicalSpace G]
    [IsTopologicalGroup G] {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
    (hH : IsOpen (Plancherel.commonNormKernel ν : Set G))
    (χ : G →* ℂˣ) (hχ : Plancherel.commonNormKernel ν ≤ χ.ker) (g : G) :
    (unramifiedCharacterOfTrivialOnOpenKernel ν hH χ hχ).val g = χ g := rfl

/-- A twist by a character trivial on a subgroup restricts to the original
representation. The underlying linear equivalence is unchanged. -/
def restrictEquivOfTwist (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (H : Subgroup G) (χ : G →* ℂˣ) (hχ : H ≤ χ.ker)
    (e : Representation.Equiv (Langlands.twist χ ρ) σ) :
    Representation.Equiv (ρ.comp H.subtype) (σ.comp H.subtype) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' h := by
    ext v
    have hh : χ h = 1 := hχ h.property
    have he := Representation.IntertwiningMap.isIntertwining
      (Langlands.twist χ ρ) σ e.toIntertwiningMap (h : G) v
    change e ((χ h : ℂ) • ρ h v) = σ h (e v) at he
    simpa [hh] using he

/-- An equivalence on a nonzero carrier gives a nonzero intertwiner. -/
theorem exists_nonzero_intertwiner_of_equiv
    {K : Type*} [Monoid K] (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
    [Nontrivial V] (e : Representation.Equiv ρ σ) :
    ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 := by
  refine ⟨e.toIntertwiningMap, ?_⟩
  intro he
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply e.injective
  have hvzero := congrArg (fun f : Representation.IntertwiningMap ρ σ => f v) he
  simpa using hvzero

/-- A nonzero intertwiner from a twist of one irreducible representation to
another is an equivalence. -/
def twistEquivOfNonzeroIntertwiner
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (χ : G →* ℂˣ) (f : Representation.IntertwiningMap (Langlands.twist χ ρ) σ)
    (hf : f ≠ 0) :
    Representation.Equiv (Langlands.twist χ ρ) σ := by
  letI := hσ
  letI : (Langlands.twist χ ρ).IsIrreducible :=
    (Langlands.isIrreducible_twist_iff χ ρ).mpr hρ
  exact f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)

/-- The formal equivalence assembly, once a nonzero restricted intertwiner
has been turned into an unramified twist equivalence. -/
theorem normKernelTwistEquivalence_of_nonzeroIntertwiner [TopologicalSpace G]
    {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [Nontrivial V]
    (hCB : (∃ f : Representation.IntertwiningMap
        (ρ.comp (Plancherel.commonNormKernel ν).subtype)
        (σ.comp (Plancherel.commonNormKernel ν).subtype), f ≠ 0) →
      ∃ χ : Plancherel.unramifiedCharacters ν,
        Nonempty (Representation.Equiv (Langlands.twist χ.val.toMonoidHom ρ) σ)) :
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
  have hBA : (∃ χ : Plancherel.unramifiedCharacters ν,
      Nonempty (Representation.Equiv (Langlands.twist χ.val.toMonoidHom ρ) σ)) →
      Nonempty (Representation.Equiv
        (ρ.comp (Plancherel.commonNormKernel ν).subtype)
        (σ.comp (Plancherel.commonNormKernel ν).subtype)) := by
    rintro ⟨χ, ⟨e⟩⟩
    exact ⟨restrictEquivOfTwist ρ σ _ χ.val.toMonoidHom χ.property e⟩
  have hAC : Nonempty (Representation.Equiv
      (ρ.comp (Plancherel.commonNormKernel ν).subtype)
      (σ.comp (Plancherel.commonNormKernel ν).subtype)) →
      ∃ f : Representation.IntertwiningMap
        (ρ.comp (Plancherel.commonNormKernel ν).subtype)
        (σ.comp (Plancherel.commonNormKernel ν).subtype), f ≠ 0 := by
    rintro ⟨e⟩
    exact exists_nonzero_intertwiner_of_equiv _ _ e
  exact ⟨⟨fun h => hCB (hAC h), hBA⟩, ⟨hAC, fun h => hBA (hCB h)⟩⟩

end Langlands.CuspidalSupport
