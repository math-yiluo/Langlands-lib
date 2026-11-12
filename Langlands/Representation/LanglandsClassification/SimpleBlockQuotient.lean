import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Basic.Complex.Basic

/-! # Splitting the retained simple block of an equivariant quotient

An equivariant operator on a quotient which factors through an irreducible
representation upstairs splits every nonzero copy of that representation
on which it acts as the identity.
-/

noncomputable section

namespace Langlands.Classification

universe uG uV uW uX

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
  {χ : Representation ℂ G X}

/-- Let `q : ρ → χ` be surjective and `τ` irreducible. Suppose the
endomorphism `E` of `χ` satisfies `E q = q s p` for maps `p : ρ → τ`
and `s : τ → ρ`. Every nonzero `j : τ → χ` with `E j = j`
then admits an equivariant retraction. No finite-dimensionality or common
carrier universe is assumed. -/
theorem simpleBlockQuotient_retraction
    (hτ : τ.IsIrreducible)
    (q : ρ.IntertwiningMap χ) (hq : Function.Surjective q)
    (s : τ.IntertwiningMap ρ) (p : ρ.IntertwiningMap τ)
    (E : χ.IntertwiningMap χ)
    (hE : ∀ v, E (q v) = q (s (p v)))
    (j : τ.IntertwiningMap χ) (hj : j ≠ 0)
    (hEj : ∀ w, E (j w) = j w) :
    ∃ r : χ.IntertwiningMap τ, r.comp j = Representation.IntertwiningMap.id τ := by
  let := hτ
  have hqs : q.comp s ≠ 0 := by
    intro hz
    apply hj
    ext w
    change j w = 0
    obtain ⟨v, hv⟩ := hq (j w)
    have hs0 := congrArg (fun f : τ.IntertwiningMap χ => f (p v)) hz
    change q (s (p v)) = 0 at hs0
    rw [← hE, hv, hEj] at hs0
    exact hs0
  have hqs_inj : Function.Injective (q.comp s) :=
    (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right hqs
  let qM := Representation.IntertwiningMap.equivLinearMapAsModule ρ χ q
  let pM := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ p
  have hqM : Function.Surjective qM := hq
  have hker : qM.ker ≤ pM.ker := by
    intro v hv
    change V at v
    change p v = 0
    apply hqs_inj
    change q (s (p v)) = q (s 0)
    change q v = 0 at hv
    rw [← hE, hv, map_zero, map_zero, map_zero]
  let fM := (qM.ker.liftQ pM hker).comp
    (qM.quotKerEquivOfSurjective hqM).symm.toLinearMap
  let f : χ.IntertwiningMap τ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule χ τ).symm fM
  have hf : ∀ v, f (q v) = p v := by
    intro v
    change (qM.ker.liftQ pM hker)
      ((qM.quotKerEquivOfSurjective hqM).symm (qM v)) = p v
    erw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  have hqsf : ∀ x, q (s (f x)) = E x := by
    intro x
    obtain ⟨v, rfl⟩ := hq x
    rw [hf, hE]
  have hfj : f.comp j ≠ 0 := by
    intro hz
    apply hj
    ext w
    change j w = 0
    have hs0 := congrArg (fun g : τ.IntertwiningMap τ => g w) hz
    change f (j w) = 0 at hs0
    rw [← hEj, ← hqsf, hs0, map_zero, map_zero]
  let e := (f.comp j).ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero _).resolve_right hfj)
  refine ⟨e.symm.toIntertwiningMap.comp f, ?_⟩
  ext w
  change e.symm (e w) = w
  exact e.symm_apply_apply w

/-- A chosen equivariant retraction onto the retained irreducible block. -/
def simpleBlockQuotientRetraction
    (hτ : τ.IsIrreducible)
    (q : ρ.IntertwiningMap χ) (hq : Function.Surjective q)
    (s : τ.IntertwiningMap ρ) (p : ρ.IntertwiningMap τ)
    (E : χ.IntertwiningMap χ)
    (hE : ∀ v, E (q v) = q (s (p v)))
    (j : τ.IntertwiningMap χ) (hj : j ≠ 0)
    (hEj : ∀ w, E (j w) = j w) :
    χ.IntertwiningMap τ :=
  (simpleBlockQuotient_retraction hτ q hq s p E hE j hj hEj).choose

/-- The chosen map is a left inverse to the given embedding. -/
theorem simpleBlockQuotientRetraction_comp
    (hτ : τ.IsIrreducible)
    (q : ρ.IntertwiningMap χ) (hq : Function.Surjective q)
    (s : τ.IntertwiningMap ρ) (p : ρ.IntertwiningMap τ)
    (E : χ.IntertwiningMap χ)
    (hE : ∀ v, E (q v) = q (s (p v)))
    (j : τ.IntertwiningMap χ) (hj : j ≠ 0)
    (hEj : ∀ w, E (j w) = j w) :
    (simpleBlockQuotientRetraction hτ q hq s p E hE j hj hEj).comp j =
      Representation.IntertwiningMap.id τ :=
  (simpleBlockQuotient_retraction hτ q hq s p E hE j hj hEj).choose_spec

end Langlands.Classification
