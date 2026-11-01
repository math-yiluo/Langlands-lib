import Langlands.Representation.Filtration.IrreducibleMultiplicityProof
import Langlands.Representation.Filtration.RepresentationLength
import Mathlib.RepresentationTheory.Irreducible

/-! Exact injections and composition-factor comparisons with a simple object. -/

noncomputable section

namespace Langlands

universe uR uG uE uL uP uQ

namespace RepresentationExactComparison

section Lift

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {E : Type uE} {L : Type uL} {P : Type uP}
  [AddCommGroup E] [Module R E] [AddCommGroup L] [Module R L]
  [AddCommGroup P] [Module R P]
  {ρ : Representation R G E} {τ : Representation R G L} {π : Representation R G P}

/-- The actual lift of an intertwiner through an injective intertwiner whose
range contains its image. -/
def liftThroughInjection (i : τ.IntertwiningMap π) (hi : Function.Injective i)
    (f : ρ.IntertwiningMap π)
    (hf : LinearMap.range f.toLinearMap ≤ LinearMap.range i.toLinearMap) :
    ρ.IntertwiningMap τ := by
  let e := LinearEquiv.ofInjective i.toLinearMap hi
  let g : E →ₗ[R] L := e.symm.toLinearMap.comp
    (f.toLinearMap.codRestrict (LinearMap.range i.toLinearMap)
      (fun v => hf ⟨v, rfl⟩))
  have hg (v : E) : i (g v) = f v :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f v, hf ⟨v, rfl⟩⟩)
  refine { toLinearMap := g, isIntertwining' := ?_ }
  intro a
  ext v
  apply hi
  simp only [LinearMap.comp_apply]
  rw [hg, i.isIntertwining, hg, f.isIntertwining]

/-- The lift is an actual factorization of the original intertwiner. -/
theorem injection_liftThroughInjection (i : τ.IntertwiningMap π)
    (hi : Function.Injective i) (f : ρ.IntertwiningMap π)
    (hf : LinearMap.range f.toLinearMap ≤ LinearMap.range i.toLinearMap) (v : E) :
    i (liftThroughInjection i hi f hf v) = f v := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective i.toLinearMap hi).apply_symm_apply ⟨f v, hf ⟨v, rfl⟩⟩)

end Lift

section Exact

variable {k : Type uR} [Field k] {G : Type uG} [Monoid G]
  {E : Type uE} {L : Type uL} {P : Type uP} {Q : Type uQ}
  [AddCommGroup E] [Module k E] [AddCommGroup L] [Module k L]
  [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
  {ρ : Representation k G E} {τ : Representation k G L}
  {π : Representation k G P} {χ : Representation k G Q}

/-- A nonzero map from a simple representation into the middle of an exact
sequence with simple left term either identifies it with the left term or
injects it into the right term. -/
theorem equiv_left_or_injective_right (hρ : ρ.IsIrreducible) (hτ : τ.IsIrreducible)
    (i : τ.IntertwiningMap π) (q : π.IntertwiningMap χ) (f : ρ.IntertwiningMap π)
    (hi : Function.Injective i)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv τ) ∨ Function.Injective (q.comp f) := by
  let := hρ
  let := hτ
  by_cases hqf : q.comp f = 0
  · have hmem : LinearMap.range f.toLinearMap ≤ LinearMap.range i.toLinearMap := by
      rintro _ ⟨v, rfl⟩
      rw [hex]
      exact congrArg (fun h => h v) hqf
    let g := liftThroughInjection i hi f hmem
    have hg : g ≠ 0 := by
      intro hg
      apply hf
      ext v
      have hv := injection_liftThroughInjection i hi f hmem v
      change i (g v) = f v at hv
      rw [hg] at hv
      simpa using hv.symm
    exact Or.inl ⟨g.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero g).resolve_right hg)⟩
  · exact Or.inr ((Representation.IsIrreducible.injective_or_eq_zero (q.comp f)).resolve_right hqf)

end Exact

section Factors

variable {k : Type uR} [Field k] {G : Type uG} [Monoid G]

/-- The sole grade of any zero-to-whole one-slot filtration is the ambient
representation, not merely an object with the same constituent count. -/
def oneSlotGradedEquiv (A : Rep.{uE} k G) (s : ObjectRepFiltration A 1) :
    (s.gradedRepresentation 0).ρ.Equiv A.ρ := by
  change (LengthCriterionProof.quotientRep (s.subrepresentation 0)
    (s.subrepresentation (Fin.last 1))).Equiv A.ρ
  rw [s.subrepresentation_zero, s.subrepresentation_last]
  exact IrreducibleMultiplicityProof.oneStepGradedEquiv A

/-- Multiplicity-sensitive equality of composition factors with one simple
object supplies an actual representation equivalence. -/
theorem nonempty_equiv_of_sameFactors (A : Rep.{uE} k G) (B : Rep.{uL} k G)
    (hA : A.ρ.IsIrreducible) (h : HaveSameJordanHolderFactors A B) :
    Nonempty (A.ρ.Equiv B.ρ) := by
  obtain ⟨n, s, t, hs, _, e, he⟩ := h
  have hn : n = 1 := by
    have hlen : (n : ℕ∞) = 1 :=
      (repLength_eq_of_hasSimpleFactors s hs).symm.trans (repLength_eq_one_iff.mpr hA)
    exact_mod_cast hlen
  subst n
  have he0 : e 0 = 0 := Subsingleton.elim _ _
  obtain ⟨φ⟩ := he 0
  rw [he0] at φ
  exact ⟨(oneSlotGradedEquiv A s).symm.trans (φ.trans (oneSlotGradedEquiv B t))⟩

end Factors

end RepresentationExactComparison

end Langlands
