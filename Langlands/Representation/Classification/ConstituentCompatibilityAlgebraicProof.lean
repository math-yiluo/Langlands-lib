import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Twist.AlgebraProof

/-!
# Algebraic compatibility of irreducible constituents

Common twists preserve constituent relations, canonical heads and socles give
isomorphism uniqueness, and scalar characters pass through constituent maps.
-/

namespace Langlands.Classification

universe uG uV uF uC

section Twist

variable {G : Type uG} [Group G]
variable {V W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
variable (χ : G →* ℂˣ) (ρ : Representation ℂ G V) (π : Representation ℂ G W)

theorem isIrreducibleQuotient_twist_iff :
    IsIrreducibleQuotient (twist χ ρ) (twist χ π) ↔
      IsIrreducibleQuotient ρ π := by
  constructor
  · rintro ⟨hπ, q, hq⟩
    exact ⟨(isIrreducible_twist_iff χ π).mp hπ, untwistIntertwining χ q, hq⟩
  · rintro ⟨hπ, q, hq⟩
    exact ⟨(isIrreducible_twist_iff χ π).mpr hπ, twistIntertwining χ q, hq⟩

theorem isIrreducibleSubrepresentation_twist_iff :
    IsIrreducibleSubrepresentation (twist χ ρ) (twist χ π) ↔
      IsIrreducibleSubrepresentation ρ π := by
  constructor
  · rintro ⟨hπ, j, hj⟩
    exact ⟨(isIrreducible_twist_iff χ π).mp hπ, untwistIntertwining χ j, hj⟩
  · rintro ⟨hπ, j, hj⟩
    exact ⟨(isIrreducible_twist_iff χ π).mpr hπ, twistIntertwining χ j, hj⟩

theorem IsIrreducibleHead.of_twist
    (h : IsIrreducibleHead (twist χ ρ) (twist χ π)) :
    IsIrreducibleHead ρ π := by
  obtain ⟨hπ, q, hq, hu⟩ := h
  refine ⟨(isIrreducible_twist_iff χ π).mp hπ, untwistIntertwining χ q, hq, ?_⟩
  intro W' _ _ π' hπ' q' hq'
  exact hu W' (twist χ π') ((isIrreducible_twist_iff χ π').mpr hπ')
    (twistIntertwining χ q') hq'

theorem isIrreducibleHead_twist_iff :
    IsIrreducibleHead (twist χ ρ) (twist χ π) ↔ IsIrreducibleHead ρ π := by
  refine ⟨IsIrreducibleHead.of_twist χ ρ π, fun h => ?_⟩
  apply IsIrreducibleHead.of_twist χ⁻¹ (twist χ ρ) (twist χ π)
  simpa only [twist_inv_twist] using h

theorem IsIrreducibleSocle.of_twist
    (h : IsIrreducibleSocle (twist χ ρ) (twist χ π)) :
    IsIrreducibleSocle ρ π := by
  obtain ⟨hπ, j, hj, hu⟩ := h
  refine ⟨(isIrreducible_twist_iff χ π).mp hπ, untwistIntertwining χ j, hj, ?_⟩
  intro W' _ _ π' hπ' j' hj'
  exact hu W' (twist χ π') ((isIrreducible_twist_iff χ π').mpr hπ')
    (twistIntertwining χ j') hj'

theorem isIrreducibleSocle_twist_iff :
    IsIrreducibleSocle (twist χ ρ) (twist χ π) ↔ IsIrreducibleSocle ρ π := by
  refine ⟨IsIrreducibleSocle.of_twist χ ρ π, fun h => ?_⟩
  apply IsIrreducibleSocle.of_twist χ⁻¹ (twist χ ρ) (twist χ π)
  simpa only [twist_inv_twist] using h

end Twist

/-- Algebraic twist compatibility for every group and arbitrary module carriers. -/
theorem twistConstituentCompatibilityFor (G : Type uG) [Group G] :
    TwistConstituentCompatibilityFor.{uG, uV} G := by
  intro V W _ _ _ _ ρ π χ
  exact ⟨isIrreducibleQuotient_twist_iff χ ρ π,
    isIrreducibleSubrepresentation_twist_iff χ ρ π,
    isIrreducibleHead_twist_iff χ ρ π, isIrreducibleSocle_twist_iff χ ρ π⟩

/-- Two irreducible heads or socles of the same representation are equivalent. -/
theorem constituentIsomorphismUniquenessFor (G : Type uG) [Group G] :
    ConstituentIsomorphismUniquenessFor.{uG, uV} G := by
  intro V W W' _ _ _ _ _ _ ρ π π'
  constructor
  · intro h h'
    obtain ⟨e⟩ := h.nonempty_headEquiv
    obtain ⟨e'⟩ := h'.nonempty_headEquiv
    exact ⟨e.symm.trans e'⟩
  · intro h h'
    obtain ⟨e⟩ := h.nonempty_socleEquiv
    obtain ⟨e'⟩ := h'.nonempty_socleEquiv
    exact ⟨e.trans e'.symm⟩

section ScalarCharacter

variable {G : Type uG} [Group G] {C : Type uC} [Group C]
variable {V W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {π : Representation ℂ G W}
variable {z : C →* G} {ω : C →* ℂˣ}

/-- A scalar character passes through a surjective intertwiner. -/
theorem HasScalarCharacter.of_surjective (h : HasScalarCharacter ρ z ω)
    (q : ρ.IntertwiningMap π) (hq : Function.Surjective q) :
    HasScalarCharacter π z ω := by
  intro c w
  obtain ⟨v, rfl⟩ := hq w
  rw [← q.isIntertwining, h c v, map_smul]

/-- A scalar character pulls back along an injective intertwiner. -/
theorem HasScalarCharacter.of_injective (h : HasScalarCharacter ρ z ω)
    (j : π.IntertwiningMap ρ) (hj : Function.Injective j) :
    HasScalarCharacter π z ω := by
  intro c w
  apply hj
  rw [j.isIntertwining, h c (j w), map_smul]

end ScalarCharacter

/-- Central-character compatibility over every field, including rank zero. -/
theorem glConstituentCentralCharacterFor (F : Type uF) [Field F] (n : ℕ) :
    GLConstituentCentralCharacterFor.{uV, uF} F n := by
  intro V W _ _ _ _ ρ π ω χ
  refine ⟨?_, ?_, ?_⟩
  · rintro h ⟨_, q, hq⟩
    exact h.of_surjective q hq
  · rintro h ⟨_, j, hj⟩
    exact h.of_injective j hj
  · intro h z v
    change ((χ (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin n) z)) : ℂˣ) : ℂ) •
      ρ (Matrix.GeneralLinearGroup.scalar (Fin n) z) v =
      (((ω * χ ^ n) z : ℂˣ) : ℂ) • v
    rw [h z v, Matrix.GeneralLinearGroup.det_scalar]
    simp [smul_smul, mul_comm]

/-- The exact published all-fields, all-positive-ranks algebraic target. -/
theorem allPadicGLAlgebraicConstituentCompatibility :
    AllPadicGLAlgebraicConstituentCompatibility.{uV, uF} := by
  intro p _ F n _
  exact ⟨twistConstituentCompatibilityFor _,
    constituentIsomorphismUniquenessFor _, glConstituentCentralCharacterFor _ n⟩

end Langlands.Classification
