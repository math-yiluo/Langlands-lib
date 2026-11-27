import Langlands.VirtualRepresentation.Weil.GroupTransport
import Langlands.Weil.Representation.IsomorphismInvarianceProof
import Langlands.Weil.Representation.TwistClasses
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous irreducible classes of a group quotient

Inflation identifies the continuous irreducible complex classes of `G ⧸ N`
with the classes of `G` whose kernel contains `N`. This uses the quotient
topology and retains the rank and the action of characters of the quotient.
-/

noncomputable section

set_option autoImplicit false

universe uG uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- A subgroup acts trivially on an isomorphism class if it is contained in
the kernel of any representative. -/
def IsomorphismClasses.IsTrivialOn (c : IsomorphismClasses.{0, uG, uV} ℂ G)
    (N : Subgroup G) : Prop := by
  refine Quotient.liftOn c (fun A => N ≤ A.representation.ker) ?_
  intro A B h
  obtain ⟨e⟩ := (show IsIsomorphic A B from h)
  exact congrArg (N ≤ ·) (Weil.IsomorphismInvariance.ker_eq e)

@[simp]
theorem classOf_isTrivialOn (A : FiniteRepresentation.{0, uG, uV} ℂ G) (N : Subgroup G) :
    (classOf A).IsTrivialOn N ↔ N ≤ A.representation.ker := Iff.rfl

variable (N : Subgroup G) [N.Normal]

local notation "π" => QuotientGroup.mk' N

/-- Factor an actual representation through the quotient on its original
carrier. -/
def descendQuotient (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hA : N ≤ A.representation.ker) :
    FiniteRepresentation.{0, uG, uV} ℂ (G ⧸ N) :=
  of (QuotientGroup.lift N A.representation hA)

@[simp]
theorem descendQuotient_mk (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hA : N ≤ A.representation.ker) (g : G) :
    (descendQuotient N A hA).representation (π g) = A.representation g := rfl

variable [TopologicalSpace G]

theorem isContinuous_descendQuotient {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : N ≤ A.representation.ker) (hc : A.IsContinuous) :
    (descendQuotient N A hA).IsContinuous := by
  let B := descendQuotient N A hA
  let : TopologicalSpace (Module.End ℂ B) := moduleTopology ℂ (Module.End ℂ B)
  change Continuous B.representation
  exact (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr hc

private def inflateClass
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ (G ⧸ N) =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible) :=
  VirtualRepresentation.ExactGrothendieckGroup.restrictClassWith π _ _
    (fun A hA => ⟨isContinuous_restrict π QuotientGroup.continuous_mk hA.1,
      (isIrreducible_restrict_iff π (QuotientGroup.mk'_surjective N) A).mpr hA.2⟩) c

private theorem forget_inflateClass
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ (G ⧸ N) =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    forgetPropertyClass _ (inflateClass N c) = restrictClass π (forgetPropertyClass _ c) :=
  Quotient.inductionOn c fun _ => rfl

private def inflateRanked {n : ℕ} (c : ContinuousIrreducibleClasses.{uG, uV} (G ⧸ N) n) :
    {d : ContinuousIrreducibleClasses.{uG, uV} G n //
      (forgetPropertyClass _ d.val).IsTrivialOn N} := by
  refine ⟨⟨inflateClass N c.val, ?_⟩, ?_⟩
  · rw [forget_inflateClass, classRank_restrictClass]
    exact c.property
  · rw [forget_inflateClass]
    generalize forgetPropertyClass _ c.val = c'
    induction c' using Quotient.inductionOn with
    | h A =>
      change (classOf (restrict π A)).IsTrivialOn N
      rw [classOf_isTrivialOn]
      intro g hg
      change A.representation (π g) = 1
      have hg' : π g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
      rw [hg', map_one]

omit [TopologicalSpace G] in
private theorem restrictClass_mk_injective :
    Function.Injective (restrictClass.{0, uG, uG, uV} (K := ℂ) π) := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro A B h
  obtain ⟨e⟩ := (classOf_eq_iff (restrict π A) (restrict π B)).mp h
  apply (classOf_eq_iff A B).mpr
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun q => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact e.isIntertwining' g

/-- Inflation along the quotient map gives a rank-preserving class bijection
onto the classes on which the normal subgroup acts trivially. -/
def continuousIrreducibleQuotientEquiv (n : ℕ) :
    ContinuousIrreducibleClasses.{uG, uV} (G ⧸ N) n ≃
      {d : ContinuousIrreducibleClasses.{uG, uV} G n //
        (forgetPropertyClass _ d.val).IsTrivialOn N} := by
  refine _root_.Equiv.ofBijective (inflateRanked N) ⟨?_, ?_⟩
  · intro c d h
    apply Subtype.ext
    apply forgetPropertyClass_injective _
    apply restrictClass_mk_injective N
    simpa only [inflateRanked, forget_inflateClass] using
      congrArg (fun a => forgetPropertyClass _ a.val.val) h
  · rintro ⟨c, hc⟩
    obtain ⟨A, hA⟩ := Quotient.exists_rep c.val
    have hclass : classOf A.val = forgetPropertyClass _ c.val :=
      congrArg (forgetPropertyClass _) hA
    have hN : N ≤ A.val.representation.ker := by
      rwa [← hclass, classOf_isTrivialOn] at hc
    let B := descendQuotient N A.val hN
    have hB : B.IsContinuous ∧ B.IsIrreducible :=
      ⟨isContinuous_descendQuotient N hN A.property.1,
        (isIrreducible_restrict_iff π (QuotientGroup.mk'_surjective N) B).mp A.property.2⟩
    have hrank : B.rank = n := (congrArg classRank hclass).trans c.property
    refine ⟨⟨Quotient.mk _ ⟨B, hB⟩, hrank⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply forgetPropertyClass_injective _
    change classOf (restrict π B) = forgetPropertyClass _ c.val
    rw [← hclass]
    exact (classOf_eq_iff _ _).mpr ⟨Representation.Equiv.refl A.val.representation⟩

/-- The underlying ordinary isomorphism class is restriction along the
quotient map. -/
@[simp]
theorem forget_continuousIrreducibleQuotientEquiv {n : ℕ}
    (c : ContinuousIrreducibleClasses.{uG, uV} (G ⧸ N) n) :
    forgetPropertyClass _ (continuousIrreducibleQuotientEquiv N n c).val.val =
      restrictClass π (forgetPropertyClass _ c.val) :=
  forget_inflateClass N c.val

/-- Inflation commutes with twisting by a character of the quotient and its
pullback to the original group. -/
theorem continuousIrreducibleQuotientEquiv_twist {n : ℕ} (χ : (G ⧸ N) →ₜ* ℂˣ)
    (c : ContinuousIrreducibleClasses.{uG, uV} (G ⧸ N) n) :
    (continuousIrreducibleQuotientEquiv N n (continuousIrreducibleTwistEquiv χ n c)).val =
      continuousIrreducibleTwistEquiv
        (χ.comp ⟨π, QuotientGroup.continuous_mk⟩) n (continuousIrreducibleQuotientEquiv N n c).val := by
  apply Subtype.ext
  apply forgetPropertyClass_injective _
  rw [forget_continuousIrreducibleQuotientEquiv, forget_continuousIrreducibleTwistEquiv,
    forget_continuousIrreducibleTwistEquiv, forget_continuousIrreducibleQuotientEquiv]
  generalize forgetPropertyClass _ c.val = c'
  exact Quotient.inductionOn c' fun _ => rfl

end Langlands.FiniteRepresentation
