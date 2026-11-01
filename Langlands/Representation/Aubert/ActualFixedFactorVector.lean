import Langlands.Representation.Aubert.IrreducibleImageAssembly
import Langlands.VirtualRepresentation.EffectiveFixedVector
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof

/-!
# Actual irreducible images from a fixed composition-factor vector

Identify actual irreducible subquotients with the support of the canonical
factor vector, apply positive integral counting to a fixed actual class,
and realize the resulting signed generator by an actual irreducible object.
Effectivity and the fixed-class identity remain explicit hypotheses.
-/

noncomputable section

open CategoryTheory Langlands.VirtualRepresentation

universe uR uG uV

namespace Langlands.SmoothRep.IrreducibleOperator

open IrreducibleGrothendieckProof

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual smooth subquotient representing a graded factor, over an
arbitrary field and in the ambient representation's carrier universe. -/
def factorSubquotient (A : SmoothRep.{uR, uG, uV} k G) {n : ℕ}
    (s : ObjectRepFiltration A.obj n) (i : Fin n) :
    SmoothRep.{uR, uG, uV} k G :=
  subquotient A (s.subrepresentation i.succ)
    ((s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit))

theorem factorSubquotient_isSubquotient
    (A : SmoothRep.{uR, uG, uV} k G) {n : ℕ}
    (s : ObjectRepFiltration A.obj n) (i : Fin n) :
    IsSubquotient (factorSubquotient A s i) A :=
  ⟨_, _, ⟨Iso.refl _⟩⟩

/-- The actual quotient used above carries the published graded action. -/
def factorSubquotientEquiv (A : SmoothRep.{uR, uG, uV} k G) {n : ℕ}
    (s : ObjectRepFiltration A.obj n) (i : Fin n) :
    (factorSubquotient A s i).representation.Equiv (s.gradedRepresentation i).ρ :=
  Representation.Equiv.refl _

/-- A genuine irreducible label occurs in the canonical factor vector
exactly when its actual representative is an actual subquotient. -/
theorem mem_support_compositionFactors_iff_isSubquotient
    (M : FiniteLengthObject.{uR, uG, uV} k G)
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible) :
    irreducibleIsoClass A hA ∈ (compositionFactors M).support ↔
      IsSubquotient A M.val := by
  classical
  have hcount :
      irreducibleIsoClass A hA ∈ (compositionFactors M).support ↔
        0 < compositionMultiplicity M A := by
    rw [Finsupp.mem_support_iff, compositionFactors_apply M A hA]
    omega
  rw [hcount]
  let s := (chosenSeries M).2.val
  have hs : s.HasSimpleFactors := (chosenSeries M).2.property
  change 0 < s.factorMultiplicity A.obj ↔ IsSubquotient A M.val
  constructor
  · intro h
    obtain ⟨⟨i, ⟨e⟩⟩⟩ := (Nat.card_pos_iff.mp h).1
    refine ⟨s.subrepresentation i.succ,
      ((s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit)),
      ⟨?_⟩⟩
    exact mkIso (e.symm.trans (factorSubquotientEquiv M.val s i).symm)
  · rintro ⟨S, U, ⟨e⟩⟩
    obtain ⟨i, ⟨f⟩⟩ := simpleSubquotientFactor k G M.val _ s hs A S U hA
      ⟨equivOfIso e⟩
    exact Nat.card_pos_iff.mpr ⟨⟨⟨i, ⟨f.symm⟩⟩⟩, inferInstance⟩

variable (D : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ]
  FiniteLengthGrothendieckGroup.{uR, uG, uV} k G)

/-- Actual effectivity on every irreducible subquotient of a fixed actual
class forces every supported irreducible image to be a generator. -/
theorem generator_image_of_effective_fixed_class
    (hD : Function.Injective D)
    (M : FiniteLengthObject.{uR, uG, uV} k G)
    (hfix : D (FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property) =
      FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property)
    (hpositive : ∀ (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible),
      IsSubquotient A M.val →
      factorMap (D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA))) ∈ effective) :
    ∀ c ∈ (compositionFactors M).support,
      ∃ d, onIrreducibles D (generator c) = generator d := by
  apply generator_image_of_effective_fixed (onIrreducibles D)
    (onIrreducibles_injective D hD) (compositionFactors M)
    (compositionFactors_effective M)
  · simpa only [factorMap_ofRepresentation] using
      onIrreducibles_fixed D
        (FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property) hfix
  · intro c hc
    obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
    have hsub := (mem_support_compositionFactors_iff_isSubquotient M A hA).mp hc
    change factorMap (D (realizeIrreducibles k G
      (generator (irreducibleIsoClass A hA)))) ∈ effective
    rw [realizeIrreducibles_generator_irreducibleIsoClass A hA
      (hasFiniteLength_of_isIrreducible hA)]
    exact hpositive A hA hsub

/-- A fixed actual class and signed effectivity on its actual irreducible
subquotients give an actual irreducible image up to sign for each of them. -/
theorem exists_irreducible_image_of_effective_fixed_class
    (hD : Function.Injective D) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (M : FiniteLengthObject.{uR, uG, uV} k G)
    (hfix : (s • D) (FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property) =
      FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property)
    (hpositive : ∀ (C : SmoothRep.{uR, uG, uV} k G) (hC : C.IsIrreducible),
      IsSubquotient C M.val →
      factorMap ((s • D) (FiniteLengthGrothendieckGroup.ofRepresentation C
        (hasFiniteLength_of_isIrreducible hC))) ∈ effective)
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible)
    (hsub : IsSubquotient A M.val) :
    ∃ (B : SmoothRep.{uR, uG, uV} k G) (hB : B.IsIrreducible),
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) ∨
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          -FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) := by
  have hsign : Function.Injective (s • D) := by
    rcases hs with rfl | rfl
    · simpa only [one_smul] using hD
    · intro x y h
      apply hD
      simpa only [LinearMap.smul_apply, neg_one_smul, LinearMap.neg_apply, neg_inj] using h
  apply exists_irreducible_image_of_sign_adjusted_generator D s hs A hA
  exact generator_image_of_effective_fixed_class (s • D) hsign M hfix hpositive
    (irreducibleIsoClass A hA)
    ((mem_support_compositionFactors_iff_isSubquotient M A hA).mpr hsub)

/-- The same conclusion applies to an actual irreducible embedding into the
fixed finite-length representation. -/
theorem exists_irreducible_image_of_embedding_in_effective_fixed_class
    (hD : Function.Injective D) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (M : FiniteLengthObject.{uR, uG, uV} k G)
    (hfix : (s • D) (FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property) =
      FiniteLengthGrothendieckGroup.ofRepresentation M.val M.property)
    (hpositive : ∀ (C : SmoothRep.{uR, uG, uV} k G) (hC : C.IsIrreducible),
      IsSubquotient C M.val →
      factorMap ((s • D) (FiniteLengthGrothendieckGroup.ofRepresentation C
        (hasFiniteLength_of_isIrreducible hC))) ∈ effective)
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible)
    (i : A.representation.IntertwiningMap M.val.representation)
    (hi : Function.Injective i) :
    ∃ (B : SmoothRep.{uR, uG, uV} k G) (hB : B.IsIrreducible),
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) ∨
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          -FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) := by
  apply exists_irreducible_image_of_effective_fixed_class D hD s hs M hfix hpositive A hA
  exact (mem_support_compositionFactors_iff_isSubquotient M A hA).mp
    (mem_support_compositionFactors_of_injective A M.val hA M.property i hi)

end Langlands.SmoothRep.IrreducibleOperator
