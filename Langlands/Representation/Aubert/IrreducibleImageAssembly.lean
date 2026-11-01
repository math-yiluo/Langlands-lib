import Langlands.Representation.Smooth.IrreducibleGrothendieckProof
import Langlands.Representation.Aubert.IrreducibleImageStatement
import Langlands.Representation.Aubert.RankZero

/-!
# Actual irreducible realizations of integral generator images

Transport exact finite-length Grothendieck endomorphisms to the genuine
irreducible lattice, locate an embedded irreducible in an actual factor vector,
and realize a signed generator image by an actual irreducible representation.
The Aubert rank-zero consequence is unconditional. No signed-effectivity
property or positive-rank irreducible-image theorem is asserted here.
-/

noncomputable section

open Langlands.VirtualRepresentation

universe uR uG uV uF

namespace Langlands.SmoothRep.IrreducibleOperator

open IrreducibleGrothendieckProof

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The endomorphism on genuine irreducible coefficients induced by an
endomorphism of the actual exact finite-length Grothendieck group. -/
def onIrreducibles
    (D : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uR, uG, uV} k G) :
    IrreducibleLattice.{uR, uG, uV} k G →ₗ[ℤ] IrreducibleLattice.{uR, uG, uV} k G :=
  factorMap.comp (D.comp (realizeIrreducibles k G))

variable (D : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ]
  FiniteLengthGrothendieckGroup.{uR, uG, uV} k G)

/-- Realizing transported coefficients recovers the actual exact-K0 operator. -/
theorem realize_onIrreducibles (v : IrreducibleLattice.{uR, uG, uV} k G) :
    realizeIrreducibles k G (onIrreducibles D v) =
      D (realizeIrreducibles k G v) := by
  exact LinearMap.congr_fun realize_comp_factorMap _

/-- The transport applied to the factor vector of a virtual class. -/
theorem onIrreducibles_factorMap
    (x : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G) :
    onIrreducibles D (factorMap x) = factorMap (D x) := by
  change factorMap (D (realizeIrreducibles k G (factorMap x))) = _
  rw [show realizeIrreducibles k G (factorMap x) = x from
    LinearMap.congr_fun realize_comp_factorMap x]

/-- Exact-K0 injectivity passes to genuine irreducible coefficients. -/
theorem onIrreducibles_injective (hD : Function.Injective D) :
    Function.Injective (onIrreducibles D) := by
  intro v w h
  apply (irreducibleGrothendieckStatement k G).1
  apply hD
  simpa only [realize_onIrreducibles] using congrArg (realizeIrreducibles k G) h

/-- Involutivity passes to genuine irreducible coefficients. -/
theorem onIrreducibles_involutive (hD : Function.Involutive D) :
    Function.Involutive (onIrreducibles D) := by
  intro v
  apply (irreducibleGrothendieckStatement k G).1
  rw [realize_onIrreducibles, realize_onIrreducibles, hD]

/-- An actual fixed class gives a fixed factor vector. -/
theorem onIrreducibles_fixed
    (x : FiniteLengthGrothendieckGroup.{uR, uG, uV} k G) (hx : D x = x) :
    onIrreducibles D (factorMap x) = factorMap x := by
  rw [onIrreducibles_factorMap, hx]

/-- Every actual finite-length factor vector has nonnegative coefficients. -/
theorem compositionFactors_effective (A : FiniteLengthObject.{uR, uG, uV} k G) :
    compositionFactors A ∈ effective := by
  intro c
  obtain ⟨τ, hτ, rfl⟩ := IrreducibleIsoClass.exists_eq c
  rw [compositionFactors_apply A τ hτ]
  exact Nat.cast_nonneg _

/-- The coefficient of an irreducible object's own class is one. -/
theorem compositionMultiplicity_self
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible) :
    compositionMultiplicity ⟨A, hasFiniteLength_of_isIrreducible hA⟩ A = 1 := by
  have h := compositionFactors_apply
    ⟨A, hasFiniteLength_of_isIrreducible hA⟩ A hA
  rw [compositionFactors_irreducible A hA] at h
  simp only [generator, Finsupp.single_eq_same] at h
  exact_mod_cast h.symm

/-- An actual injective intertwiner from an irreducible object forces a
strictly positive coefficient in the target's actual factor vector. -/
theorem compositionFactors_pos_of_injective
    (A B : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible)
    (hB : B.HasFiniteLength)
    (i : A.representation.IntertwiningMap B.representation)
    (hi : Function.Injective i) :
    0 < compositionFactors ⟨B, hB⟩ (irreducibleIsoClass A hA) := by
  have hmono := jordanHolderInjectiveMonotonicity k G A.obj B.obj A.obj i hi
    (compositionMultiplicity ⟨A, hasFiniteLength_of_isIrreducible hA⟩ A)
    (compositionMultiplicity ⟨B, hB⟩ A)
    (compositionMultiplicity_witness ⟨A, hasFiniteLength_of_isIrreducible hA⟩ A)
    (compositionMultiplicity_witness ⟨B, hB⟩ A)
  rw [compositionMultiplicity_self A hA] at hmono
  rw [compositionFactors_apply ⟨B, hB⟩ A hA]
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmono)

/-- An embedded actual irreducible lies in the support used by lattice
counting arguments. -/
theorem mem_support_compositionFactors_of_injective
    (A B : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible)
    (hB : B.HasFiniteLength)
    (i : A.representation.IntertwiningMap B.representation)
    (hi : Function.Injective i) :
    irreducibleIsoClass A hA ∈ (compositionFactors ⟨B, hB⟩).support :=
  Finsupp.mem_support_iff.mpr
    (ne_of_gt (compositionFactors_pos_of_injective A B hA hB i hi))

/-- A signed generator image produces an actual irreducible output, with
finite length obtained from irreducibility on both sides. -/
theorem exists_irreducible_image_of_signed_generator
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible)
    (himage : ∃ c : IrreducibleIsoClass.{uR, uG, uV} k G,
      onIrreducibles D (generator (irreducibleIsoClass A hA)) = generator c ∨
        onIrreducibles D (generator (irreducibleIsoClass A hA)) = -generator c) :
    ∃ (B : SmoothRep.{uR, uG, uV} k G) (hB : B.IsIrreducible),
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) ∨
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          -FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) := by
  obtain ⟨c, hc⟩ := himage
  obtain ⟨B, hB, rfl⟩ := IrreducibleIsoClass.exists_eq c
  refine ⟨B, hB, ?_⟩
  rcases hc with hc | hc
  · left
    have h := congrArg (realizeIrreducibles k G) hc
    simpa only [realize_onIrreducibles,
      realizeIrreducibles_generator_irreducibleIsoClass A hA
        (hasFiniteLength_of_isIrreducible hA),
      realizeIrreducibles_generator_irreducibleIsoClass B hB
        (hasFiniteLength_of_isIrreducible hB)] using h
  · right
    have h := congrArg (realizeIrreducibles k G) hc
    simpa only [realize_onIrreducibles, map_neg,
      realizeIrreducibles_generator_irreducibleIsoClass A hA
        (hasFiniteLength_of_isIrreducible hA),
      realizeIrreducibles_generator_irreducibleIsoClass B hB
        (hasFiniteLength_of_isIrreducible hB)] using h

/-- A generator image for either sign of an actual operator gives an actual
irreducible output up to sign for the original operator. -/
theorem exists_irreducible_image_of_sign_adjusted_generator
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible)
    (himage : ∃ c : IrreducibleIsoClass.{uR, uG, uV} k G,
      onIrreducibles (s • D) (generator (irreducibleIsoClass A hA)) = generator c) :
    ∃ (B : SmoothRep.{uR, uG, uV} k G) (hB : B.IsIrreducible),
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) ∨
      D (FiniteLengthGrothendieckGroup.ofRepresentation A
        (hasFiniteLength_of_isIrreducible hA)) =
          -FiniteLengthGrothendieckGroup.ofRepresentation B
            (hasFiniteLength_of_isIrreducible hB) := by
  obtain ⟨c, hc⟩ := himage
  obtain ⟨B, hB, rfl⟩ := IrreducibleIsoClass.exists_eq c
  have h := congrArg (realizeIrreducibles k G) hc
  rw [realize_onIrreducibles,
    realizeIrreducibles_generator_irreducibleIsoClass,
    realizeIrreducibles_generator_irreducibleIsoClass] at h
  refine ⟨B, hB, ?_⟩
  rcases hs with rfl | rfl
  · exact Or.inl (by simpa only [one_smul] using h)
  · exact Or.inr (neg_eq_iff_eq_neg.mp (by
      simpa only [LinearMap.smul_apply, neg_one_smul, LinearMap.neg_apply] using h))

end Langlands.SmoothRep.IrreducibleOperator

namespace Langlands.Aubert

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual irreducible-image assertion in rank zero, using the published
identity for the existing unadjusted Aubert operator. -/
theorem irreducibleImage_rankZero :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
      (hA : Representation.IsIrreducible A.representation),
      ∃ (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
        (hB : Representation.IsIrreducible B.representation),
        alternatingOperator.{uF, uV} F T 0
            (GeneralLinear.finiteLengthClass 0 F.Carrier A
              (SmoothRep.hasFiniteLength_of_isIrreducible hA)) =
          GeneralLinear.finiteLengthClass 0 F.Carrier B
            (SmoothRep.hasFiniteLength_of_isIrreducible hB) ∨
        alternatingOperator.{uF, uV} F T 0
            (GeneralLinear.finiteLengthClass 0 F.Carrier A
              (SmoothRep.hasFiniteLength_of_isIrreducible hA)) =
          -GeneralLinear.finiteLengthClass 0 F.Carrier B
            (SmoothRep.hasFiniteLength_of_isIrreducible hB) := by
  let := T.topology
  intro A hA
  refine ⟨A, hA, Or.inl ?_⟩
  rw [alternatingOperator_rankZero]
  rfl

end Langlands.Aubert
