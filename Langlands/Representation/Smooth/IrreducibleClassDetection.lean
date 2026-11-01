import Langlands.Representation.Smooth.IrreducibleCompositionFactors
import Langlands.Representation.Filtration.RepresentationLength

/-! Detection of actual irreducibles from their exact finite-length classes. -/

noncomputable section

open Langlands.VirtualRepresentation
open Langlands.SmoothRep.IrreducibleGrothendieckProof
open scoped BigOperators

universe uR uG uV

namespace Langlands.SmoothRep

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Total composition length as an integer-linear invariant of the exact
finite-length Grothendieck group. -/
def FiniteLengthGrothendieckGroup.compositionLength :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ] ℤ :=
  (extend (fun _ : IrreducibleIsoClass.{uR, uG, uV} k G => (1 : ℤ))).comp factorMap

/-- On an actual object the exact length invariant counts the steps of every
supplied composition series. -/
theorem FiniteLengthGrothendieckGroup.compositionLength_of_series
    (A : SmoothRep.{uR, uG, uV} k G) (hA : A.HasFiniteLength) {n : ℕ}
    (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors) :
    compositionLength (ofRepresentation A hA) = (n : ℤ) := by
  classical
  simp only [compositionLength, LinearMap.comp_apply, factorMap_ofRepresentation,
    compositionFactors_eq_series ⟨A, hA⟩ s hs]
  simp [seriesClass, extend, generator]

/-- A finite-length object whose factor sum is one irreducible generator is
itself irreducible. -/
theorem isIrreducible_of_compositionFactors_eq_generator
    (A : FiniteLengthObject.{uR, uG, uV} k G)
    (c : IrreducibleIsoClass.{uR, uG, uV} k G)
    (h : compositionFactors A = generator c) : A.val.IsIrreducible := by
  classical
  have hcount := congrArg
    (extend (fun _ : IrreducibleIsoClass.{uR, uG, uV} k G => (1 : ℤ))) h
  have hn : ((chosenSeries A).1 : ℤ) = 1 := by
    simpa [compositionFactors, seriesClass, extend, generator] using hcount
  have hn' : (chosenSeries A).1 = 1 := by exact_mod_cast hn
  apply repLength_eq_one_iff.mp
  change repLength A.val.obj.ρ = 1
  rw [repLength_eq_of_hasSimpleFactors (chosenSeries A).2.val
    (chosenSeries A).2.property, hn']
  rfl

/-- A finite-length object whose factor sum is the label of a supplied
irreducible is actually equivalent to that irreducible. -/
theorem nonempty_equiv_of_compositionFactors_eq_generator
    (A : FiniteLengthObject.{uR, uG, uV} k G)
    (τ : SmoothRep.{uR, uG, uV} k G) (hτ : τ.IsIrreducible)
    (h : compositionFactors A = generator (irreducibleIsoClass τ hτ)) :
    Nonempty (A.val.representation.Equiv τ.representation) := by
  have hA := isIrreducible_of_compositionFactors_eq_generator A _ h
  apply (irreducibleIsoClass_eq_iff_nonempty_equiv hA hτ).mp
  apply Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)
  exact (compositionFactors_irreducible A.val hA A.property).symm.trans h

/-- The factor sum of an actual finite-length object cannot be the negative
of an irreducible generator. -/
theorem compositionFactors_ne_neg_generator
    (A : FiniteLengthObject.{uR, uG, uV} k G)
    (τ : SmoothRep.{uR, uG, uV} k G) (hτ : τ.IsIrreducible) :
    compositionFactors A ≠ -generator (irreducibleIsoClass τ hτ) := by
  intro h
  have hc := congrArg
    (fun v : IrreducibleLattice.{uR, uG, uV} k G => v (irreducibleIsoClass τ hτ)) h
  simp [compositionFactors_apply, generator] at hc

/-- Equality of an actual finite-length class with an irreducible class
detects an actual equivalence. -/
theorem ofRepresentation_eq_irreducible_iff
    (A τ : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) (hτ : τ.IsIrreducible)
    (hτLength : τ.HasFiniteLength) :
    FiniteLengthGrothendieckGroup.ofRepresentation A hA =
        FiniteLengthGrothendieckGroup.ofRepresentation τ hτLength ↔
      Nonempty (A.representation.Equiv τ.representation) := by
  constructor
  · intro h
    apply nonempty_equiv_of_compositionFactors_eq_generator ⟨A, hA⟩ τ hτ
    have hf := congrArg factorMap h
    simpa only [factorMap_ofRepresentation,
      compositionFactors_irreducible τ hτ hτLength] using hf
  · rintro ⟨e⟩
    exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv hA hτLength e

/-- Equality with an irreducible exact class also detects irreducibility. -/
theorem isIrreducible_of_class_eq_irreducible
    (A τ : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) (hτ : τ.IsIrreducible)
    (hτLength : τ.HasFiniteLength)
    (h : FiniteLengthGrothendieckGroup.ofRepresentation A hA =
      FiniteLengthGrothendieckGroup.ofRepresentation τ hτLength) :
    A.IsIrreducible := by
  obtain ⟨e⟩ := (ofRepresentation_eq_irreducible_iff A τ hA hτ hτLength).mp h
  exact isIrreducible_of_equiv e.symm hτ

/-- No actual finite-length class is the negative of an irreducible class. -/
theorem ofRepresentation_ne_neg_irreducible
    (A τ : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) (hτ : τ.IsIrreducible)
    (hτLength : τ.HasFiniteLength) :
    FiniteLengthGrothendieckGroup.ofRepresentation A hA ≠
      -FiniteLengthGrothendieckGroup.ofRepresentation τ hτLength := by
  intro h
  apply compositionFactors_ne_neg_generator ⟨A, hA⟩ τ hτ
  have hf := congrArg factorMap h
  simpa only [map_neg, factorMap_ofRepresentation,
    compositionFactors_irreducible τ hτ hτLength] using hf

end Langlands.SmoothRep
