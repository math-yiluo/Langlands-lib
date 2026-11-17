import Langlands.Automorphic.FiniteInfiniteMultiplicity

/-! # Finite versus infinite decomposition of cuspidal realizations -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Automorphic

open Langlands.Global
open scoped TensorProduct

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance cuspidalFiniteInfiniteRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalFiniteInfiniteContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalFiniteInfiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalFiniteInfiniteFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cuspidalFiniteInfiniteStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance cuspidalFiniteInfiniteSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance cuspidalFiniteInfiniteFiniteSpaceGroup (A : FiniteRealization F n) :
    AddCommGroup A.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n) (A : Subrepresentation S.finiteRepresentation)

local instance cuspidalFiniteInfiniteSliceGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

/-- Evaluation at a finite-factor vector intertwines the compact actions. -/
def finiteMultiplicityEvalAt (a : A.toSubmodule) :
    (S.finiteMultiplicityCompact A).IntertwiningMap S.compactRepresentation where
  toLinearMap := (Representation.IntertwiningMap.toLinearMapl
    A.toRepresentation S.finiteRepresentation).flip a
  isIntertwining' _ := LinearMap.ext fun _ => rfl

theorem finiteMultiplicityEvalAt_injective
    (hA : A.toRepresentation.IsIrreducible) {a : A.toSubmodule} (ha : a ≠ 0) :
    Function.Injective (S.finiteMultiplicityEvalAt A a) := by
  let := hA
  change Function.Injective (S.finiteMultiplicityEvalAt A a).toLinearMap
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hfa : f a = 0 := hf
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hi | hz
  · exact absurd (hi (hfa.trans (map_zero f).symm)) ha
  · exact hz

/-- Every multiplicity vector has a finite-dimensional compact orbit. -/
theorem finiteMultiplicityCompact_isFiniteVector
    (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (f : S.FiniteMultiplicity A) :
    FiniteVectors.IsFiniteVector (S.finiteMultiplicityCompact A) f := by
  obtain ⟨a, ha, ha0⟩ := TwoFactorExistence.exists_ne_zero_of_ne_bot hne
  have hsub : (⟨a, ha⟩ : A.toSubmodule) ≠ 0 :=
    fun h => ha0 (congrArg Subtype.val h)
  exact (FiniteVectors.isFiniteVector_map_iff (S.finiteMultiplicityEvalAt A ⟨a, ha⟩)
    (S.finiteMultiplicityEvalAt_injective A hA hsub) f).mp
      (S.compactRepresentation_isFiniteVector _)

/-- The compact/enveloping covariance on multiplicities is the actual adjoint covariance. -/
theorem finiteMultiplicityCompact_enveloping
    (k : standardInfiniteCompact F n) (b : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : S.FiniteMultiplicity A) :
    S.finiteMultiplicityCompact A k (S.finiteMultiplicityEnveloping A b f) =
      S.finiteMultiplicityEnveloping A
        (ArchimedeanGL.envelopingConjugation F n k.val b)
        (S.finiteMultiplicityCompact A k f) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  exact S.compactRepresentation_envelopingAction k b (f a)

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- An actual irreducible admissible finite factor, with all multiplicities retained. -/
structure FiniteInfiniteDecomposition (S : CuspidalOperatorRealization F r) where
  finite : Subrepresentation S.realization.finiteRepresentation
  nonzero : finite ≠ ⊥
  irreducible : finite.toRepresentation.IsIrreducible
  admissible : IsAdmissible finite.toRepresentation

/-- Every cuspidal realization supplies an actual finite factor for tensor evaluation. -/
def finiteInfiniteDecomposition (S : CuspidalOperatorRealization F r) :
    S.FiniteInfiniteDecomposition := by
  let hex := cuspidalIrreducibleAdmissibleFiniteSliceExistence F r S
  let B := Classical.choose hex
  have hirr := (Classical.choose_spec hex).1
  have hadm := (Classical.choose_spec hex).2
  let ι : B.subspace.representation.IntertwiningMap S.realization.finiteRepresentation :=
    S.realization.finiteEquiv.symm.toIntertwiningMap.comp B.inclusion
  have hι : Function.Injective ι :=
    S.realization.finiteEquiv.symm.toLinearEquiv.injective.comp B.inclusion_injective
  let A := ι.range
  let e : B.subspace.representation.Equiv A.toRepresentation :=
    Representation.Equiv.mk (LinearEquiv.ofInjective ι.toLinearMap hι) (by
      intro d
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      exact Representation.IntertwiningMap.isIntertwining _ _ ι d a)
  refine
    { finite := A
      nonzero := ?_
      irreducible := CountableDual.isIrreducible_of_equiv _ e hirr
      admissible := isAdmissible_of_equiv e hadm }
  intro hA
  obtain ⟨a, ha⟩ := B.exists_ne_zero
  have hm : ι a ∈ A.toSubmodule := ⟨a, rfl⟩
  rw [hA] at hm
  have hi0 : ι a = ι 0 := (Submodule.mem_bot ℂ).mp hm |>.trans (map_zero ι).symm
  exact ha (hι hi0)

namespace FiniteInfiniteDecomposition

variable {S : CuspidalOperatorRealization F r} (D : S.FiniteInfiniteDecomposition)

local instance cuspidalFiniteInfiniteFactorGroup : AddCommGroup D.finite.toSubmodule :=
  Submodule.addCommGroup _

/-- The archimedean multiplicity space of this actual finite factor. -/
abbrev InfiniteSpace := S.realization.FiniteMultiplicity D.finite

/-- The tensor equivalence is evaluation on the actual finite factor. -/
def equiv : D.finite.toSubmodule ⊗[ℂ] D.InfiniteSpace ≃ₗ[ℂ] S.Space :=
  S.realization.finiteMultiplicityEquiv D.finite S.irreducible D.nonzero
    D.irreducible D.admissible

@[simp]
theorem equiv_tmul (a : D.finite.toSubmodule) (f : D.InfiniteSpace) :
    D.equiv (a ⊗ₜ[ℂ] f) = f a := rfl

end FiniteInfiniteDecomposition
end CuspidalOperatorRealization
end Langlands.Automorphic
