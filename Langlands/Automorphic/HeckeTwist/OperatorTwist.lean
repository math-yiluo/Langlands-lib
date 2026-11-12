import Langlands.Automorphic.OperatorDeterminantTwist
import Langlands.Representation.SubrepresentationConjugation
import Langlands.Automorphic.HeckeTwist.StableMultiplier

/-! # Twists of automorphic operator realizations by any Hecke character

The image of an operator realization under multiplication by `χ ∘ det`, for an arbitrary
Hecke character `χ`, is again an operator realization. Irreducibility and cuspidality are
preserved in both directions.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance heckeOperatorTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeOperatorTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeOperatorTwistFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeOperatorTwistFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeOperatorTwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n) (χ : HeckeCharacter F)

local instance heckeOperatorTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual multiplied function subspace, invariant under every concrete operator. -/
def heckeDeterminantTwist : OperatorRealization F n where
  toSubmodule := S.toSubmodule.map
    (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ).toLinearMap
  apply_mem_toSubmodule a _ hf := by
    change ∃ f, f ∈ S.toSubmodule ∧
      StableAutomorphicFunctions.heckeDeterminantMultiplier n χ f = _ at hf
    obtain ⟨f, hf, rfl⟩ := hf
    change stableAutomorphicAction F n a
      (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ f) ∈ _
    rw [StableAutomorphicFunctions.operatorAction_heckeDeterminantMultiplier]
    exact Submodule.mem_map_of_mem
      (S.apply_mem_toSubmodule (heckeDeterminantOperatorConjugation n χ a) hf)

/-- Actual determinant multiplication identifies the original space with its image. -/
def heckeDeterminantTwistEquiv : S.Space ≃L[ℂ] (S.heckeDeterminantTwist χ).Space :=
  (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ).ofSubmodules _ _ rfl

@[simp]
theorem heckeDeterminantTwistEquiv_val (f : S.Space) :
    (S.heckeDeterminantTwistEquiv χ f).val =
      StableAutomorphicFunctions.heckeDeterminantMultiplier n χ f.val := rfl

theorem heckeDeterminantTwistEquiv_operatorAction
    (a : automorphicOperatorAlgebra F n) (f : S.Space) :
    (S.heckeDeterminantTwist χ).representation a (S.heckeDeterminantTwistEquiv χ f) =
      S.heckeDeterminantTwistEquiv χ
        (S.representation (heckeDeterminantOperatorConjugation n χ a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.operatorAction_heckeDeterminantMultiplier n χ a f.val

theorem heckeDeterminantTwistEquiv_finite (d : FiniteAdelicGL F n) (f : S.Space) :
    (S.heckeDeterminantTwist χ).finiteRepresentation d (S.heckeDeterminantTwistEquiv χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        S.heckeDeterminantTwistEquiv χ (S.finiteRepresentation d f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.finiteAction_heckeDeterminantMultiplier n χ d f.val

theorem heckeDeterminantTwistEquiv_compact (k : standardInfiniteCompact F n) (f : S.Space) :
    (S.heckeDeterminantTwist χ).compactRepresentation k (S.heckeDeterminantTwistEquiv χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        S.heckeDeterminantTwistEquiv χ (S.compactRepresentation k f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.compactAction_heckeDeterminantMultiplier n χ k f.val

theorem heckeDeterminantTwistEquiv_differential
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    (S.heckeDeterminantTwist χ).envelopingAction a (S.heckeDeterminantTwistEquiv χ f) =
      S.heckeDeterminantTwistEquiv χ (S.envelopingAction (heckeEnvelopingShift n χ a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.envelopingAction_heckeDeterminantMultiplier n χ a f.val

@[simp]
theorem toContinuous_heckeDeterminantTwistEquiv (f : S.Space) :
    (S.heckeDeterminantTwist χ).toContinuous (S.heckeDeterminantTwistEquiv χ f) =
      determinantMultiplier n χ (S.toContinuous f) := rfl

@[simp]
theorem evaluate_heckeDeterminantTwistEquiv (f : S.Space) (g : AdelicGL F n) :
    evaluate F n ((S.heckeDeterminantTwist χ).toContinuous (S.heckeDeterminantTwistEquiv χ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (S.toContinuous f) g := rfl

/-- The full invariant-subspace lattices correspond via actual multiplication. -/
def heckeDeterminantTwistSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o
      Subrepresentation (S.heckeDeterminantTwist χ).representation :=
  conjugatedSubrepresentationOrderIso S.representation
    (S.heckeDeterminantTwist χ).representation
    (heckeDeterminantOperatorConjugation n χ).toMulEquiv
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (S.heckeDeterminantTwistEquiv_operatorAction χ)

/-- Irreducibility refers to all operators, and is preserved in both directions. -/
theorem heckeDeterminantTwist_isIrreducible_iff :
    (S.heckeDeterminantTwist χ).IsIrreducible ↔ S.IsIrreducible :=
  (S.heckeDeterminantTwistSubrepresentationOrderIso χ).isSimpleOrder_iff.symm

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

/-- The constructed full realization is cuspidal precisely when the original one is. -/
theorem heckeDeterminantTwist_isCuspidal_iff :
    (S.heckeDeterminantTwist χ).IsCuspidal ↔ S.IsCuspidal := by
  rw [isCuspidal_iff, isCuspidal_iff]
  constructor
  · intro ht f
    have hf := ht (S.heckeDeterminantTwistEquiv χ f)
    rw [toContinuous_heckeDeterminantTwistEquiv, isCuspidal_determinantMultiplier_iff] at hf
    exact hf
  · intro hs f
    obtain ⟨g, rfl⟩ := (S.heckeDeterminantTwistEquiv χ).surjective f
    rw [toContinuous_heckeDeterminantTwistEquiv]
    exact IsCuspidal.determinantMultiplier n χ (hs g)

end Cuspidal
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The twist of an irreducible cuspidal realization by any Hecke character. -/
def heckeDeterminantTwist (S : CuspidalOperatorRealization F r)
    (χ : HeckeCharacter F) : CuspidalOperatorRealization F r where
  realization := S.realization.heckeDeterminantTwist χ
  irreducible := (S.realization.heckeDeterminantTwist_isIrreducible_iff χ).mpr S.irreducible
  cuspidal := (S.realization.heckeDeterminantTwist_isCuspidal_iff χ).mpr S.cuspidal

end CuspidalOperatorRealization
end Langlands.Automorphic
