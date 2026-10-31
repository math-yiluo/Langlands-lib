import Langlands.Automorphic.StableAutomorphicDeterminantMultiplier
import Langlands.Automorphic.FiniteOrderDeterminantTwist

/-! # Actual determinant twists of full automorphic operator realizations -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance operatorTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance operatorTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance operatorTwistFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance operatorTwistFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance operatorTwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

private def conjugatedSubrepresentationOrderIso
    {A V W : Type*} [Monoid A] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W)
    (α : A ≃* A) (e : V ≃ₗ[ℂ] W)
    (hc : ∀ a f, τ a (e f) = e (ρ (α a) f)) :
    Subrepresentation ρ ≃o Subrepresentation τ where
  toFun P :=
    { toSubmodule := P.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule a _ hf := by
        change ∃ f, f ∈ P.toSubmodule ∧ e f = _ at hf
        obtain ⟨f, hf, rfl⟩ := hf
        rw [hc]
        exact Submodule.mem_map_of_mem (P.apply_mem_toSubmodule (α a) hf) }
  invFun Q :=
    { toSubmodule := Q.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule a f hf := by
        change e (ρ a f) ∈ Q
        have hcov := hc (α.symm a) f
        rw [α.apply_symm_apply] at hcov
        rw [← hcov]
        exact Q.apply_mem_toSubmodule (α.symm a) hf }
  left_inv P := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).symm_apply_apply P.toSubmodule)
  right_inv Q := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).apply_symm_apply Q.toSubmodule)
  map_rel_iff' := (Submodule.orderIsoMapComap e).map_rel_iff

namespace OperatorRealization

variable (S : OperatorRealization F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance operatorTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual multiplied function subspace, invariant under every concrete operator. -/
def determinantTwist : OperatorRealization F n where
  toSubmodule := S.toSubmodule.map
    (StableAutomorphicFunctions.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap
  apply_mem_toSubmodule a _ hf := by
    change ∃ f, f ∈ S.toSubmodule ∧
      StableAutomorphicFunctions.finiteOrderDeterminantMultiplier n χ hχ f = _ at hf
    obtain ⟨f, hf, rfl⟩ := hf
    change stableAutomorphicAction F n a
      (StableAutomorphicFunctions.finiteOrderDeterminantMultiplier n χ hχ f) ∈ _
    rw [StableAutomorphicFunctions.operatorAction_determinantMultiplier]
    exact Submodule.mem_map_of_mem
      (S.apply_mem_toSubmodule (determinantOperatorConjugation n χ hχ a) hf)

/-- Actual determinant multiplication identifies the original space with its image. -/
def determinantTwistEquiv : S.Space ≃L[ℂ] (S.determinantTwist χ hχ).Space :=
  (StableAutomorphicFunctions.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _ rfl

@[simp]
theorem determinantTwistEquiv_val (f : S.Space) :
    (S.determinantTwistEquiv χ hχ f).val =
      StableAutomorphicFunctions.finiteOrderDeterminantMultiplier n χ hχ f.val := rfl

theorem determinantTwistEquiv_operatorAction
    (a : automorphicOperatorAlgebra F n) (f : S.Space) :
    (S.determinantTwist χ hχ).representation a (S.determinantTwistEquiv χ hχ f) =
      S.determinantTwistEquiv χ hχ
        (S.representation (determinantOperatorConjugation n χ hχ a) f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.operatorAction_determinantMultiplier n χ hχ a f.val

theorem determinantTwistEquiv_finite (d : FiniteAdelicGL F n) (f : S.Space) :
    (S.determinantTwist χ hχ).finiteRepresentation d (S.determinantTwistEquiv χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        S.determinantTwistEquiv χ hχ (S.finiteRepresentation d f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.finiteAction_determinantMultiplier n χ hχ d f.val

theorem determinantTwistEquiv_compact (k : standardInfiniteCompact F n) (f : S.Space) :
    (S.determinantTwist χ hχ).compactRepresentation k (S.determinantTwistEquiv χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        S.determinantTwistEquiv χ hχ (S.compactRepresentation k f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.compactAction_determinantMultiplier n χ hχ k f.val

theorem determinantTwistEquiv_differential
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    (S.determinantTwist χ hχ).envelopingAction a (S.determinantTwistEquiv χ hχ f) =
      S.determinantTwistEquiv χ hχ (S.envelopingAction a f) := by
  apply Subtype.ext
  exact StableAutomorphicFunctions.envelopingAction_determinantMultiplier n χ hχ a f.val

@[simp]
theorem toContinuous_determinantTwistEquiv (f : S.Space) :
    (S.determinantTwist χ hχ).toContinuous (S.determinantTwistEquiv χ hχ f) =
      determinantMultiplier n χ (S.toContinuous f) := rfl

@[simp]
theorem evaluate_determinantTwistEquiv (f : S.Space) (g : AdelicGL F n) :
    evaluate F n ((S.determinantTwist χ hχ).toContinuous (S.determinantTwistEquiv χ hχ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (S.toContinuous f) g := rfl

/-- The constructed image and actual multiplier satisfy the existing full twist relation. -/
theorem determinantTwistEquations :
    DeterminantTwistEquations χ S (S.determinantTwist χ hχ)
      (S.determinantTwistEquiv χ hχ).toLinearEquiv :=
  ⟨S.determinantTwistEquiv_finite χ hχ, S.determinantTwistEquiv_compact χ hχ,
    S.determinantTwistEquiv_differential χ hχ⟩

theorem isFiniteOrderDeterminantTwist :
    IsFiniteOrderDeterminantTwist χ S (S.determinantTwist χ hχ) :=
  ⟨hχ, (S.determinantTwistEquiv χ hχ).toLinearEquiv, S.determinantTwistEquations χ hχ⟩

/-- The full invariant-subspace lattices correspond via actual multiplication. -/
def determinantTwistSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o
      Subrepresentation (S.determinantTwist χ hχ).representation :=
  conjugatedSubrepresentationOrderIso S.representation
    (S.determinantTwist χ hχ).representation
    (determinantOperatorConjugation n χ hχ).toMulEquiv
    (S.determinantTwistEquiv χ hχ).toLinearEquiv
    (S.determinantTwistEquiv_operatorAction χ hχ)

/-- Irreducibility refers to all operators, and is preserved in both directions. -/
theorem determinantTwist_isIrreducible_iff :
    (S.determinantTwist χ hχ).IsIrreducible ↔ S.IsIrreducible :=
  (S.determinantTwistSubrepresentationOrderIso χ hχ).isSimpleOrder_iff.symm

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

/-- The constructed full realization is cuspidal precisely when the original one is. -/
theorem determinantTwist_isCuspidal_iff :
    (S.determinantTwist χ hχ).IsCuspidal ↔ S.IsCuspidal := by
  rw [isCuspidal_iff, isCuspidal_iff]
  constructor
  · intro ht f
    have hf := ht (S.determinantTwistEquiv χ hχ f)
    rw [toContinuous_determinantTwistEquiv, isCuspidal_determinantMultiplier_iff] at hf
    exact hf
  · intro hs f
    obtain ⟨g, rfl⟩ := (S.determinantTwistEquiv χ hχ).surjective f
    rw [toContinuous_determinantTwistEquiv]
    exact IsCuspidal.determinantMultiplier n χ (hs g)

end Cuspidal
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- A total finite-order determinant twist of an actual positive-rank cuspidal realization. -/
def determinantTwist (S : CuspidalOperatorRealization F r)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) : CuspidalOperatorRealization F r where
  realization := S.realization.determinantTwist χ hχ
  irreducible := (S.realization.determinantTwist_isIrreducible_iff χ hχ).mpr S.irreducible
  cuspidal := (S.realization.determinantTwist_isCuspidal_iff χ hχ).mpr S.cuspidal

theorem determinantTwist_isFiniteOrderDeterminantTwist
    (S : CuspidalOperatorRealization F r) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsFiniteOrderDeterminantTwist χ S (S.determinantTwist χ hχ) :=
  S.realization.isFiniteOrderDeterminantTwist χ hχ

end CuspidalOperatorRealization
end Langlands.Automorphic
