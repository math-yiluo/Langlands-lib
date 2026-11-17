import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof

/-! # Finite adelic factors and archimedean multiplicity spaces -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Langlands.Automorphic

open Langlands.Global
open scoped TensorProduct

private theorem finiteEvaluation_injective
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A : Subrepresentation ρ)
    (hA : A.toRepresentation.IsIrreducible)
    (hscalar : ∀ f : A.toRepresentation.IntertwiningMap A.toRepresentation,
      ∃ c : ℂ, f = c • Representation.IntertwiningMap.id A.toRepresentation) :
    Function.Injective (TensorProduct.lift
      (Representation.IntertwiningMap.toLinearMapl A.toRepresentation ρ).flip) := by
  let ρ' : Representation ℂ (G × PUnit.{1}) V := ρ.comp (MonoidHom.fst _ _)
  let U : Subrepresentation (TwoFactorExistence.first ρ') := A
  let := hA
  exact TwoFactorExistence.eval_injective U hscalar

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance finiteInfiniteRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance finiteInfiniteContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteInfiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteInfiniteFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance finiteInfiniteStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance finiteInfiniteSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable (S : OperatorRealization F n)
variable (A : Subrepresentation S.finiteRepresentation)

local instance finiteInfiniteSliceGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

/-- All finite-equivariant maps from the supplied actual finite subspace. -/
abbrev FiniteMultiplicity := A.toRepresentation.IntertwiningMap S.finiteRepresentation

/-- Compact translation acts on multiplicity maps by postcomposition. -/
def finiteMultiplicityCompact :
    Representation ℂ (standardInfiniteCompact F n) (S.FiniteMultiplicity A) where
  toFun k := Representation.IntertwiningMap.llcomp _ _ _
    (S.commutingIntertwiner (S.compactRepresentation k)
      (fun d x => S.finiteRepresentation_compactRepresentation d k x))
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    change S.compactRepresentation 1 (f a) = f a
    exact congrArg (fun T : Module.End ℂ S.Space => T (f a))
      (map_one S.compactRepresentation)
  map_mul' k l := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    change S.compactRepresentation (k * l) (f a) =
      S.compactRepresentation k (S.compactRepresentation l (f a))
    exact congrArg (fun T : Module.End ℂ S.Space => T (f a))
      (map_mul S.compactRepresentation k l)

@[simp]
theorem finiteMultiplicityCompact_apply (k : standardInfiniteCompact F n)
    (f : S.FiniteMultiplicity A) (a : A.toSubmodule) :
    S.finiteMultiplicityCompact A k f a = S.compactRepresentation k (f a) := rfl

/-- Genuine enveloping operators act on multiplicity maps by postcomposition. -/
def finiteMultiplicityEnveloping :
    ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ (S.FiniteMultiplicity A) where
  toFun a := Representation.IntertwiningMap.llcomp _ _ _
    (S.commutingIntertwiner (S.envelopingAction a)
      (fun d x => S.finiteRepresentation_envelopingAction d a x))
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change S.envelopingAction 1 (f x) = f x
    exact congrArg (fun T : Module.End ℂ S.Space => T (f x))
      (map_one S.envelopingAction)
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change S.envelopingAction (a * b) (f x) =
      S.envelopingAction a (S.envelopingAction b (f x))
    exact congrArg (fun T : Module.End ℂ S.Space => T (f x))
      (map_mul S.envelopingAction a b)
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change S.envelopingAction 0 (f x) = 0
    exact congrArg (fun T : Module.End ℂ S.Space => T (f x))
      (map_zero S.envelopingAction)
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change S.envelopingAction (a + b) (f x) =
      S.envelopingAction a (f x) + S.envelopingAction b (f x)
    exact congrArg (fun T : Module.End ℂ S.Space => T (f x))
      (map_add S.envelopingAction a b)
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change S.envelopingAction (algebraMap ℂ _ c) (f x) = c • f x
    exact congrArg (fun T : Module.End ℂ S.Space => T (f x))
      (AlgHom.commutes S.envelopingAction c)

@[simp]
theorem finiteMultiplicityEnveloping_apply (b : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : S.FiniteMultiplicity A) (a : A.toSubmodule) :
    S.finiteMultiplicityEnveloping A b f a = S.envelopingAction b (f a) := rfl

/-- Evaluation on the finite factor, with all multiplicities retained. -/
def finiteMultiplicityEvaluation : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A →ₗ[ℂ] S.Space :=
  TensorProduct.lift
    (Representation.IntertwiningMap.toLinearMapl A.toRepresentation S.finiteRepresentation).flip

@[simp]
theorem finiteMultiplicityEvaluation_tmul (a : A.toSubmodule) (f : S.FiniteMultiplicity A) :
    S.finiteMultiplicityEvaluation A (a ⊗ₜ[ℂ] f) = f a := rfl

theorem finiteMultiplicityEvaluation_finite (d : FiniteAdelicGL F n)
    (t : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A) :
    S.finiteMultiplicityEvaluation A
        (TensorProduct.map (A.toRepresentation d) LinearMap.id t) =
      S.finiteRepresentation d (S.finiteMultiplicityEvaluation A t) := by
  induction t with
  | tmul a f => exact Representation.IntertwiningMap.isIntertwining _ _ f d a
  | add t t' ht ht' => simp only [map_add, ht, ht']

theorem finiteMultiplicityEvaluation_compact (k : standardInfiniteCompact F n)
    (t : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A) :
    S.finiteMultiplicityEvaluation A
        (TensorProduct.map LinearMap.id (S.finiteMultiplicityCompact A k) t) =
      S.compactRepresentation k (S.finiteMultiplicityEvaluation A t) := by
  induction t with
  | tmul a f => rfl
  | add t t' ht ht' => simp only [map_add, ht, ht']

theorem finiteMultiplicityEvaluation_enveloping (b : ArchimedeanGL.EnvelopingAlgebra F n)
    (t : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A) :
    S.finiteMultiplicityEvaluation A
        (TensorProduct.map LinearMap.id (S.finiteMultiplicityEnveloping A b) t) =
      S.envelopingAction b (S.finiteMultiplicityEvaluation A t) := by
  induction t with
  | tmul a f => rfl
  | add t t' ht ht' => simp only [map_add, ht, ht']

set_option maxHeartbeats 1000000 in
/-- Irreducibility for the full operator action makes the evaluation range all of `S`. -/
theorem finiteMultiplicityEvaluation_surjective (hS : S.IsIrreducible) (hA : A ≠ ⊥) :
    Function.Surjective (S.finiteMultiplicityEvaluation A) := by
  have htop : LinearMap.range (S.finiteMultiplicityEvaluation A) = ⊤ := by
    apply S.eq_top_of_generatorStable hS
    · rintro d _ ⟨t, rfl⟩
      exact ⟨_, S.finiteMultiplicityEvaluation_finite A d t⟩
    · rintro k _ ⟨t, rfl⟩
      exact ⟨_, S.finiteMultiplicityEvaluation_compact A k t⟩
    · rintro b _ ⟨t, rfl⟩
      exact ⟨_, S.finiteMultiplicityEvaluation_enveloping A b t⟩
    · obtain ⟨a, ha, ha0⟩ := TwoFactorExistence.exists_ne_zero_of_ne_bot hA
      intro h
      have hmem : a ∈ LinearMap.range (S.finiteMultiplicityEvaluation A) :=
        ⟨(⟨a, ha⟩ : A.toSubmodule) ⊗ₜ[ℂ] ProductFactorization.subrepresentationInclusion A,
          rfl⟩
      rw [h] at hmem
      exact ha0 ((Submodule.mem_bot ℂ).mp hmem)
  exact LinearMap.range_eq_top.mp htop

set_option maxHeartbeats 1000000 in
/-- Jacobson density and admissible Schur make evaluation injective. -/
theorem finiteMultiplicityEvaluation_injective
    (hA : A.toRepresentation.IsIrreducible) (ha : IsAdmissible A.toRepresentation) :
    Function.Injective (S.finiteMultiplicityEvaluation A) := by
  apply finiteEvaluation_injective S.finiteRepresentation A hA
  intro f
  exact (admissibleSchur_scalarEndomorphism A.toRepresentation ha hA f).exists

/-- The finite factor and the archimedean multiplicity space recover the actual carrier. -/
def finiteMultiplicityEquiv (hS : S.IsIrreducible) (hne : A ≠ ⊥)
    (hA : A.toRepresentation.IsIrreducible) (ha : IsAdmissible A.toRepresentation) :
    A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A ≃ₗ[ℂ] S.Space :=
  LinearEquiv.ofBijective (S.finiteMultiplicityEvaluation A)
    ⟨S.finiteMultiplicityEvaluation_injective A hA ha,
      S.finiteMultiplicityEvaluation_surjective A hS hne⟩

@[simp]
theorem finiteMultiplicityEquiv_tmul (hS : S.IsIrreducible) (hne : A ≠ ⊥)
    (hA : A.toRepresentation.IsIrreducible) (ha : IsAdmissible A.toRepresentation)
    (a : A.toSubmodule) (f : S.FiniteMultiplicity A) :
    S.finiteMultiplicityEquiv A hS hne hA ha (a ⊗ₜ[ℂ] f) = f a := rfl

end OperatorRealization
end Langlands.Automorphic
