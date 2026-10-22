import Langlands.WeilDeligne.Parameters
import Mathlib.LinearAlgebra.Determinant

/-!
# Weil–Deligne linear algebra targets

The invariant-subspace predicates below describe ordinary WD irreducibility
and semisimplicity directly. Their comparison with zero monodromy is a target,
not part of a definition or an input hypothesis.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.LinearAlgebra

universe uG uV uW

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- An actual linear subspace stable under both the Weil action and monodromy. -/
def IsStable (A : WeilDeligneRepresentation ℂ G ν) (S : Submodule ℂ A) : Prop :=
  (∀ g, S ≤ S.comap (A.representation g)) ∧ S ≤ S.comap A.monodromy

/-- Ordinary irreducibility of a pair, including nontriviality of its carrier. -/
def IsIrreducible (A : WeilDeligneRepresentation ℂ G ν) : Prop :=
  Nontrivial A ∧ ∀ S : Submodule ℂ A, IsStable A S → S = ⊥ ∨ S = ⊤

/-- Ordinary WD semisimplicity means that every stable subspace has a stable
linear complement. This does not define it by the desired comparison theorem. -/
def IsSemisimple (A : WeilDeligneRepresentation ℂ G ν) : Prop :=
  ∀ S : Submodule ℂ A, IsStable A S →
    ∃ T : Submodule ℂ A, IsStable A T ∧ IsCompl S T

/-- Kernel stability concerns the actual kernel of the actual monodromy map. -/
def KernelStability : Prop :=
  ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
    IsStable A (LinearMap.ker A.monodromy) ∧
    ∀ g, (LinearMap.ker A.monodromy).map (A.representation g) =
      LinearMap.ker A.monodromy

/-- A pair is irreducible exactly when monodromy is zero and the underlying
Weil representation is irreducible; nilpotence and kernel stability force
irreducible pairs to have zero monodromy. No classification or
Frobenius-semisimplicity hypothesis is used. -/
def IrreducibilityComparison : Prop :=
  ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
    IsIrreducible A ↔ A.monodromy = 0 ∧ A.toFiniteRepresentation.IsIrreducible

/-- Ordinary semisimplicity of the whole pair holds exactly when monodromy is
zero and the underlying Weil representation is semisimple. Frobenius
semisimplicity is not involved in this comparison. -/
def SemisimplicityComparison : Prop :=
  ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
    IsSemisimple A ↔ A.monodromy = 0 ∧ A.toFiniteRepresentation.IsSemisimple

/-- Every WD morphism preserves the actual kernels and images of all powers
of monodromy; images and inverse images of stable subspaces are stable. -/
def MorphismCompatibility : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) (f : Hom A B),
    (∀ n : ℕ, (LinearMap.ker (A.monodromy ^ n)).map f.intertwiner.toLinearMap ≤
      LinearMap.ker (B.monodromy ^ n)) ∧
    (∀ n : ℕ, (LinearMap.range (A.monodromy ^ n)).map f.intertwiner.toLinearMap ≤
      LinearMap.range (B.monodromy ^ n)) ∧
    (∀ S : Submodule ℂ A, IsStable A S →
      IsStable B (S.map f.intertwiner.toLinearMap)) ∧
    ∀ T : Submodule ℂ B, IsStable B T →
      IsStable A (T.comap f.intertwiner.toLinearMap)

/-- Genuine pair isomorphisms preserve linear-algebra invariants and all
three distinct notions of irreducibility/semisimplicity used here. -/
def IsomorphismInvariants : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) (e : Equiv A B),
    A.rank = B.rank ∧
    (A.monodromy = 0 ↔ B.monodromy = 0) ∧
    (IsIrreducible A ↔ IsIrreducible B) ∧
    (IsSemisimple A ↔ IsSemisimple B) ∧
    (∀ degree : G →* Multiplicative ℤ,
      A.IsFrobeniusSemisimple degree ↔ B.IsFrobeniusSemisimple degree) ∧
    (∀ n : ℕ,
      (LinearMap.ker (A.monodromy ^ n)).map e.representationEquiv.toLinearMap =
        LinearMap.ker (B.monodromy ^ n)) ∧
    (∀ n : ℕ,
      (LinearMap.range (A.monodromy ^ n)).map e.representationEquiv.toLinearMap =
        LinearMap.range (B.monodromy ^ n)) ∧
    (∀ n : ℕ,
      Module.finrank ℂ (LinearMap.ker (A.monodromy ^ n)) =
        Module.finrank ℂ (LinearMap.ker (B.monodromy ^ n))) ∧
    (∀ n : ℕ,
      Module.finrank ℂ (LinearMap.range (A.monodromy ^ n)) =
        Module.finrank ℂ (LinearMap.range (B.monodromy ^ n))) ∧
    ∀ g, LinearMap.det (A.representation g) = LinearMap.det (B.representation g)

/-- The actual zero-monodromy embedding is fully faithful even for
intertwiners between carriers in different universes. Its irreducibility and
ordinary semisimplicity predicates recover those of the Weil representation. -/
def ZeroMonodromyCompatibility : Prop :=
  ∀ (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (B : FiniteRepresentation.{0, uG, uW} ℂ G),
    (∀ f : A.representation.IntertwiningMap B.representation,
      ∃! h : Hom (zeroMonodromy ν A) (zeroMonodromy ν B), h.intertwiner = f) ∧
    (Nonempty (Equiv (zeroMonodromy ν A) (zeroMonodromy ν B)) ↔
      Nonempty (A.Equiv B)) ∧
    (IsIrreducible (zeroMonodromy ν A) ↔ A.IsIrreducible) ∧
    (IsSemisimple (zeroMonodromy ν A) ↔ A.IsSemisimple) ∧
    LinearMap.ker (zeroMonodromy ν A).monodromy = ⊤

/-- Coherent whole target for kernel, morphism and ordinary-semisimplicity laws. -/
def AlgebraicFamily : Prop :=
  KernelStability.{uG, uV} (ν := ν) ∧
  IrreducibilityComparison.{uG, uV} (ν := ν) ∧
  SemisimplicityComparison.{uG, uV} (ν := ν) ∧
  MorphismCompatibility.{uG, uV, uW} (ν := ν) ∧
  IsomorphismInvariants.{uG, uV, uW} (ν := ν) ∧
  ZeroMonodromyCompatibility.{uG, uV, uW} (ν := ν)

section Topology

variable [TopologicalSpace G]

/-- Isomorphism invariance of the separate topological and inertia conditions.
This does not identify the conditions with one another. -/
def ParameterIsomorphismInvariants : Prop :=
  ∀ (I : Subgroup G)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    Equiv A B →
    (IsParameter I A ↔ IsParameter I B) ∧
    (A.IsContinuous ↔ B.IsContinuous) ∧
    (A.toFiniteRepresentation.HasFiniteInertiaImage I ↔
      B.toFiniteRepresentation.HasFiniteInertiaImage I)

/-- Whole target, including isomorphism invariance of the distinct parameter conditions. -/
def Statement : Prop :=
  AlgebraicFamily.{uG, uV, uW} (ν := ν) ∧
  ParameterIsomorphismInvariants.{uG, uV, uW} (ν := ν)

end Topology

end Langlands.WeilDeligneRepresentation.LinearAlgebra
