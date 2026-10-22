import Langlands.Weil.Representation.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Complex.Basic

/-!
# Distinct conditions on finite-dimensional complex Weil representations

The group and inertia subgroup are explicit inputs. Their actual local-field
specialization is a separate construction.
-/

noncomputable section

universe uG uV uΓ

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- Irreducibility means nontriviality and absence of proper nontrivial subrepresentations. -/
abbrev IsIrreducible (A : FiniteRepresentation ℂ G) : Prop :=
  Representation.IsIrreducible A.representation

/-- Semisimplicity of the whole representation, independently of any chosen Frobenius. -/
abbrev IsSemisimple (A : FiniteRepresentation ℂ G) : Prop :=
  Representation.IsSemisimpleRepresentation A.representation

/-- The kernel of the action restricted to the supplied inertia subgroup. -/
def inertiaKernel (A : FiniteRepresentation ℂ G) (I : Subgroup G) : Subgroup I :=
  (A.representation.comp I.subtype).ker

/-- Finite image of inertia, stated separately from openness of its kernel. -/
def HasFiniteInertiaImage (A : FiniteRepresentation ℂ G) (I : Subgroup G) : Prop :=
  (Set.range (A.representation.comp I.subtype)).Finite

/-- Unramifiedness means that every inertia element acts as the identity. -/
def IsUnramified (A : FiniteRepresentation ℂ G) (I : Subgroup G) : Prop :=
  ∀ i : I, A.representation i = 1

/-- Finite image of the whole group, without identifying it with Galois type. -/
def HasFiniteImage (A : FiniteRepresentation ℂ G) : Prop :=
  (Set.range A.representation).Finite

/-- Unitarizability: existence of a positive-definite Hermitian inner product
preserved by the action. No particular norm or inner product has been chosen. -/
def IsUnitary (A : FiniteRepresentation ℂ G) : Prop :=
  ∃ h : InnerProductSpace.Core ℂ A,
    ∀ (g : G) (v w : A), h.inner (A.representation g v) (A.representation g w) = h.inner v w

variable [TopologicalSpace G]

/-- Continuity into the usual finite-dimensional complex endomorphism topology.
The complex coefficient topology is the usual one, not the discrete topology. -/
def IsContinuous (A : FiniteRepresentation ℂ G) : Prop :=
  letI : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  Continuous A.representation

/-- The algebraic Weil convention: the kernel on inertia is open in inertia
with its subgroup topology. This is not asserted equivalent to continuity. -/
def HasOpenInertiaKernel (A : FiniteRepresentation ℂ G) (I : Subgroup G) : Prop :=
  IsOpen (A.inertiaKernel I : Set I)

/-- Galois type relative to a supplied continuous group map: the representation
extends to a continuous representation on the same vector space.
For local Weil groups the map is the canonical map into the absolute Galois group. -/
def IsGaloisTypeAlong (A : FiniteRepresentation ℂ G) {Γ : Type uΓ} [Group Γ]
    [TopologicalSpace Γ] (j : G →ₜ* Γ) : Prop :=
  ∃ τ : Representation ℂ Γ A,
    IsContinuous (of τ) ∧ τ.comp j.toMonoidHom = A.representation

/-- Continuous representations, without a semisimplicity restriction. -/
def ContinuousObjects (G : Type uG) [Group G] [TopologicalSpace G] :=
  {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous}

/-- Representations with open inertia kernel, without a continuity assertion. -/
def OpenInertiaObjects (I : Subgroup G) :=
  {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.HasOpenInertiaKernel I}

/-- The continuous irreducible rank-`n` parameter set on a supplied group. -/
def ContinuousIrreducibleClasses (G : Type uG) [Group G] [TopologicalSpace G] (n : ℕ) :=
  IsomorphismClassesOfRankWith
    (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous ∧ A.IsIrreducible) n

/-- The open-inertia-kernel semisimple rank-`n` parameter set.
It is kept separate from the continuous or irreducible parameter sets. -/
def OpenInertiaSemisimpleClasses (I : Subgroup G) (n : ℕ) :=
  IsomorphismClassesOfRankWith
    (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.HasOpenInertiaKernel I ∧ A.IsSemisimple) n

end Langlands.FiniteRepresentation
