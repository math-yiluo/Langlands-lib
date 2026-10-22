import Langlands.WeilDeligne.Parameters
import Langlands.WeilDeligne.Induction
import Langlands.Weil.Representation.InductionTopology

/-! # Finite-index induction on actual open-inertia parameter objects -/

noncomputable section

universe uG uV

namespace Langlands.WeilDeligneRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ν : G →* ℂˣ}

/-- Induce an actual pair with open inertia kernel. The source inertia is the
intersection with the inducing subgroup, and both ambient subgroups are
explicitly assumed open. -/
def parameterInduce
    (S I : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (hI : IsOpen (I : Set G))
    (A : ParameterObjects.{uG, uV} (ν := ν.comp S.subtype) (I.subgroupOf S)) :
    ParameterObjects.{uG, max uG uV} (ν := ν) I :=
  ⟨induce S A.val,
    FiniteRepresentation.hasOpenInertiaKernel_induce S I hS hI
      A.val.toFiniteRepresentation A.property⟩

/-- The induced parameter class is independent of the representative pair. -/
def parameterInduceClass
    (S I : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (hI : IsOpen (I : Set G)) :
    ParameterClasses.{uG, uV} (ν := ν.comp S.subtype) (I.subgroupOf S) →
      ParameterClasses.{uG, max uG uV} (ν := ν) I :=
  Quotient.map (parameterInduce S I hS hI) (fun _ _ ⟨e⟩ => ⟨induceEquiv S e⟩)

/-- Induction on rank-indexed genuine parameter classes. -/
def parameterInduceClassOfRank
    (S I : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (hI : IsOpen (I : Set G)) (n : ℕ) :
    ParameterClassesOfRank.{uG, uV} (ν := ν.comp S.subtype) (I.subgroupOf S) n →
      ParameterClassesOfRank.{uG, max uG uV} (ν := ν) I (S.index * n) := by
  intro c
  refine ⟨parameterInduceClass S I hS hI c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A =>
    change (induce S A.val).rank = S.index * n
    rw [rank_induce]
    change A.val.rank = n at hc
    rw [hc]

end Langlands.WeilDeligneRepresentation
