import Langlands.ClassFieldTheory.Local.FundamentalClasses
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# The underlying multiplicative Galois formation

This constructs Serre's formation data, with no class-formation axiom assumed.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Serre's underlying formation data for an actual representation. It contains
the subgroup-family certificates and local fixedness, not H¹ or H² axioms. -/
structure FormationData {G : Type u} [Group G]
    (A : Rep.{u} IntegerScalars.{u} G) where
  admissible : Set (Subgroup G)
  top_mem : (⊤ : Subgroup G) ∈ admissible
  inf_mem : ∀ {H J}, H ∈ admissible → J ∈ admissible → H ⊓ J ∈ admissible
  upward_mem : ∀ {H J}, H ∈ admissible → H ≤ J → J ∈ admissible
  conjugate_mem : ∀ (g : G) {H}, H ∈ admissible →
    H.comap (MulAut.conj g).toMonoidHom ∈ admissible
  finite_index : ∀ {H}, H ∈ admissible → H.FiniteIndex
  locally_fixed : ∀ x : A, ∃ H ∈ admissible, ∀ g ∈ H, A.ρ g x = x

/-- The actual multiplicative formation of a perfect field: absolute Galois
group, its open subgroups, and units of its algebraic closure. -/
def multiplicativeFormation (K : Type u) [Field K] [PerfectField K] :
    FormationData (unitsRepresentation K (AlgebraicClosure K)) where
  admissible := {H | IsOpen (H : Set Gal(AlgebraicClosure K/K))}
  top_mem := by
    change IsOpen ((⊤ : Subgroup Gal(AlgebraicClosure K/K)) :
      Set Gal(AlgebraicClosure K/K))
    simp
  inf_mem {H J} hH hJ := by
    change IsOpen (H : Set Gal(AlgebraicClosure K/K)) at hH
    change IsOpen (J : Set Gal(AlgebraicClosure K/K)) at hJ
    exact hH.inter hJ
  upward_mem {H J} hH hHJ := Subgroup.isOpen_mono hHJ hH
  conjugate_mem g {H} hH := hH.preimage (IsTopologicalGroup.continuous_conj g)
  finite_index {H} hH := by
    have : CompactSpace Gal(AlgebraicClosure K/K) := inferInstance
    have : Finite (Gal(AlgebraicClosure K/K) ⧸ H) :=
      H.quotient_finite_of_isOpen hH
    exact H.finiteIndex_of_finite_quotient
  locally_fixed x := by
    refine ⟨(unitOpenStabilizer K (AlgebraicClosure K) x.toMul).toSubgroup,
      (unitOpenStabilizer K (AlgebraicClosure K) x.toMul).isOpen, ?_⟩
    intro g hg
    exact (mem_unitOpenStabilizer_iff K (AlgebraicClosure K) x g).mp hg

/-- The admissible subgroups are exactly the open subgroups in the actual
Krull topology, with no separately postulated family. -/
theorem mem_multiplicativeFormation_iff (K : Type u) [Field K] [PerfectField K]
    (H : Subgroup Gal(AlgebraicClosure K/K)) :
    H ∈ (multiplicativeFormation K).admissible ↔
      IsOpen (H : Set Gal(AlgebraicClosure K/K)) := Iff.rfl

/-- The actual finite subfield associated to an open subgroup in the formation. -/
def formationField (K : Type u) [Field K]
    (H : OpenSubgroup Gal(AlgebraicClosure K/K)) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField H.toSubgroup

theorem fixingSubgroup_formationField (K : Type u) [Field K] [PerfectField K]
    (H : OpenSubgroup Gal(AlgebraicClosure K/K)) :
    (formationField K H).fixingSubgroup = H.toSubgroup :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H.toSubgroup, H.isClosed⟩

/-- Openness gives the finite extension certificate through the existing
infinite Galois correspondence. -/
instance formationField_finiteDimensional (K : Type u) [Field K] [PerfectField K]
    (H : OpenSubgroup Gal(AlgebraicClosure K/K)) :
    FiniteDimensional K (formationField K H) :=
  (InfiniteGalois.isOpen_iff_finite (formationField K H)).mp (by
    change IsOpen ((formationField K H).fixingSubgroup : Set Gal(AlgebraicClosure K/K))
    rw [fixingSubgroup_formationField]
    exact H.isOpen)

end Langlands.ClassFieldTheory.Local
