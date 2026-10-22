import Langlands.LocalField.Canonical
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.Norm.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Maps.Proper.Basic

/-! # Local norm groups: topology, index, and the existence theorem

These are proposition definitions, not proofs or assumptions of reciprocity.
The norm maps, subgroups, and extensions are the existing Mathlib objects.
-/

namespace Langlands.LocalClassField

universe u v

/-- The actual norm of any finite extension of p-adic fields is proper, and its
image is open of finite index. The index divides the degree, with equality
exactly for abelian Galois extensions. -/
def FiniteNormProperties : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier],
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    let N := Units.map (Algebra.norm F.Carrier (S := E.Carrier))
    IsProperMap N ∧
      IsOpen (N.range : Set F.Carrierˣ) ∧
      N.range.FiniteIndex ∧
      N.range.index ∣ Module.finrank F.Carrier E.Carrier ∧
      (N.range.index = Module.finrank F.Carrier E.Carrier ↔
        IsAbelianGalois F.Carrier E.Carrier)

/-- Each open finite-index subgroup is the norm group of a unique finite abelian
intermediate extension in the actual algebraic closure. -/
def NormSubgroupExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    letI := F.canonicalTopologicalData.topology
    ∀ H : Subgroup F.Carrierˣ, IsOpen (H : Set F.Carrierˣ) → H.FiniteIndex →
      ∃! E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier),
        FiniteDimensional F.Carrier E ∧ IsAbelianGalois F.Carrier E ∧
          (Units.map (Algebra.norm F.Carrier (S := E))).range = H

/-- The norm-group part of local class field theory, with all fields quantified
and no reciprocity system supplied as a hypothesis. -/
def NormGroupTheorems : Prop :=
  FiniteNormProperties.{u, v} ∧ NormSubgroupExistence.{u}

end Langlands.LocalClassField
