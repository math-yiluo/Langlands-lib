import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Equiv
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Compactness.LocallyCompact

open Topology

namespace Langlands

/-- One ambient compact open subgroup detects a finite family of nonzero types
of an open subgroup, and every simple subrepresentation actually equivalent to
a member of that family. The compact open subgroup is chosen before the second
representation. -/
def FiniteTypeCompactOpenDetectionStatement.{uR, uG, uV, uW, uI} : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V), IsSmooth ρ →
    ∀ (H : OpenSubgroup G) (ι : Type uI) [Finite ι]
      (T : ι → Subrepresentation (ρ.comp H.toSubgroup.subtype)),
    (∀ i, T i ≠ ⊥) → ∀ (U : Set G), U ∈ 𝓝 (1 : G) →
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧
      K.toSubgroup ≤ H.toSubgroup ∧
      (∀ i, ∃ v : (T i).toSubmodule,
        v ∈ fixedVectors (T i).toRepresentation
          (K.toSubgroup.comap H.toSubgroup.subtype) ∧ v ≠ 0) ∧
      ∀ (W : Type uW) [AddCommGroup W] [Module R W] (σ : Representation R G W),
        (∀ S : Subrepresentation (σ.comp H.toSubgroup.subtype), IsAtom S →
          ∃ i, Nonempty ((T i).toRepresentation.Equiv S.toRepresentation)) →
        ∀ S : Subrepresentation (σ.comp H.toSubgroup.subtype), IsAtom S →
          ∃ w : W, w ∈ S ∧ w ∈ fixedVectors σ K.toSubgroup ∧ w ≠ 0

end Langlands
