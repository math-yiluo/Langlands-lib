import Langlands.Representation.RestrictedTensor.Smooth
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Admissibility and equivalence of constructed restricted tensor representations

These proposition definitions express Flath's section 2, Example 2, and the
local-factor uniqueness consequence for representations already constructed as
restricted tensors. General existence of a factorization is a separate target.
-/

namespace Langlands

open RestrictedTensor

universe uI uG uV uW

/-- Admissible local factors with one-dimensional reference-subgroup fixed
spaces almost everywhere give an admissible restricted tensor representation. -/
def RestrictedTensorAdmissibilityStatement : Prop :=
  ∀ (ι : Type uI) (G : ι → Type uG) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (E : Finset ι) (r : ReferenceVectors V E)
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi),
    (∀ i, IsOpen (H i : Set (G i)) ∧ IsCompact (H i : Set (G i))) →
    (∀ i, IsAdmissible (ρ i)) →
    (∀ᶠ i in Filter.cofinite, Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1) →
    IsAdmissible (productRepresentation H ρ E r hr)

/-- For the admissible construction of Example 2, global irreducibility is
equivalent to irreducibility of every local factor. -/
def RestrictedTensorIrreducibilityStatement : Prop :=
  ∀ (ι : Type uI) (G : ι → Type uG) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (E : Finset ι) (r : ReferenceVectors V E)
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi),
    (∀ i, IsOpen (H i : Set (G i)) ∧ IsCompact (H i : Set (G i))) →
    (∀ i, IsAdmissible (ρ i)) →
    (∀ᶠ i in Filter.cofinite, Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1) →
    ((productRepresentation H ρ E r hr).IsIrreducible ↔ ∀ i, (ρ i).IsIrreducible)

/-- The equivalence class of the constructed representation is independent
of the nonzero reference vectors in the almost-everywhere fixed lines.
Local irreducibility is not required. -/
def RestrictedTensorReferenceIndependenceStatement : Prop :=
  ∀ (ι : Type uI) (G : ι → Type uG) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (E E' : Finset ι) (r : ReferenceVectors V E) (r' : ReferenceVectors V E')
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi)
    (hr' : ∀ i (hi : i ∉ E'), ∀ g ∈ H i, ρ i g (r'.vector i hi) = r'.vector i hi),
    (∀ i, IsOpen (H i : Set (G i)) ∧ IsCompact (H i : Set (G i))) →
    (∀ i, IsAdmissible (ρ i)) →
    (∀ᶠ i in Filter.cofinite, Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1) →
    Nonempty ((productRepresentation H ρ E r hr).Equiv
      (productRepresentation H ρ E' r' hr'))

/-- Equivalence of two constructed tensors of admissible irreducible factors
determines every local factor up to equivariant linear equivalence. -/
def RestrictedTensorFactorUniquenessStatement : Prop :=
  ∀ (ι : Type uI) (G : ι → Type uG) [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (V : ι → Type uV) (W : ι → Type uW)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (σ : ∀ i, Representation ℂ (G i) (W i))
    (E E' : Finset ι) (r : ReferenceVectors V E) (s : ReferenceVectors W E')
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi)
    (hs : ∀ i (hi : i ∉ E'), ∀ g ∈ H i, σ i g (s.vector i hi) = s.vector i hi),
    (∀ i, IsOpen (H i : Set (G i)) ∧ IsCompact (H i : Set (G i))) →
    (∀ i, IsAdmissible (ρ i) ∧ (ρ i).IsIrreducible) →
    (∀ i, IsAdmissible (σ i) ∧ (σ i).IsIrreducible) →
    (∀ᶠ i in Filter.cofinite, Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1) →
    (∀ᶠ i in Filter.cofinite, Module.finrank ℂ (fixedVectors (σ i) (H i)) = 1) →
    Nonempty ((productRepresentation H ρ E r hr).Equiv
      (productRepresentation H σ E' s hs)) →
    ∀ i, Nonempty ((ρ i).Equiv (σ i))

/-- The admissibility, irreducibility, reference independence and factor
uniqueness assertions for actual restricted tensor representations. -/
def FlathRestrictedTensorStatement : Prop :=
  RestrictedTensorAdmissibilityStatement.{uI, uG, uV} ∧
  RestrictedTensorIrreducibilityStatement.{uI, uG, uV} ∧
  RestrictedTensorReferenceIndependenceStatement.{uI, uG, uV} ∧
  RestrictedTensorFactorUniquenessStatement.{uI, uG, uV, uW}

end Langlands
