import Langlands.LocalField.Extension
import Mathlib.NumberTheory.Padics.LocalField

/-!
# Finite extensions of the p-adic numbers

`PadicField p` contains only algebraic data. Its norm and normed-field structures
are the existing Mathlib spectral constructions. `PadicField.TopologicalData`
separately records a local-field structure with the canonical module topology.
No constructor of `TopologicalData` for an arbitrary `PadicField` is asserted.

Sources: Henniart (2000), Section 1.1, page 439; Serre, *Local Fields* (1979),
Chapter II, Sections 1-2, pages 26-30. See the paired Markdown for normalization
conventions, exact citation receipts, and the Mathlib audit.
-/

namespace Langlands

universe u

/-- A p-adic field is a field with a specified finite extension structure over
Mathlib's `Padic p`. The prime is a parameter, not a fixed project constant. -/
structure PadicField (p : ℕ) [Fact p.Prime] where
  Carrier : Type u
  [field : Field Carrier]
  [algebra : Algebra (Padic p) Carrier]
  [finiteDimensional : FiniteDimensional (Padic p) Carrier]

attribute [instance] PadicField.field PadicField.algebra PadicField.finiteDimensional

namespace PadicField

variable {p : ℕ} [Fact p.Prime]

/-- Package any specified finite field extension of `Padic p`. -/
def ofField (K : Type u) [Field K] [Algebra (Padic p) K]
    [FiniteDimensional (Padic p) K] : PadicField.{u} p where
  Carrier := K

/-- The unique extended p-adic norm, reusing Mathlib's spectral norm.
It extends the base norm; it is not the residue-cardinality normalization. -/
noncomputable def canonicalNorm (F : PadicField.{u} p) : F.Carrier → ℝ :=
  spectralNorm (Padic p) F.Carrier

/-- Mathlib's spectral construction of the nontrivially normed field.
This is explicit data, not a global instance replacing a user's existing norm. -/
noncomputable abbrev canonicalNormedField (F : PadicField.{u} p) :
    NontriviallyNormedField F.Carrier :=
  LocalField.canonicalNormedField (Padic p) F.Carrier

/-- The compatible normed algebra for the spectral norm. -/
noncomputable abbrev canonicalNormedAlgebra (F : PadicField.{u} p) :
    letI := F.canonicalNormedField
    NormedAlgebra (Padic p) F.Carrier :=
  LocalField.canonicalNormedAlgebra (Padic p) F.Carrier

/-- The canonical topology as the topology of a finite-dimensional module
over the usual topological field `Padic p`. -/
noncomputable abbrev canonicalTopology (F : PadicField.{u} p) : TopologicalSpace F.Carrier :=
  LocalField.canonicalTopology (Padic p) F.Carrier

/-- A local-field realization of the algebraic extension, with the canonical
module topology. The valuation is specified up to equivalence by `ValuativeRel`.
Local compactness is an explicit certified requirement of `localField`. -/
structure TopologicalData (F : PadicField.{u} p) where
  [topology : TopologicalSpace F.Carrier]
  [valuativeRel : ValuativeRel F.Carrier]
  [valuativeExtension : ValuativeExtension (Padic p) F.Carrier]
  [moduleTopology : IsModuleTopology (Padic p) F.Carrier]
  [localField : IsNonarchimedeanLocalField F.Carrier]

/-- View the same supplied realization over the general base interface.
Every field is copied unchanged, so its integer ring is definitionally the same. -/
abbrev TopologicalData.toLocalData {F : PadicField.{u} p} (T : F.TopologicalData) :
    LocalField.TopologicalData (Padic p) F.Carrier where
  topology := T.topology
  valuativeRel := T.valuativeRel
  valuativeExtension := T.valuativeExtension
  moduleTopology := T.moduleTopology
  localField := T.localField

/-- Package a general realization over `Padic p` using the existing interface. -/
abbrev TopologicalData.ofLocalData {F : PadicField.{u} p}
    (T : LocalField.TopologicalData (Padic p) F.Carrier) : F.TopologicalData where
  topology := T.topology
  valuativeRel := T.valuativeRel
  valuativeExtension := T.valuativeExtension
  moduleTopology := T.moduleTopology
  localField := T.localField

/-- The degree-one algebraic base example, with the identity algebra structure. -/
noncomputable def rational (p : ℕ) [Fact p.Prime] : PadicField.{0} p :=
  ofField (Padic p)

/-- The usual topology and valuation on `Padic p`, with Mathlib's existing
local-field and module-topology certificates. -/
noncomputable def rationalTopologicalData (p : ℕ) [Fact p.Prime] :
    (rational p).TopologicalData where
  topology := inferInstanceAs (TopologicalSpace (Padic p))
  valuativeRel := inferInstanceAs (ValuativeRel (Padic p))
  valuativeExtension :=
    (show ValuativeExtension (Padic p) (Padic p) from ⟨fun _ _ => Iff.rfl⟩)
  moduleTopology := inferInstanceAs (IsModuleTopology (Padic p) (Padic p))
  localField := inferInstanceAs (IsNonarchimedeanLocalField (Padic p))

end PadicField

end Langlands
