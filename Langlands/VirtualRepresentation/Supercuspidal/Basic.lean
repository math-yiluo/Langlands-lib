import Langlands.VirtualRepresentation.Integral
import Langlands.Representation.Classification.Supercuspidal

/-!
# Integral lattices on actual supercuspidal classes

The basis consists of genuine supercuspidal representation isomorphism classes,
over all positive ranks. The rank is the size of the general linear group;
representation carriers have neither a dimension nor a topology restriction.
-/

noncomputable section

universe uF uV uA

namespace Langlands.VirtualRepresentation.Supercuspidal

variable (F : Type uF) [Field F] [TopologicalSpace F]

/-- Genuine supercuspidal classes in each positive group rank. -/
abbrev ClassFamily (n : ℕ+) :=
  GeneralLinear.SupercuspidalClass.{uV, uF} (F := F) (n := (n : ℕ))

/-- The disjoint union of actual classes of supercuspidal representations. -/
abbrev Basis := RankedBasis (ClassFamily.{uF, uV} F)

/-- The free integral group on supercuspidal classes, with finite support. -/
abbrev Lattice := IntegralLattice (Basis.{uF, uV} F)

/-- The underlying irreducible admissible class in its actual group rank. -/
def underlyingClass (b : Basis.{uF, uV} F) :
    SmoothDualClass.{0, uF, uV} (k := ℂ) (G := GeneralLinear (b.1 : ℕ) F) :=
  GeneralLinear.SupercuspidalClass.toSmoothDualClass b.2

/-- Integral degree weighted by the positive rank of the general linear group. -/
def degree : Lattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  rankedDegree (ClassFamily.{uF, uV} F)

/-- Integral multiplicity pairing on the actual supercuspidal basis. -/
def multiplicityPairing : Lattice.{uF, uV} F →ₗ[ℤ] Lattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  pairing

/-- Include classes in one positive group rank, retaining that rank label. -/
def includeRank (n : ℕ+) :
    IntegralLattice (ClassFamily.{uF, uV} F n) →ₗ[ℤ] Lattice.{uF, uV} F :=
  VirtualRepresentation.includeRank (ClassFamily.{uF, uV} F) n

/-- Extract the coefficients in one positive group rank. -/
def restrictRank (n : ℕ+) :
    Lattice.{uF, uV} F →ₗ[ℤ] IntegralLattice (ClassFamily.{uF, uV} F n) :=
  VirtualRepresentation.restrictRank (ClassFamily.{uF, uV} F) n

/-- Elements supported on a single group rank, distinct from total degree. -/
def rankSupported (n : ℕ+) : Submodule ℤ (Lattice.{uF, uV} F) :=
  VirtualRepresentation.rankSupported (ClassFamily.{uF, uV} F) n

/-- A total-degree stratum of the virtual lattice. No finiteness is asserted. -/
def degreeStratum (d : ℤ) : Set (Lattice.{uF, uV} F) :=
  {x | degree F x = d}

/-- Nonnegative integral combinations of the given supercuspidal classes. -/
def effective : AddSubmonoid (Lattice.{uF, uV} F) :=
  VirtualRepresentation.effective

/-- Effective elements of specified degree; this definition supplies no count. -/
def effectiveDegreeStratum (d : ℤ) : Set (Lattice.{uF, uV} F) :=
  {x | x ∈ effective F ∧ degree F x = d}

/-- The descended existence of an invariant positive Hermitian form. -/
def IsUnitaryClass (b : Basis.{uF, uV} F) : Prop :=
  GeneralLinear.SupercuspidalClass.IsUnitarizable b.2

/-- The actual subset of unitarizable supercuspidal classes. -/
def unitarySet : Set (Basis.{uF, uV} F) := {b | IsUnitaryClass F b}

/-- The unitary basis is a subset of the genuine supercuspidal basis. -/
abbrev UnitaryBasis := unitarySet.{uF, uV} F

/-- The free integral group on precisely the unitary supercuspidal classes. -/
abbrev UnitaryLattice := IntegralLattice (UnitaryBasis.{uF, uV} F)

/-- The equivalent supported model inside the full supercuspidal lattice. -/
def unitarySupported : Submodule ℤ (Lattice.{uF, uV} F) :=
  supported (unitarySet F)

/-- The support condition and the unitary coefficient model are equivalent. -/
def unitaryModel :
    unitarySupported.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  supportedEquiv (unitarySet F)

/-- Include unitary supercuspidal coefficients. -/
def includeUnitary : UnitaryLattice.{uF, uV} F →ₗ[ℤ] Lattice.{uF, uV} F :=
  includeSubset (unitarySet F)

/-- Restrict coefficients to the genuine unitary subset. -/
def restrictUnitary : Lattice.{uF, uV} F →ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  restrictSubset (unitarySet F)

/-- The positive group-rank weight on the unitary basis. -/
def unitaryDegree : UnitaryLattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  (degree F).comp (includeUnitary F)

/-- Integral multiplicity pairing with the unitary supercuspidal basis orthonormal. -/
def unitaryPairing :
    UnitaryLattice.{uF, uV} F →ₗ[ℤ] UnitaryLattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  pairing

/-- The actual unitary classes in a specified positive group rank. -/
def unitaryRankStratum (n : ℕ+) : Set (UnitaryBasis.{uF, uV} F) :=
  {b | b.val.1 = n}

/-- A rank and invariant fiber of the actual unitary basis.
The invariant must be supplied as a genuine function; no finiteness is asserted. -/
def unitaryBasisStratum {A : Type uA} (invariant : UnitaryBasis.{uF, uV} F → A)
    (n : ℕ+) (a : A) : Set (UnitaryBasis.{uF, uV} F) :=
  {b | b.val.1 = n ∧ invariant b = a}

variable {F}

/-- An actual supercuspidal object gives its basis class at the group rank. -/
def basisClass (n : ℕ+)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F) (n := (n : ℕ))) :
    Basis.{uF, uV} F :=
  ⟨n, A.isoClass⟩

/-- A positive invariant form witness places the actual class in the unitary basis. -/
def unitaryBasisClass (n : ℕ+)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F) (n := (n : ℕ)))
    (hunitary : Langlands.IsUnitarizable A.obj.representation) :
    UnitaryBasis.{uF, uV} F :=
  ⟨basisClass n A, hunitary⟩

/-- The multiplicity-one generator attached to an actual supercuspidal object. -/
def ofRepresentation (n : ℕ+)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F) (n := (n : ℕ))) :
    Lattice.{uF, uV} F :=
  generator (basisClass n A)

/-- An actual unitary supercuspidal object as a multiplicity-one generator. -/
def ofUnitaryRepresentation (n : ℕ+)
    (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F) (n := (n : ℕ)))
    (hunitary : Langlands.IsUnitarizable A.obj.representation) :
    UnitaryLattice.{uF, uV} F :=
  generator (unitaryBasisClass n A hunitary)

end Langlands.VirtualRepresentation.Supercuspidal

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime]

/-- The actual positive-rank supercuspidal basis over the canonical p-adic topology. -/
abbrev Basis (F : PadicField.{uF} p) :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.Basis.{uF, uV} F.Carrier

/-- The automorphic-side free integral group for an actual p-adic field. -/
abbrev Lattice (F : PadicField.{uF} p) := IntegralLattice (Basis.{uF, uV} F)

/-- Degree is the size of the actual general linear group, extended integrally. -/
def degree (F : PadicField.{uF} p) : Lattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.degree F.Carrier

/-- The actual unitary supercuspidal basis over the canonical p-adic topology. -/
abbrev UnitaryBasis (F : PadicField.{uF} p) :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.UnitaryBasis.{uF, uV} F.Carrier

/-- The free integral group on actual unitary supercuspidal classes. -/
abbrev UnitaryLattice (F : PadicField.{uF} p) :=
  IntegralLattice (UnitaryBasis.{uF, uV} F)

/-- The actual inclusion of the unitary basis lattice. -/
def includeUnitary (F : PadicField.{uF} p) :
    UnitaryLattice.{uF, uV} F →ₗ[ℤ] Lattice.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.includeUnitary F.Carrier

/-- Integral degree on the specified unitary basis. -/
def unitaryDegree (F : PadicField.{uF} p) : UnitaryLattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  (degree F).comp (includeUnitary F)

/-- Integral multiplicity pairing on actual unitary supercuspidal classes. -/
def unitaryPairing (F : PadicField.{uF} p) :
    UnitaryLattice.{uF, uV} F →ₗ[ℤ] UnitaryLattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  pairing

end Langlands.VirtualRepresentation.PadicSupercuspidal
