import Langlands.VirtualRepresentation.Integral
import Langlands.Weil.Representation.Predicates

/-!
# Integral combinations of actual continuous irreducible representations

The input is a group with a topology. This adapter uses the genuine
finite-dimensional representation classes supplied by the parameter branch.
Specialization to an actual local Weil group is a further construction.
-/

noncomputable section

universe uG uV uH

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Actual continuous irreducible complex classes, across positive ranks.
The carrier universe is fixed independently of the group universe. -/
abbrev IrreducibleBasis :=
  RankedBasis (fun n => ContinuousIrreducibleClasses.{uG, uV} G (n : ℕ))

/-- Finite integral combinations of the actual irreducible classes. -/
abbrev IrreducibleLattice := IntegralLattice (IrreducibleBasis.{uG, uV} G)

/-- The underlying representation-isomorphism class, forgetting the rank label
and the continuous-irreducible condition. -/
def underlyingClass (b : IrreducibleBasis.{uG, uV} G) :
    IsomorphismClasses.{0, uG, uV} ℂ G :=
  forgetPropertyClass _ b.2.val

/-- The integral rank-weighted degree. It can be negative on virtual elements. -/
def degree : IrreducibleLattice.{uG, uV} G →ₗ[ℤ] ℤ :=
  rankedDegree (fun n => ContinuousIrreducibleClasses.{uG, uV} G (n : ℕ))

/-- The integral coefficient pairing on all continuous irreducible classes.
No assertion about Hom dimensions or local factors is included. -/
def multiplicityPairing :
    IrreducibleLattice.{uG, uV} G →ₗ[ℤ] IrreducibleLattice.{uG, uV} G →ₗ[ℤ] ℤ :=
  pairing

/-- The genuine isomorphism class has an actual finite-image representative.
No equivalence with Galois type or finite-order determinant is assumed. -/
def HasFiniteImageClass (b : IrreducibleBasis.{uG, uV} G) : Prop :=
  ∃ A : FiniteRepresentation.{0, uG, uV} ℂ G,
    A.HasFiniteImage ∧ FiniteRepresentation.classOf A = underlyingClass G b

/-- The sublattice supported on actual finite-image irreducible classes. -/
def finiteImageSupported : Submodule ℤ (IrreducibleLattice.{uG, uV} G) :=
  supported {b | HasFiniteImageClass G b}

/-- Algebraic factorization along a supplied group homomorphism, up to genuine
representation isomorphism. No topology on the target group, continuity of the
factor representation, or surjectivity of the group map is asserted. -/
def FactorsThrough {H : Type uH} [Group H] (f : G →* H)
    (b : IrreducibleBasis.{uG, uV} G) : Prop :=
  ∃ A : FiniteRepresentation.{0, uH, uV} ℂ H,
    FiniteRepresentation.classOf (FiniteRepresentation.of (A.representation.comp f)) =
      underlyingClass G b

/-- The span of irreducible classes factoring through the specified actual map.
In applications the map may be the local map to a finite Galois quotient. -/
def factoringSupported {H : Type uH} [Group H] (f : G →* H) :
    Submodule ℤ (IrreducibleLattice.{uG, uV} G) :=
  supported {b | FactorsThrough G f b}

/-- A class is unitary if its genuine isomorphism class contains an actual
unitarizable representation. This defines a predicate on the quotient directly;
it does not assume an unproved invariance theorem or choose a Hermitian form. -/
def IsUnitaryClass (b : IrreducibleBasis.{uG, uV} G) : Prop :=
  ∃ A : FiniteRepresentation.{0, uG, uV} ℂ G,
    A.IsUnitary ∧ FiniteRepresentation.classOf A = underlyingClass G b

/-- The subset of the irreducible basis consisting of genuine unitary classes. -/
def unitarySet : Set (IrreducibleBasis.{uG, uV} G) := {b | IsUnitaryClass G b}

/-- The specified unitary basis, without a choice of representatives or forms. -/
abbrev UnitaryBasis := unitarySet.{uG, uV} G

/-- The integral lattice on the specified unitary basis. -/
abbrev UnitaryLattice := IntegralLattice (UnitaryBasis.{uG, uV} G)

/-- Integral combinations whose irreducible support is unitary. -/
def unitarySupported : Submodule ℤ (IrreducibleLattice.{uG, uV} G) :=
  supported (unitarySet G)

/-- The supported sublattice and the unitary-basis model are actually equivalent. -/
def unitaryModel :
    unitarySupported.{uG, uV} G ≃ₗ[ℤ] UnitaryLattice.{uG, uV} G :=
  supportedEquiv (unitarySet G)

/-- Include the unitary-basis lattice into the full irreducible lattice. -/
def includeUnitary :
    UnitaryLattice.{uG, uV} G →ₗ[ℤ] IrreducibleLattice.{uG, uV} G :=
  includeSubset (unitarySet G)

/-- Extract the coefficients of genuine unitary classes. -/
def restrictUnitary :
    IrreducibleLattice.{uG, uV} G →ₗ[ℤ] UnitaryLattice.{uG, uV} G :=
  restrictSubset (unitarySet G)

/-- Degree restricted to the actual unitary lattice. -/
def unitaryDegree : UnitaryLattice.{uG, uV} G →ₗ[ℤ] ℤ :=
  (degree G).comp (includeUnitary G)

/-- Integral multiplicity pairing with the specified unitary basis orthonormal. -/
def unitaryPairing :
    UnitaryLattice.{uG, uV} G →ₗ[ℤ] UnitaryLattice.{uG, uV} G →ₗ[ℤ] ℤ :=
  pairing

/-- Unitary classes in a specified positive rank; no finiteness is assumed. -/
def unitaryRankStratum (n : ℕ+) : Set (UnitaryBasis.{uG, uV} G) :=
  {b | b.val.1 = n}

/-- The unitary sublattice supported on classes factoring through an actual map. -/
def unitaryFactoringSupported {H : Type uH} [Group H] (f : G →* H) :
    Submodule ℤ (UnitaryLattice.{uG, uV} G) :=
  supported {b | FactorsThrough G f b.val}

variable {G}

/-- Send an actual continuous irreducible representation of the specified
positive rank to the disjoint union of its genuine isomorphism classes. -/
def basisClass (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (n : ℕ+) (hrank : A.rank = (n : ℕ)) : IrreducibleBasis.{uG, uV} G :=
  ⟨n, ⟨Quotient.mk _ ⟨A, hcontinuous, hirreducible⟩, hrank⟩⟩

/-- A supplied actual unitary representation gives a member of the unitary basis.
The witness is retained only propositionally, not selected from its class. -/
def unitaryBasisClass (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (hunitary : A.IsUnitary) (n : ℕ+) (hrank : A.rank = (n : ℕ)) :
    UnitaryBasis.{uG, uV} G :=
  ⟨basisClass A hcontinuous hirreducible n hrank, A, hunitary, rfl⟩

/-- An actual continuous irreducible representation as a lattice generator. -/
def ofRepresentation (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (n : ℕ+) (hrank : A.rank = (n : ℕ)) : IrreducibleLattice.{uG, uV} G :=
  generator (basisClass A hcontinuous hirreducible n hrank)

/-- An actual continuous irreducible unitary representation in the unitary lattice. -/
def ofUnitaryRepresentation (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (hunitary : A.IsUnitary) (n : ℕ+) (hrank : A.rank = (n : ℕ)) :
    UnitaryLattice.{uG, uV} G :=
  generator (unitaryBasisClass A hcontinuous hirreducible hunitary n hrank)

end Langlands.VirtualRepresentation.Weil
