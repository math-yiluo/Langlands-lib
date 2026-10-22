import Langlands.VirtualRepresentation.Weil.Generic
import Langlands.Weil.Local.Parameters

/-! # Integral lattices for the actual local Weil group -/

noncomputable section

universe uF uV uQ

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual local irreducible Weil basis over all positive ranks. -/
abbrev Basis := Weil.IrreducibleBasis.{uF, uV} (localWeilGroup F)

/-- The free integral group on actual local irreducible Weil classes. -/
abbrev Lattice := IntegralLattice (Basis.{uF, uV} F)

/-- Dimension of local Weil representations, extended by integer linearity. -/
def degree : Lattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  Weil.degree (localWeilGroup F)

/-- The integral coefficient pairing on actual local irreducible classes. -/
def multiplicityPairing :
    Lattice.{uF, uV} F →ₗ[ℤ] Lattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  pairing

/-- The actual local unitary irreducible classes, with no chosen Hermitian form. -/
abbrev UnitaryBasis := Weil.UnitaryBasis.{uF, uV} (localWeilGroup F)

/-- The free integral group on the specified local unitary irreducible basis. -/
abbrev UnitaryLattice := IntegralLattice (UnitaryBasis.{uF, uV} F)

/-- The corresponding supported sublattice in the full local Weil lattice. -/
def unitarySupported : Submodule ℤ (Lattice.{uF, uV} F) :=
  Weil.unitarySupported (localWeilGroup F)

/-- An actual equivalence of the support and unitary-basis models. -/
def unitaryModel : unitarySupported.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  Weil.unitaryModel (localWeilGroup F)

/-- Include coefficients on local unitary irreducible classes. -/
def includeUnitary : UnitaryLattice.{uF, uV} F →ₗ[ℤ] Lattice.{uF, uV} F :=
  Weil.includeUnitary (localWeilGroup F)

/-- Extract the coefficients on local unitary irreducible classes. -/
def restrictUnitary : Lattice.{uF, uV} F →ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  Weil.restrictUnitary (localWeilGroup F)

/-- Dimension degree restricted to the actual local unitary lattice. -/
def unitaryDegree : UnitaryLattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  Weil.unitaryDegree (localWeilGroup F)

/-- Integral multiplicity pairing on the specified local unitary basis. -/
def unitaryPairing :
    UnitaryLattice.{uF, uV} F →ₗ[ℤ] UnitaryLattice.{uF, uV} F →ₗ[ℤ] ℤ :=
  pairing

/-- Actual finite-image local Weil classes define a support sublattice. -/
def finiteImageSupported : Submodule ℤ (Lattice.{uF, uV} F) :=
  Weil.finiteImageSupported (localWeilGroup F)

/-- Galois type uses a continuous extension along the actual local projection.
It is kept distinct from having finite image. -/
def HasGaloisTypeClass (b : Basis.{uF, uV} F) : Prop :=
  ∃ A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F),
    IsLocalGaloisType F A ∧
      FiniteRepresentation.classOf A = Weil.underlyingClass (localWeilGroup F) b

/-- The actual Galois-type support sublattice. -/
def galoisTypeSupported : Submodule ℤ (Lattice.{uF, uV} F) :=
  supported {b | HasGaloisTypeClass F b}

/-- Restrict Galois-type support to the actual local unitary basis. -/
def unitaryGaloisTypeSupported : Submodule ℤ (UnitaryLattice.{uF, uV} F) :=
  supported {b | HasGaloisTypeClass F b.val}

/-- Algebraic factorization along a specified map from the actual absolute
Galois group into a finite group. Neither continuity nor surjectivity of that
map, nor equivalence with Galois type, is assumed. -/
def finiteFactoringSupported {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup F.Carrier →* Q) :
    Submodule ℤ (Lattice.{uF, uV} F) :=
  Weil.factoringSupported (localWeilGroup F)
    (q.comp (localProjection F).toMonoidHom)

/-- The same actual finite-map factorization support on the unitary basis. -/
def unitaryFiniteFactoringSupported {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup F.Carrier →* Q) :
    Submodule ℤ (UnitaryLattice.{uF, uV} F) :=
  Weil.unitaryFactoringSupported (localWeilGroup F)
    (q.comp (localProjection F).toMonoidHom)

/-- Include classes of a specified positive representation dimension. -/
def includeRank (n : ℕ+) :
    IntegralLattice (LocalContinuousIrreducibleWeilClasses.{uF, uV} F (n : ℕ)) →ₗ[ℤ]
      Lattice.{uF, uV} F :=
  VirtualRepresentation.includeRank
    (fun n : ℕ+ => LocalContinuousIrreducibleWeilClasses.{uF, uV} F (n : ℕ)) n

/-- Extract the coefficients at a specified positive representation dimension. -/
def restrictRank (n : ℕ+) :
    Lattice.{uF, uV} F →ₗ[ℤ]
      IntegralLattice (LocalContinuousIrreducibleWeilClasses.{uF, uV} F (n : ℕ)) :=
  VirtualRepresentation.restrictRank
    (fun n : ℕ+ => LocalContinuousIrreducibleWeilClasses.{uF, uV} F (n : ℕ)) n

/-- The sublattice supported at one positive representation dimension. -/
def rankSupported (n : ℕ+) : Submodule ℤ (Lattice.{uF, uV} F) :=
  VirtualRepresentation.rankSupported
    (fun n : ℕ+ => LocalContinuousIrreducibleWeilClasses.{uF, uV} F (n : ℕ)) n

/-- Effective elements have nonnegative integral multiplicities. -/
def effective : AddSubmonoid (Lattice.{uF, uV} F) :=
  VirtualRepresentation.effective

/-- Unit classes in a specified rank; no finiteness is built in. -/
def unitaryRankStratum (n : ℕ+) : Set (UnitaryBasis.{uF, uV} F) :=
  Weil.unitaryRankStratum (localWeilGroup F) n

/-- A fiber of a supplied invariant on the genuine unitary basis.
No conductor or central-character formula is assumed. -/
def unitaryInvariantStratum {J : Type*}
    (invariant : UnitaryBasis.{uF, uV} F → J) (j : J) :
    Set (UnitaryBasis.{uF, uV} F) := {b | invariant b = j}

/-- A total-degree stratum, distinct from support in a single rank. -/
def degreeStratum (d : ℤ) : Set (Lattice.{uF, uV} F) := {x | degree F x = d}

/-- Effective elements of a fixed total degree, without finiteness assumptions. -/
def effectiveDegreeStratum (d : ℤ) : Set (Lattice.{uF, uV} F) :=
  {x | x ∈ effective F ∧ degree F x = d}

variable {F}

/-- The genuine class of an actual local continuous irreducible representation. -/
def basisClass (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (n : ℕ+) (hrank : A.rank = (n : ℕ)) : Basis.{uF, uV} F :=
  Weil.basisClass A hcontinuous hirreducible n hrank

/-- An actual local continuous irreducible representation as a generator. -/
def ofRepresentation (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (n : ℕ+) (hrank : A.rank = (n : ℕ)) : Lattice.{uF, uV} F :=
  generator (basisClass A hcontinuous hirreducible n hrank)

/-- An actual local unitary irreducible representation in the specified basis. -/
def unitaryBasisClass (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (hunitary : A.IsUnitary) (n : ℕ+) (hrank : A.rank = (n : ℕ)) :
    UnitaryBasis.{uF, uV} F :=
  Weil.unitaryBasisClass A hcontinuous hirreducible hunitary n hrank

/-- An actual local unitary irreducible representation as a unitary generator. -/
def ofUnitaryRepresentation
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (hcontinuous : A.IsContinuous) (hirreducible : A.IsIrreducible)
    (hunitary : A.IsUnitary) (n : ℕ+) (hrank : A.rank = (n : ℕ)) :
    UnitaryLattice.{uF, uV} F :=
  generator (unitaryBasisClass A hcontinuous hirreducible hunitary n hrank)

end Langlands.VirtualRepresentation.LocalWeil
