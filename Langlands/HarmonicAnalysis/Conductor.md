# Character conductors on the specified p-adic field

Worker 20 constructs the additive and multiplicative character conductors from
the actual discrete valuation of `T : F.TopologicalData`. The field is an
arbitrary finite extension of the specified `Q_p`, with its independently
supplied topological realization. The module uses the common
`UnitaryAdditiveCharacter` and `Quasicharacter` types. Its constructions do not
assume conductor certificates, reciprocity, self-dual measure, or a system of
epsilon constants.

`additiveLattice T n` is the additive subgroup defined by
`T.discreteValuation x ≤ exp n`. Thus its order convention is
`v_F(x) ≥ -n`, including zero, and its mathematical meaning is the
fractional ideal `π^(-n) O_F`. The index increases as the lattice grows.
The zero, addition and negation conditions follow from the valuation.
The module proves this fractional-ideal identification explicitly:
membership is equivalent to `x / T.uniformizer^(-n)` belonging to the actual
`T.Integers`. It proves that the discrete and underlying valuations have the
same integer ring and derives the chosen uniformizer's valuation directly
from the accepted constructor. In particular the level-zero lattice is
exactly the actual integer ring. No normalization theorem from a pending
project proof is imported.

The proof of `exists_additiveLattice_subset` transports the actual valuative
neighborhood basis through the ordered value-group isomorphism to
`WithZero (Multiplicative Int)`. It picks a strictly smaller integer level.
Continuity of an additive character then gives a lattice mapping into the
open right half-circle. All positive integer multiples remain in that
lattice, so all powers of each character value remain in the half-circle.
Mathlib's proved circle lemma forces each value to be one.

Nontriviality supplies a vector whose value is not one. Its discrete valuation
bounds all integer levels of triviality above. The integer greatest-element
theorem therefore proves that the conductor exists. `additiveConductor`
chooses only from this proved theorem, and `additiveConductor_spec` retains
both triviality and maximality. The module also proves the exact criterion
for triviality at every integer level and nontriviality on the next lattice.

`principalUnits T n` is a subgroup of the actual field-unit group. Its
membership conditions are `v(u)=1` and `v(u-1) ≤ exp(-n)`. The subgroup
conditions follow from multiplicativity and the ultrametric inequality,
using `uv-1 = u(v-1)+(u-1)` and
`u⁻¹-1 = -(u-1)u⁻¹`. The subgroups decrease with `n`. At level zero the
second condition is automatic, so `U⁰` is exactly the integral units.
The congruence condition is explicitly identified with
`(u-1)/π^n ∈ O`, using the same uniformizer and integer ring as the
additive construction.

These subgroups are proved cofinal in the neighborhoods of one in the
field-unit group. The proof uses the topological embedding of field units
into the field, translates an ambient neighborhood by one, and applies
the additive-lattice cofinality theorem. A continuous complex quasicharacter
therefore maps some `Uⁿ` into the disk of radius `1/2` around one. All powers
remain in `Uⁿ`, so the accepted complex power estimate forces every value
there to equal one. This works for arbitrary continuous quasicharacters;
unitarity is not an additional hypothesis.

`multiplicativeConductor` is `Nat.find` of this proved existence result.
The module proves its defining triviality, minimality, the equivalence
between triviality on `Uⁿ` and `a(χ) ≤ n`, and a nontrivial value at every
strictly lower level. `IsUnramifiedQuasicharacter` means triviality on
all actual integral units, and the conductor is zero exactly in that case.
The lattice and unit filtrations are actual subgroups, not free input data.

The conventions are J. Tate, *Number theoretic background*, Corvallis Part II
(1979), section 3.2.6, printed page 13 (retained PDF page 22):
`n(ψ)` is the largest integer such that the character is trivial on
`π^(-n) O`, whereas `a(χ)` is zero in the unramified case and otherwise
the least unit-congruence level of triviality.
Registered source `tate-1979-number-theoretic-background`, content SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
file `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
The original page was read visually. The least/greatest-element constructions
and the existence arguments are implementation choices proving the intrinsic
obligations of these source definitions.

The project imports are present in the independently reviewed Library at commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`:

- `Langlands.HarmonicAnalysis.Basic` supplies the character types.
- `Langlands.LocalField.Normalization.Definitions` supplies the actual
  discrete valuation, uniformizer, and integer ring. Its import
  `Langlands.LocalField.Definitions` supplies the field and
  topological-realization interface.
- `Langlands.Representation.Twist.ContinuousCharacterProof` supplies
  `Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt`. The latter is
  the proved geometric-sum estimate, not a no-small-subgroups assumption.
  Its published statement is
  `Langlands.ContinuousComplexCharacterOpenKernel`.
- The pinned environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`,
  version 1: Lean 4.34.0 and Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`. Mathlib supplies the valuative
  neighborhood basis, circle power lemma, unit embedding, and integer/natural
  extremal-element theorems used in the proofs.

Native compilation of the complete module succeeded without diagnostics.
This is a development check, not independent acceptance or publication.
The abelian epsilon expressions, conductor transformation theorems, local
functional equations, and the nonabelian epsilon-system theorem are separate
obligations. This module defines or assumes no epsilon constant.
