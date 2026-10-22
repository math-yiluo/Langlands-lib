# Permutation matrices, Weyl elements and inverse transpose

Author: Worker 16. This is a construction group for task
`974e7b2e-4779-4b03-a8a1-6b81962d310c`, revision 2.

The generic constructions act on `Matrix.GeneralLinearGroup (Fin n) R`, which
is definitionally `Langlands.GeneralLinear n R`. Here `R` is any commutative
ring in an arbitrary universe and `n` is any natural number. They therefore
cover every positive rank over a field without adding an invertibility,
decomposition or continuity hypothesis as part of the group data.

## Permutation and Weyl conventions

`GeneralLinear.permutation n R` is a homomorphism from the permutation group of
`Fin n` to the actual matrix unit group. It sends a permutation `σ` to the matrix
whose `(i,j)` entry is one when `σ j = i`, and zero otherwise. In particular, it
sends the standard basis vector `e_j` to `e_(σ j)`. This is a homomorphism because
it lifts Mathlib's `Matrix.permMatrixHom` using `MonoidHom.toHomUnits`.
Mathlib's raw `Equiv.Perm.permMatrix` reverses composition, so the homomorphism
uses the raw matrix of `σ⁻¹`. All inverse and multiplication fields come from
this existing homomorphism, rather than an assumed matrix inverse.

The entry interface proves:

- `(permutation σ * g) i j = g (σ⁻¹ i) j`;
- `(g * permutation σ) i j = g i (σ j)`;
- `(permutation σ * g * (permutation σ)⁻¹) i j = g (σ⁻¹ i) (σ⁻¹ j)`.

The proofs apply `PEquiv.toMatrix_toPEquiv_mul` and
`PEquiv.mul_toMatrix_toPEquiv` to the matrix values of the units.

`GeneralLinear.weylLong n R` is the permutation matrix for `Fin.revPerm`.
Thus its nonzero entries are all one, on the anti-diagonal. The entry test is
`j.rev = i`, where the value of `j.rev` is `n - 1 - j`. Its inverse is itself and
its square is the identity. Left multiplication reverses rows, right multiplication
reverses columns, and conjugation reverses both. No alternating signs are inserted.
Permutation injectivity over a trivial ring is not asserted.

## Inverse transpose and continuous maps

`GeneralLinear.inverseTranspose n R` is an involutive multiplicative equivalence
sending `g` to the transpose of its unit inverse, so its `(i,j)` entry is
`g⁻¹ j i`. The new unit's inverse is the transpose of the original matrix.
Transposing the original two unit identities proves the new unit fields.
Inversion and transposition each reverse multiplication, which proves
multiplicativity. Double transposition proves the two inverse-function laws.
The resulting automorphism fixes every permutation matrix, and therefore fixes
the chosen long Weyl representative.

With any `TopologicalSpace R`, `inverseTransposeContinuous` bundles this same
map as a continuous multiplicative equivalence. Mathlib's topology on matrix
units records both the value and inverse value. These become, respectively,
the transposes of the old inverse value and value. Both are continuous by
`Units.continuous_coe_inv`, `Units.continuous_val`, and coordinatewise matrix
transposition. This particular result needs no continuity assumption on the
ring operations.

With `[IsTopologicalRing R]`, `permutationConjugation n R σ` bundles conjugation
by the specified permutation matrix as a continuous multiplicative equivalence.
It uses `MulAut.conj`, and continuity of multiplication proves continuity of
both directions.

Under the same topological-ring hypothesis, `weylInverseTranspose n R` is the
homeomorphism
`g ↦ weylLong n R * inverseTranspose n R g`.
It is the composition of inverse transpose with the left-translation
homeomorphism. Its `(i,j)` entry is `g⁻¹ j i.rev`. Its square is the identity:
inverse transpose is multiplicative, fixes `weylLong`, and is involutive, while
`weylLong` squares to one. This map is not declared to be a group homomorphism.

## Every finite p-adic extension

For every prime `p`, every accepted `F : PadicField p` in any universe and every
supplied `T : F.TopologicalData`, the three `TopologicalData.generalLinear...`
definitions specialize inverse transpose, permutation conjugation and the
Weyl--inverse-transpose homeomorphism. They use precisely `T.topology`.
The latter two install the existing `T.valuativeRel` and `T.localField`
certificates to obtain the topological-ring instance. They do not assume an
extra topological property of the matrix group.

The three `canonicalGeneralLinear...` abbreviations use the accepted
`F.canonicalTopologicalData`. They therefore need only the algebraic p-adic
field, not a caller-supplied realization. They introduce no global field
topology and make no identification between spectral and residue-normalized
absolute values. The generic entry formulas still describe the underlying maps
of all these specializations.

## Source and exact dependencies

The anti-diagonal representative and inverse-transpose convention are those of
Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des représentations du groupe
linéaire* (1981), section 1.2, formula (3), printed page 200 (PDF page 2).
The original page was inspected. Literature ID: `jpss-1981-conductor`;
SHA-256: `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
Its formula is `W̃(g) = W(w_r (g⁻¹)ᵀ)`: it uses left multiplication by the long
Weyl representative, not conjugation by that representative. The current file
formalizes the matrix maps only; it does not assert a theorem on Whittaker models.
The extension to arbitrary commutative rings, permutation conjugation,
topological packaging and intrinsic map proofs are internal constructions.

The imported `Langlands.Group.GL.Padic`, together with its companion
`Langlands.Group.GL.Basic`, is accepted definition artifact
`cd1132db-8cab-4cab-bd28-0c6164b44dbe`, version 1, published at commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, with independent semantic receipt
`7c88f2621a5047a9a85fe9ef375a8ed0`. Its final validation uses an incremental
Lake build and exact declaration inspection. A fresh fetch verifies acceptance,
publication and current Library membership without missing files or unavailable
dependencies. The complete effective Basic/Padic pairs and final review were
read, and their source hashes match the local imported files.

The exact transitive local-field definitions are:

- `Langlands.LocalField.Definitions`, artifact
  `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1, publication commit
  `1fe07fd211e579cc430734fd96ce959aadb7663d`.
- `Langlands.LocalField.Canonical`, artifact
  `c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629`, version 1, publication commit
  `9db46907db3181b0c1dfd287b8ab2f1f02054cab`.

Their complete effective Lean/Markdown pairs were read and their exact hashes
match the dependency closure of the published core construction. Basic and
Padic are Worker 6's work; their imported constructions are reused without
modification. This file introduces no new field or general-linear-group wrapper.

The pinned environment is Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The specific reused APIs were
audited in `LinearAlgebra.Matrix.Permutation`, `Data.Matrix.PEquiv`,
`Data.Fin.Rev`, `Algebra.Group.Units.Hom`, `Topology.Algebra.Group.Units`,
`Topology.Algebra.Group.Matrix` and `Topology.Instances.Matrix`.
Native compilation of this unchanged Lean source and its exact dependency
modules completed without errors or warnings. Compilation is development
evidence; independent semantic review and publication establish acceptance.
