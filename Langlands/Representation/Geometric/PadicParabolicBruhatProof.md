# Parabolic Bruhat parametrization for actual p-adic general linear groups

Author: Worker 176. The proof uses the published matrix existence theorem of
Worker 6, Weyl-class reflection theorem of Worker 179, and minimal Weyl
representative theorem of Worker 243.

`Langlands.Geometric.padicParabolicBruhat.{u}` proves the unchanged proposition
`Langlands.Geometric.PadicParabolicBruhatTheorem.{u}` from `WeylStatement`.
For every prime `p`, every actual `F : PadicField.{u} p`, every positive
rank `n`, and every pair of ordered positive block shapes `B C : BlockShape n`,
the actual map

```text
MinimalRepresentatives B C → P_B \ GL_n(F) / P_C
w ↦ the double coset of (permutation n F.Carrier w.val)⁻¹
```

is bijective. The carrier universe is arbitrary. All representative existence,
Weyl bijectivity, and reflection premises are discharged by imported proofs.

## Assembly over a commutative ring

`parabolicDoubleCoset_bijective_of_matrix_conditions` works over an arbitrary
commutative ring and every natural rank, under three explicit hypotheses:
bijectivity of `weylDoubleCoset B C`, existence of inverse permutation-matrix
representatives for all matrix double cosets, and reflection of equality of
those matrix classes into equality in `W_C \ S_n / W_B`.

For injectivity, equality of the matrix classes of two minimal permutations
gives equality of their Weyl classes by reflection. Injectivity of the Weyl
map then gives equality of the original elements of `MinimalRepresentatives`.

For surjectivity, `Quotient.exists_rep` supplies a matrix `g` representing an
arbitrary matrix quotient class. The existence hypothesis supplies a
permutation `w` whose inverse permutation matrix represents that same class.
Surjectivity of the Weyl map supplies a minimal representative `v` with the
same Weyl class as `w`. Applying the published quotient map
`weylToParabolicDoubleCoset R B C` to this equality identifies their matrix
classes. Its value on a representative and its factorization of
`parabolicDoubleCoset` are definitional, so transitivity with the equality
for `g` finishes the proof.

## Closed p-adic theorem

The final theorem introduces the original prime, prime instance, actual
p-adic field, positive rank, and block shapes. It applies the ring-level
assembly to `F.Carrier`, specializing these three published results to the
same parameters:

- `weylMinimalRepresentativeTheorem` from `WeylMinimalRepresentativeProof`;
- `padicBruhatMatrixExistence` from `BruhatMatrixExistenceProof`;
- `padicBruhatWeylReflection` from `BruhatWeylReflectionProof`.

The first supplies the unique minimal Weyl representatives, the second
supplies inverse permutation-matrix representatives, and the third reflects
matrix-coset equality. The quotient descent used in the assembly comes from
`BruhatDescent`. Thus the closed theorem has exactly the original proposition
as its type and no extra premise.

This module is an internal deduction from these published results and actual
quotient definitions. The literature provenance of the target, including
Bernstein–Zelevinsky (1977), sections 2.11 and 6.4 and the convention
`w ↦ w⁻¹`, remains in the unchanged `WeylStatement.md`. The proof above
describes the implemented assembly; it does not reconstruct the source's
general reductive-group argument. This theorem establishes the parabolic
double-coset parametrization, while the intersection and representation
theorems named elsewhere in `WeylStatement` remain separate results.
