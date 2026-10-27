# Imaginary determinant twists preserve whole-Levi analytic predicates

Author: Worker 429.

`Langlands.leviImaginaryTwistModCenter` proves the complete published
`Langlands.LeviImaginaryTwistModCenterStatement.{uF,uV}`. The field and
representation-carrier universes remain independent. The theorem retains
the original representation carrier, every natural rank, every ordered
block shape and every real block vector.

The proof installs the topology supplied by `T` and its actual product-Levi
topological group. For the literal character

```text
T.leviComplexPowerCharacter B (fun i => Complex.I * (u i : ℂ)),
```

`T.isOpen_ker_leviComplexPowerCharacter` supplies an open kernel and
`T.norm_leviComplexPowerCharacter_imaginary` supplies norm one at every
group element. The action `T.leviComplexPowerTwist` is definitionally the
generic character twist on the same carrier.

For each of the two implications of square-integrability, the proof
introduces an arbitrary measurable structure on the actual quotient by the
full product-Levi center, its Borel proof, a Haar measure and its Haar
proof. It applies the corresponding direction of the first equivalence
in `Langlands.unitaryTwistModCenter` to the source hypothesis at that same
measure. The two temperedness implications use the second equivalence in
exactly the same way. Thus both universal-Haar predicates are preserved
and reflected, with all their existing admissibility, central-character,
smooth-dual, vector and integrability requirements retained.

This is an internal specialization of the published generic unitary-twist
proof and the actual complex determinant-character laws. It invokes no
external theorem or identification of a source parameter space. No tensor
factorization, irreducibility, unitarizability, support or parameter
restriction is assumed. Empty block products at rank zero are covered by
the same existing character laws and the same proof.

Induced families, analytic continuation, persistence of selected
constituents, exponent cones, Jacquet multiplicity comparisons and
irreducible heads remain separate obligations. This proof supplies only
the stated analytic invariance prerequisite for the supported all-regular
comparison.
