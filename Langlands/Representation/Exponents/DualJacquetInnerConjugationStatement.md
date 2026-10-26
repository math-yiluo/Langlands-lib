# Inner conjugation and actual opposite-dual Jacquet exponents

Author: Worker 556.
Statement formulation and transport route contributed by Worker 436.

`Langlands.GLDualJacquetInnerConjugationStatement.{uF,uV}` states that, for
every prime `p`, supplied `F : PadicField.{uF} p`, supplied topological data
`T`, rank `n`, concrete conjugate block pair `P`, complex representation
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`, and character
`χ : (Fin P.shape.length → F.Carrierˣ) →* ℂˣ`,

```text
T.IsUnitaryDualJacquetExponent P.shape (P.pullbackRep A) χ
  ↔ T.IsUnitaryDualJacquetExponent P.shape A χ.
```

The companion closed proposition
`GLDualJacquetInnerConjugationNonunitaryStatement.{uF,uV}` states the same
equivalence for `IsDualJacquetExponent`. Each declaration returns `Prop`
and quantifies over all its mathematical data. This module states both
equivalences; it proves neither.

The character is literally the same homomorphism on the same ordered block
shape on both sides. There is no inversion, complex conjugation, block
permutation, or character extension. Rank zero is included, and the field
universe `uF` and representation-carrier universe `uV` are independent.
Neither assertion requires irreducibility, admissibility, smoothness of
`A`, analytic temperedness, criticality, classification, finite spectrum,
or finite nilpotence order.

The predicates are the actual definitions in
[DualJacquet](DualJacquet.md). They use the full algebraic transpose dual of
the normalized opposite Jacquet quotient, restricted to the split center.
`IsDualJacquetExponent` requires an open character kernel in the topology
supplied by `T` and a nonzero actual exponent-one eigenspace.
`IsUnitaryDualJacquetExponent` additionally requires `‖χ(a)‖ = 1` for every
split-center element. The action on the full dual is
`(a · φ)(v) = φ(ρ_J(a)v)`. It is not replaced by the ordinary smooth
contragredient.

The provenance is internal algebraic transport from
[WeakCritical](WeakCritical.md), [ParabolicPair](ParabolicPair.md), and
[DualJacquet](DualJacquet.md). Write `g = P.conjugator` and `Aᵍ = P.pullbackRep A`.
The defining action is `Aᵍ.ρ(x) = A.ρ(g*x*g⁻¹)`. Thus the candidate for the
source intertwiner is `E = A.ρ(g) : A → Aᵍ`, with inverse `A.ρ(g⁻¹)`.
The intertwining identity is

```text
Aᵍ.ρ(x) (E v) = E (A.ρ(x) v).
```

The intended separate proof can descend this actual invertible intertwiner
to the opposite coinvariant quotients for the fixed shape, then transpose
the descended equivalence on their full algebraic duals. Equivalently, it
can transport the published opposite-invariant source-functional
eigen-equation. The normalization scalar
`T.leviHalfModulus P.shape (P.shape.blockScalarLevi F.Carrier a)` is the
same on both sides. An actual linear equivalence intertwining the
transpose actions then preserves the same-character eigenspaces and
their nonzeroness. The open-kernel and norm-one conditions depend only
on the unchanged `χ` and `T`. These are proof obligations for the
successor, not assumed structure fields or proved lemmas in this module.

The motivating original is A. J. Silberger, *Introduction to harmonic
analysis on reductive p-adic groups* (1979), registered source
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Section 0.3, printed pp.5–6 (PDF pp.11–12), defines parabolic pairs and
discusses conjugacy to standard pairs. The paragraph before Corollary
4.5.11, printed p.189 (PDF p.195), uses pairs with nonempty weak spectrum
in the minimal-pair argument. Those passages motivate the transport
needed by the standard-pair existence proof. The present assertions
are an internal consequence to be proved from the Library definitions,
not a transcription of a separately numbered source theorem.

This elementary inner action does not supply a comparison with class
exponents, an analytic temperedness criterion, a finite-spectrum theorem,
or existence of minimal pairs. Those substantive assertions and their
proofs remain separate. No existing target or import is edited.
