# Outer reversal on exact K0 and the surviving Jacquet term

This is an internal derived construction for actual reversed-Levi Jacquet
compatibility. It uses the actual representation equivalence in
`Geometric.OuterReversalInduction`, exact finite-length K0 pullback,
`Geometric.JacquetPieceGrothendieck`, and the published actual
`Parabolic.normalizedFlattenedJacquetK0_eq`. No new literature assertion or
classification premise is introduced.

Fix an actual ordered positive block shape `B` and refinement `S`, and write
`S' = outerReverseRefinement B S`, `D = B.flatten S`, and
`K = B.reverse.flatten S'`. Let `e` be coarse outer reversal from `B.Levi` to
`B.reverse.Levi`, and `f` its restriction from the original refined subgroup
to the reversed refined subgroup. The definition `outerReverseRefinedLeviK0`
is the exact K0 pullback equivalence along `f`, directed from reversed to
original refined coordinates. Its carrier universe is `Type (max uF uV)`;
field and carrier universes remain independent.

`normalizedRefinedInductionK0_outerReverse` proves

```text
I_(B,S) ∘ f* = e* ∘ I_(B.reverse,S').
```

Here every induction map is the existing positively normalized upper refined
induction map on the full exact finite-length smooth Grothendieck group. The
proof uses `hom_ext_object`, reducing the equality to actual finite-length
smooth representations. Pullback and the published refined finite-length
exactness theorem supply the needed output length proofs. The generator
formulas then identify both sides with their literal induced objects. The
actual smooth induced-function equivalence from
`normalizedRefinedInduced_outerReverseEquiv`, in the inverse direction,
identifies their classes. Thus this proof works on all virtual classes and
retains the quotient by every short exact relation, including nonsplit ones.
It does not replace K0 with a free irreducible or coefficient module.

`normalizedRefinedInductionK0_outerReverse_transport` writes `e*` as the
specified `leviTransportK0` for `B.reversePermutation`, for any proof of the
concrete coarse conjugacy. The inverse-conjugation formula established at the
representation level proves this equality; the transport direction is from
`B.reverse` to `B`.

For the flattened middle coordinates, let `a : D.Levi ≃ₜ* refinedLevi B S`
and `a' : K.Levi ≃ₜ* refinedLevi B.reverse S'` be the actual flattened
coordinate equivalences. Actual inverse conjugation from `D.Levi` to
`K.Levi` is the constructed flattened outer reversal `k`. The theorem
`leviConjugationContinuous_outerReverseFlattened_symm` packages this formula
continuously. The explicit coordinate composite satisfies

```text
a'.comp k.comp a.symm = f.
```

`outerReverseFlattenedLeviEquivContinuous_unflatten` proves this using the
inverse identities of the actual flattened equivalences. Contravariant
functoriality of exact K0 pullback gives
`flattenedLeviK0_outerReverse_transport`: unflattening to the original refined
Levi, after actual flattened transport and reversed flattening, equals `f*`.
The witness is any proof that the reversed flattened source is conjugated onto
the original flattened target by `B.reversePermutation`.

Finally `jacquetGeometricTerm_outerReverse` identifies the actual surviving
geometric term:

```text
jacquetGeometricTerm F T K B S B.reversePermutation h
  = transport_(B.reverse -> B) ∘ I_(B.reverse,S')
      ∘ J_(B.reverse,S') ∘ J_(B.reverse).
```

The transport uses any supplied proof `hB` of the concrete coarse conjugacy,
so in particular it uses the exact witness of `JacquetCompatibilityStatement`.
The proof first applies the published flattened-Jacquet identity at
`B.reverse,S'`: restriction directly to `K` is refined restriction after coarse
restriction, followed by actual reversed flattening. This identity contains
the actual restriction-transitivity and flattened-coordinate comparisons.
The just-proved middle-coordinate equality then turns the middle maps into
`f*`; the actual induction comparison moves it past induction and produces the
required coarse inverse-conjugation transport.

Every theorem holds for arbitrary rank, including zero, arbitrary supplied
p-adic field and topology, and independent field/carrier universes. No positive
rank, admissibility, irreducibility, cuspidality, finite vector-space dimension,
central character, or theorem-valued preservation assumption is added. This
module proves the witnessed survivor comparison; the signed finite regrouping
and final compatibility theorem belong to the separate Aubert assembly.
