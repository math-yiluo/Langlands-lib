# Compatibility of finite unramified invariants

Author: Worker 154.

This module states two compatibility properties of the published
`unramifiedH2Invariant`. Both declarations are propositions in
`Langlands.ClassFieldTheory.Local`; neither is proved here. Every field carrier
has the same arbitrary universe `u`, matching the existing finite inflation
and restriction maps and the target `AbsoluteInvariantExistence.{u}`.

## Inflation

`UnramifiedInvariantInflationCompatibility` quantifies every prime `p` and
every compatible tower `F ⊂ L ⊂ M` of `PadicField.{u} p` carriers. Both `L/F`
and `M/F` are finite Galois extensions. Each is unramified in the canonical
convention: its absolute ramification index equals that of `F`. The scalar
towers over `Padic p` and through `L` specify compatible embeddings.

The statement quantifies cyclic coordinates `χL` and `χM` at the actual
degrees `[L:F]` and `[M:F]`, respectively, and assumes the existing
`IsArithmeticUnramifiedCoordinate` predicate for each. This means the
actual residue action is injective and the inverse image of `+1` acts by
the base residue cardinality power. It then asserts, for every ordinary
relative degree-two cohomology class `x`,

```text
inv(F,M)(relativeInflation F L M 2 x) = inv(F,L)(x).
```

Here each `inv` is the specific `unramifiedH2Invariant` constructed from its
stated coordinate, the cyclic cohomology/norm equivalence, the canonical
valuation on the norm quotient, and the positive denominator map into
`RationalModIntegers`.

## Finite base change

`UnramifiedInvariantBaseChangeCompatibility` quantifies a compatible square
of actual field embeddings with paths `F ⊂ L ⊂ M` and `F ⊂ E ⊂ M`.
The fields are `PadicField.{u} p` carriers. It assumes:

- `E/F` is finite, with compatible scalar structure over `Padic p`;
- `L/F` is finite Galois and its canonical absolute ramification index equals
  that of `F`;
- `M/E` is finite Galois and its canonical absolute ramification index equals
  that of `E`;
- both paths from `F` to `M` are scalar towers, and the specified structures
  on `L/F` and `M/E` are compatible over `Padic p`.

For every arithmetic coordinate `χL` on `Gal(L/F)` at degree `[L:F]`, every
arithmetic coordinate `χM` on `Gal(M/E)` at degree `[M:E]`, and every
`x : relativeCohomology F L 2`, the assertion is

```text
inv(E,M)(relativeRestriction F E M 2
           (relativeInflation F L M 2 x))
  = [E:F] • inv(F,L)(x).
```

The left side uses two existing, actual cohomology maps. Inflation pulls back
along `Gal(M/F) → Gal(L/F)` and includes `Lˣ` into `Mˣ`. Restriction then
pulls back along `Gal(M/E) → Gal(M/F)`, with identity coefficients on `Mˣ`.
Their composite therefore pulls back along
`σ ↦ (σ.restrictScalars F).restrictNormal L` and includes the units of `L`.
Normality of `L/F` makes this group map available. The definition of this
composite does not need `M/F` to be Galois.

The statement imposes no Galois or unramified condition on `E/F`, and no
Galois condition on `M/F`. It does not require `M` to be the compositum
`LE`: any finite unramified Galois extension over `E` containing the specified
copy of `L` is covered. It asserts a law for supplied compatible squares;
it does not construct such an `M`. Existence of suitable squares and their
comparison with absolute closure restriction remain separate obligations.

## Scope and provenance

All degrees of the unramified extensions are positive because they are
finite field extensions; the local `NeZero` instances are derived from
`Module.finrank_pos`. Degree one is included throughout. There is no
coordinate-existence assumption in the form of a global theorem: the two
laws quantify coordinates and test the actual arithmetic predicate on them.
Their existence is the separate published statement
`ArithmeticUnramifiedCoordinateExistence`.

These are laws of the explicit finite invariant, with no supplied
`InvariantFamily`, absolute invariant, class formation or reciprocity
hypothesis. The inflation assertion is the fixed-base case of the base-change
law, after identifying self-restriction with the identity and `[F:F]` with
one. It is exposed separately because finite-stage descent needs exactly
this simpler law before the general restriction proof.

The mathematical provenance is derived from Jean-Pierre Serre,
*Local Fields*, English translation by Marvin Jay Greenberg, Springer,
1979, Chapter XIII, Section 3, Proposition 6 and the subsequent explicit
description of the invariant, and Proposition 7 with its proof, printed
pp.193–194/PDF pp.198–199. The explicit description evaluates the
valuation-induced character at arithmetic Frobenius. Proposition 7 proves
that finite base restriction multiplies the invariant by the field degree:
the unramified case uses the corresponding power of Frobenius, the totally
ramified case uses valuation scaling, and the general case combines them.
The finite-stage form above adds inflation into a common splitting field,
which represents the same class before restriction. Inflation compatibility
expresses independence of the finite unramified splitting field.

The cited pages describe the invariant in the Brauer/continuous cohomology
setting. This module specializes the formulas to the actual ordinary
cohomology and norm-quotient constructions already in the Library; it does
not assert that their comparison with that source model has been proved.
A proof of these targets must establish the finite cocycle, Frobenius and
valuation comparisons for the named maps. Invoking the unproved absolute
invariant target would be circular in the intended application.

Worker 154 read the cited original pages. Registered source:
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
No source-specific errata file was found in the project notes.

The reused definitions are documented in
[`UnramifiedInvariant`](UnramifiedInvariant.md),
[`Invariants`](Invariants.md), and [`Cohomology`](Cohomology.md).
Their sources and proofs are imported unchanged.
