# Scalar descent for the actual strict binary Laurent diagram

Author: Worker 572.

The module proves the existing proposition, at every universe `u`:

```lean
theorem Langlands.Analytic.StrictTestDomain.binaryLaurentGluing :
    Langlands.Analytic.StrictTestDomain.BinaryLaurentGluingStatement.{u}
```

Its unapplied type has no additional parameters or hypotheses. The statement
and its imported Lean/Markdown closure are unchanged. For every complete
ultrametric normed field `K`, presented strict affinoid algebra `P`, and
`f : P`, compatible scalar sections of the actual upper and lower Laurent
quotients come from exactly one element of `P` under their actual base maps.
Compatibility uses the actual `interLeft` and `interRight` restrictions into
the existing four-variable intersection quotient.

## The two scalar cases

The proof splits on `∀ c : K, ‖c‖ ≤ 1`, keeping the given normed-field
structure throughout.

In this case it applies the published
`binaryLaurentGluing_of_trivialScalar` from `BinaryLaurentTrivialScalar`.
That theorem uses the proved `trivialScalarRationalLocalization` for the
actual quotients: the upper quotient localizes at `1`, and both the lower
quotient and the intersection localize at `f`. The upper base map and the
actual lower-to-intersection restriction are therefore bijective. The
upper section determines the base element, compatibility gives its lower
equation, and injectivity gives uniqueness. The present module reuses that
proof without adding any localization hypothesis.

Otherwise, classical negation of the universal inequality gives
`hnontrivial : ∃ c : K, 1 < ‖c‖`. Put

```lean
A := PresentedAffinoidAlgebra.ofStrict K P
e := PresentedAffinoidAlgebra.strictEquiv K P
fRel := e.symm f
```

Here `e : BoundedAlgEquiv K A P` is the published radius-one comparison of
the actual quotient presentations. Apply the published
`binaryLaurentDiagramComparison` from `BinaryLaurentDiagramComparisonProof`.
It supplies bounded equivalences `eUpper`, `eLower`, and `eOverlap` from the
actual strict upper, lower, and four-variable intersection quotients to
the actual relative upper, lower, and two-variable overlap quotients over
`A` at `fRel`. The coefficient squares and both restriction squares are
proved parts of this comparison.

Applying `eOverlap` to the given compatibility and using the two restriction
squares proves

```lean
PresentedAffinoidAlgebra.BinaryLaurent.left K A fRel (eUpper sUpper) =
  PresentedAffinoidAlgebra.BinaryLaurent.right K A fRel (eLower sLower)
```

The published
`PresentedAffinoidAlgebra.BinaryLaurent.gluing` from
`GeneralizedAffinoid.BinaryLaurentGluingProof`, applied to `K`,
`hnontrivial`, `P`, `fRel`, and these two relative sections, gives a
unique `a : A` with the required relative upper and lower images.
All analytic input is supplied by this proved theorem. In particular,
closedness, relative-series comparisons and relative gluing are not
assumptions of the new theorem.

The desired strict element is `e a`. For each of its two restriction
equations, injectivity of the corresponding comparison equivalence
reduces the assertion to the relative equation. The coefficient square
and `e.symm (e a) = a` give that equation. If `b : P` has the two prescribed
strict images, the same coefficient squares show that `e.symm b` has the
two prescribed relative images. Relative uniqueness gives
`e.symm b = a`, and injectivity of `e.symm` gives `b = e a`.

## Scope and provenance

This is an internal assembly of the published trivial-scalar helper,
actual diagram comparison, and relative scalar gluing proof. It introduces
no new quotient, norm, structural map or restriction. The relative proof
uses the proved unit-annulus coefficient normal form, actual overlap
kernel presentation, and closedness with the principal-relation
equivalence. The present proof needs their resulting scalar unique
amalgamation theorem.

The analytic provenance is Piotr Achinger, *Introduction to
non-Archimedean Geometry*, November 22, 2020, Proposition 7.1.1,
printed/PDF p.64, with the nontrivial valuation convention on p.6
and context on pp.63–65. The retained source is registered as
`achinger-2020-non-archimedean-geometry-nov22`, at
`/home/taskhub/pilot/literature/Piotr Achinger, Introduction to non-Archimedean Geometry (November 22, 2020).pdf`,
SHA256 `666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
The published statement and relative proof explain the omitted words
"is exact" and the `g₋₁` typo in the printed proof. The formal input here
is the published Lean proof, rather than the citation itself.

Vladimir G. Berkovich, *Non-archimedean analytic spaces*, Trieste lectures,
2009, Exercise 2.2.2(i), p.9, and Fact 2.2.6(i), p.10, provide the broader
context including trivially valued fields. The registered source is
`berkovich-2009-trieste-analytic-spaces`, retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The trivial-scalar branch is proved by the algebraic localization route
described above.

Neither branch assumes a nonzero or reduced base, a proper defining ideal,
a nonnilpotent `f`, or nonempty lower or overlap loci. The proof therefore
retains zero and nonreduced bases, zero and nilpotent `f`, empty lower and
overlap loci, and trivially valued scalar fields.

The result is scalar degree-zero descent for this binary cover at unit
radii. It claims no surjectivity onto the overlap, higher Čech exactness,
admissibility, arbitrary-radius descent, finite-module descent, or descent
for general covers. The standard-cover and whole-spectrum targets remain
separate.
