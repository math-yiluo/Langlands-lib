# Arithmetic weak transfer attached to actual full cuspidal classes

This internal attachment construction puts the arithmetic relations from
`Langlands.Representation.Unramified.WeakTransfer` on the published actual
full cuspidal classes. It introduces no new existence or uniqueness assertion.

The number fields `F : Type uF` and `E : Type uE` have an `Algebra F E`
structure and independent universes. Both explicit assumptions
`CompactSpace (AdeleQuotient F)` and
`CompactSpace (AdeleQuotient E)` are retained, as required by the actual
automorphic-form constructions. The local-factor carrier universes `uV`
downstairs and `uW` upstairs are independent of each other and of both
field universes. The public Prop definitions have universe parameter order
`.{uF, uE, uV, uW}`.

## The two class relations

In namespace `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass`,
`IsWeakBaseChangeOf d c` takes an upstairs class
`d : IsoClass E r` and a downstairs class `c : IsoClass F r`.
Their common positive rank is `r + 1`. It means that there exist supplied
systems `s` downstairs and `t` upstairs such that

```text
HasSpectralSystem.{uF, uV} c s
HasSpectralSystem.{uE, uW} d t
t.IsArithmeticWeakBaseChangeOf s.
```

`IsWeakInductionOf c d` takes a downstairs class
`c : IsoClass F r` and an upstairs class `d : IsoClass E q` with independently
supplied positive ranks `r + 1` and `q + 1`. It existentially quantifies
systems with the same genuine attachments and requires
`s.IsArithmeticWeakInductionOf t`. Thus it explicitly includes
`r + 1 = (q + 1) * Module.finrank F E` through the numerical relation.
`IsWeakInductionOf.rank_eq` extracts this equation from its witness.

`HasSpectralSystem` is the current published relation on full cuspidal
classes, rather than a new label for a polynomial. Its witness supplies an
actual `CuspidalOperatorRealization`, a nonzero finite-adelic-invariant slice
inside its actual form image, bundled smooth local factors, reference vectors
and a genuine tensor equivalence onto that slice. Its unramified data
include irreducibility, admissibility and the normalized spherical Hecke
equations on the entire actual local fixed space away from a finite set.
The system is exactly the one exported by that presentation. The word
finite here refers to the finite adelic action, not finite dimensionality
of the slice.

Consequently the public class relations require genuine attached witnesses.
They do not claim that every class has a spectral presentation, that
independently supplied presentations give the same spectra, or that numerical
spectra alone determine a class.

## Representative transport and finite exceptions

`isWeakBaseChangeOf_isoClass_iff` and `isWeakInductionOf_isoClass_iff` express
the relations at any specified actual representatives `S` over `F` and `T`
over `E`. Each right-hand side existentially quantifies a
`CuspidalSpectralPresentation.{uF, uV} S` and a
`CuspidalSpectralPresentation.{uE, uW} T`, comparing their exported systems.
The forward proofs apply the published `hasSpectralSystem_iff` to each
attachment. That theorem transports its witness along the full equivalence
obtained from equality of cuspidal classes. The reverse proofs use those
specified representatives as the attachment witnesses.

For full equivalences `e : S.Equivalence S'` and
`f : T.Equivalence T'`, `isWeakBaseChangeOf_transport` and
`isWeakInductionOf_transport` prove equivalence of the attached relations.
After expanding the representative characterizations, they use the actual
presentations `P.transport e` and `Q.transport f` in one direction, and
transport along the inverse equivalences in the other. The published
transport preserves the supplied factor family and has definitionally the
same spectral system, so the numerical comparison is unchanged.
The equivalences retain all finite, compact and differential operators;
the argument does not replace full cuspidal equivalence by finite-factor
equivalence.

Enlarging either witnessing exceptional set is compatible with these
attachments through `HasSpectralSystem.restrict` and
`CuspidalSpectralPresentation.restrict_spectralSystem`. The imported four
numerical restriction equivalences show that either comparison is unchanged.
For upstairs restrictions their proof discards the finite image under the
actual contraction map, uniformly for every place above each retained base
place. No uniqueness of unrelated presentations is used in any argument.

## Source correspondence, normalization and scope

The arithmetic formulas come from the derived numerical definitions in
the paired `Representation/Unramified/WeakTransfer.md`. Their original source
is Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), registered as
`arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The source is readable at
`/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`.
Chapter III, printed p.199, Definition 1.1 and (1.1), gives weak base change;
printed pp.214–216, Definition 6.1 and (6.1)–(6.2), motivates the induction
Euler-polynomial identity. The latter uses a product over all actual places
and composition with `X^f`, retaining multiplicities without choosing roots.
The source's cyclic-extension formulas motivate definitions here for arbitrary
number-field extensions; no corresponding general existence theorem is
asserted.

The attachment itself is an internal composition of those formulas with the
published actual-class and presentation APIs, rather than an assertion that
the source constructs this Lean presentation interface. Its normalization is
exactly the existing `HasSphericalHeckeSpectrum` convention of the genuine
presentation: integral-subgroup Haar mass one and the positive-square-root
residue-cardinality factor in `Unramified.standardHeckeScalar`. No additional
normalization is imposed by either class relation.

The definitions compare cuspidal inputs and cuspidal outputs. Arthur–Clozel's
broader induced-from-cuspidal output category can contain noncuspidal objects
and remains a separate construction obligation. This module constructs no
global normalized induced representation, unitary induced category,
determinant twist, Galois action, or realized isobaric class. A finite sum
of numerical systems supplies none of those objects.

Automorphic existence, cuspidal preservation, uniqueness, descent, strong
local compatibility, tower theorems, local Weil-induction comparison and
Langlands correspondence remain unproved here. A specialization to the
existing rank-one Hecke-character weak-induction relation also requires an
actual spectral realization and a proved comparison. The imported
`CuspidalSpectralPresentation` and
`CuspidalOperatorRealization.IsoClass.HasSpectralSystem` are used by their
current Lean names; their independent construction and existence obligations
are preserved.
