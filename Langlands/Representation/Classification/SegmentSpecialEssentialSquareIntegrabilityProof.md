# Essential square-integrability of every segment special quotient

Author: Worker 389. The actual twist transport, scalar-character restriction,
centering arithmetic and assembly in this module are derived internal work.
The imported published proofs retain their own authorship.

## Exact declaration and scope

`Langlands.Classification.segmentSpecialEssentialSquareIntegrability` proves
exactly `SegmentSpecialEssentialSquareIntegrability.{uF,uV} F T` from the
unchanged `SegmentSquareIntegrabilityStatement` module. Its outer parameters
are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The universes `uF` and `uV` remain independent; segment representatives and
quotient carriers lie in `Type (max uF uV)`.

For every actual segment `Δ` and smooth complex representation `π` of
`GL_(Δ.degree)(F)`, the only constituent hypothesis is the existing weak
`T.IsSegmentQuotient Δ π`. The conclusion is the existing analytic predicate
`T.IsEssentiallySquareIntegrable π.representation`. The theorem has no
additional mathematical hypotheses. The cuspidal base may have any smooth
scalar character. Positive-form existence and the converse classification
are separate results.

## Actual twisting, admissibility and scalar data

`segmentQuotient_realPowerTwist` applies the published
`twistedProductCharacterTwist` to the uniform block shape, a constant
supercuspidal representative and the real norm character. The resulting
actual equivalence transports the twisted quotient to the increasing product
for `Δ.twist s`. The generic `isIrreducibleQuotient_twist_iff` preserves both
irreducibility and the surjective intertwiner. Twisting the supplied base
class equality represents the twisted segment by the actual twisted
supercuspidal object. This uses the weak quotient relation throughout.

`segmentQuotient_isAdmissible` takes irreducibility from that relation and
uses the admissibility conclusion of the published
`CuspidalSupport.cuspidalEmbedding`. This is the lower cuspidal embedding
construction.

`exists_smooth_scalarCharacter` restricts the locally constant character
supplied by the published admissible Schur theorem along the continuous
scalar homomorphism into the group center. Its kernel is open, and it acts
by the specified scalar on every vector. Applying the published
`PadicField.TopologicalData.smoothCharacterNormDecomposition` to the base
representative's character `ω` supplies `c : ℝ` with
`‖ω(a)‖ = |a|^c` for every `a : Fˣ`.

`scalarCharacter_realPowerTwist` uses the published scalar-twist formula,
including the rank factor. `scalarNorm_realPowerTwist` computes the twisted
base character's norm as `|a|^(c+r*s)`. Here `r = Δ.rank`, `m = Δ.length`,
and the main proof chooses

```
s = -c/r - (m-1)/2.
```

Both the quotient and its base representative are twisted by their actual
real determinant characters. No unitarity or square-integrability property
of the original base is assumed.

## Jacquet exponents and finite cone arithmetic

The proof applies the published
`segmentSpecialJacquetExponentNormFormula` to the twisted weak quotient.
That theorem covers every ordered standard block shape and every generalized
normalized Jacquet eigencharacter, with the supplied base representative
and its actual scalar character. It supplies positive lengths `k_i` of total
`m` and the full character norm identity. Its block-size divisibility
conclusion is available but is not needed by the centering calculation.

After combining real powers, `centeredSegmentExponent` computes the real
part as

```
x_i = r*k_i*((m-k_i)/2-K_i),    K_i = sum_{j<i} k_j.
```

`centeredNormFormula_positiveRootCone` proves that this vector is an actual
`T.IsRealPartOf` the supplied generalized character: natural prefix sums are
cast to real partial sums and the product norm is rewritten term by term.

For arbitrary positive real interval lengths `w_i` of total `M`, the internal
`initialSum_centered` proves by induction that the corresponding vector has
prefix sums

```
sum_{i<j} r*w_i*((M-w_i)/2-P_i) = r*P_j*(M-P_j)/2,
P_j = sum_{i<j} w_i.
```

The full sum is zero. Every proper nonempty prefix has `P_j > 0` and
`M-P_j > 0`. Since `r > 0`, its sum is strictly positive. The helper
`centeredInterval_positiveRootCone` therefore proves membership in the
published `Exponents.IsPositiveRootCone`. This finite arithmetic is derived
for this implementation. It retains the cuspidal rank factor.

## Analytic conclusion

`squareIntegrable_of_jacquetPositiveRootCone` applies the published
`Langlands.glSquareIntegrableExponentCriterion` at field universe `uF` and
carrier universe `max uF uV`. The twisted quotient is irreducible, admissible
and smooth in positive rank. Schur supplies its scalar character. The closed
cone inequality gives the weak Jacquet bounds, so the published elementary
`glTemperedExponentEdge` gives norm one for this scalar character. The strict
cone inequality gives every strict bound required by the analytic criterion.
Its reverse implication yields the actual `T.IsSquareIntegrable`, including
admissibility, a unitary scalar character with open kernel, and the required
L² membership of all descended absolute matrix coefficients for every Borel
Haar measure on the central quotient.

Finally the main proof chooses `-s` in the definition of
`IsEssentiallySquareIntegrable`, whose square-integrable twist has exponent
`-(-s) = s`. This is precisely the actual twisted quotient already proved
square-integrable.

## Original sources and proof boundaries

The construction direction is Zelevinsky 1980, *Induced representations of
reductive p-adic groups II*, §9.3, printed p.198 (PDF p.35), using §9.1,
printed p.197 (PDF p.34). The retained registered source is
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Henniart 2002, *Une caractérisation de la correspondance de Langlands locale
pour GL(n)*, §2.6, printed p.595 (PDF p.9), also states the forward result for
the special quotient of the increasing product. Its registered source is
`henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
These passages were read in this branch. The current source-boundary note
`notes/henniart/gln-classification-sources.md` was also read.

The implementation assembles proved Library inputs and explicit algebra;
it does not treat a citation as a mathematical hypothesis. The scalar norm
decomposition is an internal theorem. The imported Jacquet norm proof derives
its all-shape generalized-character formula from actual descending Jacquet
factors, central characters, scalar detection and interval arithmetic. The
analytic criterion has its own published proof and provenance explanation.
The conventions throughout are upper block parabolics, positive half-modulus
normalized induction with right translation, and inverse half-modulus
normalized Jacquet action. Zelevinsky's omitted converse and §9.17 conjecture
are not proof inputs.

## Dependency independence

The dependency audit uses supplied Library commit
`61cebbe0711a0368e49597c07d79b5188d0b829e`. The norm proof's 1137-module project
import closure has nonempty paired Markdown and agrees with the workspace;
its inherited pairs also agree with the independently reviewed frozen base
`159d1197aca62e7ba065e111be014f24f26d0387`. Its primary pair agrees across the
frozen accepted archive, exact publication and supplied Library. The scalar
norm proof and strict analytic criterion were separately checked against their
independently accepted published pairs and complete declarations.

No proof uses parent ordered conversion, square-integrable exhaustion,
regular exhaustion, square-integrable Langlands classification, tempered
block uniqueness, multisegment exhaustion, ordered-head existence, quotient
coverage, or the stronger strong-head analytic classification. In the norm
closure the only matching regular-exhaustion name is an unassumed proposition
definition and its conjunction in `RegularLanglandsStatement`.
`RegularLanglandsHeadReduction` was read: it supplies generic conditional
finite-length/product-obstruction helpers and actual nonzero induction; it
does not prove or assume exhaustion. Importing those proposition definitions
does not supply the excluded mathematical conclusion.

The upstream nonadjacent-product proof uses the fully proved general BZ77
derivative theory permitted by the trusted operator's source-boundary decision
on request `a8463ee15d57588c8de10306748b2538`. All 158 derivative, mirabolic,
Whittaker and Gelfand–Kazhdan modules in the norm closure belong to that general
656-module upstream closure. It contains no later segment Jacquet or segment
derivative result, highest-derivative support shift, segment-socle derivative
assertion, or excluded classification proof. The independently accepted norm
proof's review confirms the published general derivative inputs and this
boundary. The full operator decision and original request were read; the
cuspidal derivative proof and its statement were checked separately from the
excluded segment-socle assertion. No derivative theorem is added here.

The new module leaves the target Lean/Markdown pair and all pairs it imports
unchanged. Its helper results and final assembly require independent review;
this author audit and development compilation are not acceptance evidence.
