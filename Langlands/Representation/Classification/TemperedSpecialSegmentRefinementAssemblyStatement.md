# Conditional assembly of tempered special-segment refinement

Author: Worker 627.

`Langlands.Classification.TemperedSpecialSegmentRefinementAssembly.{uF,uV} F T`
is a proposition-valued definition. With exactly the outer parameters
`{p : Nat} [Fact p.Prime]`, `F : PadicField.{uF} p`, and
`T : F.TopologicalData`, it is the implication

```text
TemperedBlockExhaustion.{uF,uV} F T →
SegmentEssentialSquareIntegrableClassification.{uF,uV} F T →
LinkedSegmentHeadExponentComparison.{uF,uV} F T →
Parabolic.OrderedProductRegrouping.{uF,max uF uV} F T →
TemperedSpecialSegmentRefinement.{uF,uV} F T.
```

The field and carrier universe parameters remain independent. The regrouping
input is specialized to carriers in `Type (max uF uV)`, exactly the carrier
universe of the parent tempered data and the resulting segment heads. Every
hypothesis and the conclusion are existing Library proposition definitions;
this module supplies no proof of them or of this implication.

This is an internal derived interface for decomposing a proof. Its intended
argument exhausts each untwisted tempered parent by square-integrable unitary
blocks, passes the parent's real determinant twist through their actual
normalized product induction, and classifies each resulting factor by a strong
segment head. An exponent witness constructed from each untwisted invariant
positive form has exactly the parent's prescribed exponent after twisting.
Ordered flattening keeps a parent's factors consecutive. Precedence would
force strictly increasing head exponents, contradicting equal exponents within
a parent or the decreasing parent exponents between parents. The regrouping
input constructs the isomorphism of actual smooth induced representations,
with the exact degree sums and dependent rank transports.

The conclusion is the unchanged positive-rank refinement statement, including
strong individual heads and an isomorphism to the given tempered datum's
standard module. All products retain the published normalized upper block
parabolic convention, positive half-modulus covariance, and right translation.
No arbitrary irreducible input or full-product quotient condition is added.
The four hypotheses remain genuine obligations; the implication does not
establish unconditional refinement or any analytic exhaustion theorem.

The provenance is internal composition of the five named Library interfaces.
No original-literature theorem is asserted for this conditional interface, and
no downstream quotient coverage or multisegment, square-integrable, or regular
exhaustion result is included as an input. The intended proof must likewise
check independence of any reused lower-level results. This auxiliary interface
does not alter the target or its imports.
