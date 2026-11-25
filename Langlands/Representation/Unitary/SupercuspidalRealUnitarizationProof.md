# Single-block transport of supercuspidal real unitarization

`Langlands.supercuspidalRealUnitarization` has exactly the type
`Langlands.SupercuspidalRealUnitarizationStatement.{uF,uV}`. It specializes the proved `leviCuspidalRealUnitarization` to
`LeviAdmissibility.oneBlock n hn`. The actual embedding of this single-block
Levi is surjective. Its action on matrices is evaluation at the only block:
the single-block consecutive indices are the ambient indices. In particular
the Levi real character is the ordinary normalized determinant real
character with exponent `t 0`.

An order equivalence of invariant subspaces proves irreducibility of the
pullback action. The published `singleBlockCuspidalityClause` proves its
Levi cuspidality from the GL supercuspidality hypothesis. The existing Levi
unitarization theorem then supplies an exponent vector and an actual
positive form on `V`. The twist identity identifies this with the pullback
of the GL twist. Surjectivity makes the same form invariant under every
GL element. No topology or norm on `V` is introduced, and the independent
universes and the sign `+t` are preserved.

This is an internal transport of published lower mathematics. The generic
surjective-pullback irreducibility argument is implemented locally to keep
its imports below the classification consumers. The existing Library also
contains such arguments in `CuspidalTensorAssociationProof` and
`InducedJacquetCount`; those larger modules are not imported.

The original-literature mechanism is Casselman, *Introduction to the
theory of admissible representations of p-adic reductive groups*, draft
of 1 May 1995 (registered
`casselman-1995-admissible-representations`): Lemma 5.2.5 (p.48) removes
the real norm of a central character, and Corollary 5.2.3 (p.47) gives
unitarity for an irreducible absolutely cuspidal representation with
unitary central character. The coefficient compactness and integral
construction underlying that corollary are Theorem 5.2.1 (pp.46–47) and
Proposition 2.5.4 (pp.28–29). Section 2.1 (p.18) defines unitarity using
an invariant definite Hermitian form on the representation space. The
blockwise exponent choice, finite-index passage, right Haar measure and
single-block transport below are internal derivations of this mechanism;
the single-block adapter itself is not a claim quoted from Casselman.

`Langlands.supercuspidalRepRealUnitarization` is the supporting object-level
corollary. For an actual `SupercuspidalRep A`, it applies the main theorem
to `A.obj.representation`, `A.property.1` and `A.property.2`. It returns a
real exponent and the actual object `B = SupercuspidalRep.twist ... A`
with `IsUnitarizable B.obj.representation`. The identity
`B.isoClass = T.supercuspidalClassRealPowerTwist n t A.isoClass` is
reflexive after unfolding the existing definitions. In particular,
`determinantPowerCharacter n t` is `realPowerCharacter (determinantNorm n) t`.
The object and class corollary introduces no new representation-theoretic
hypothesis.

## Lower proof and mathematical dependencies

The reused `leviCuspidalRealUnitarization` is an actual proof from only
irreducibility and Levi cuspidality. Its implementation first obtains the
Schur central character from admissibility and irreducibility. The smooth
character norm decomposition on each block scalar gives an exponent `c_i`;
the twist exponent is `-c_i / D.size i`, making the central character
unitary. The twist is trivial on the determinant-unit subgroup.

The Harish-Chandra forward theorem obtains compact support of coefficients
on that subgroup using compact averaging, contraction, a finite compact
orbit and actual Cartan decomposition. In `HarishChandraAssembly`, the
intermediate Cartan premise is supplied by the proved
`GeneralLinear.Cartan.cartanDecomposition`. No Cartan or compactness premise
is added to the GL theorem. The determinant-unit subgroup together with the
center has finite index. A finite union of translated coefficient supports
therefore gives compact support of coefficient norms on the central
quotient. The central quotient is Hausdorff and locally compact. A right
Haar measure makes the compactly supported continuous coefficients `L²`,
and `UnitaryCentralCharacter.coefficientProductForm` integrates their
products to produce a positive invariant form. Positivity uses a nonzero
smooth dual functional and irreducibility. This proof constructs the form
on the original algebraic carrier; there is no carrier-topology premise.

The module `Unitary.SquareIntegrableProof` supplies this generic integral
construction. It proves no classification or exhaustion theorem and uses
no segment square-integrability theorem. In particular the invocation of
`coefficientProductForm` does not use Ze80 §9.3. Its `L²` hypotheses in the
Levi proof follow directly from the proved coefficient compactness.

The new single-block adapter uses only a local invariant-subspace order
equivalence, the proved cuspidality comparison, the single-block matrix
identities and surjectivity, and the existing Levi theorem. The class
corollary uses the elementary determinant-character twist closure from
`Classification.SupercuspidalTwist`.

## Import and independence audit

The recursive project import closure at Library base
`d54bbb9c881aa001e78c70a31a3a7bcb88affb43` contains 164 modules,
including this proof and its statement. All 326 published Lean
and Markdown files in that closure agree byte-for-byte with that base;
the target statement and its imported pairs are unchanged. Compared with the target statement's publication at
`6789e5106aba61566887427750f5444a494d5879`, the only closure change is
the extraction of `span_range_orbit_eq_top` from
`Smooth.SmallRealizationProof` into the new elementary `OrbitSpan`
module. Its proof takes the span of the orbit of a nonzero vector as an
invariant subspace and uses irreducibility to identify it with the whole
space; the extraction adds no classification premise.

The only modules under
`Representation.Classification` are `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement` and
`SupercuspidalTwist`. These provide the predicate, conjugation and smooth
object infrastructure, and determinant-character twist closure. No segment,
multisegment, derivative, mirabolic, tempered or exhaustion module occurs.
The closure contains the generic proposition definitions
`GeometricLemmaStatement` and `JacquetInductionStatement`; none of their
conclusions is used. The actual Harish-Chandra path described
above supplies every compactness input.

The following audit records the excluded results for this proof and for
the complete lower proof closure. Each row records absence from both the
import closure and the mathematical route just described.

| Excluded result | Audit |
| --- | --- |
| Individual special-head/reverse-socle existence | Absent; no segment endpoints are constructed or used. |
| Individual segment-socle/reverse-head existence | Absent; only the original cuspidal representation is transported. |
| Analytic segment classification | Absent; the form comes from coefficient integration. |
| `SegmentSpecialEssentialSquareIntegrability` | Absent; no special representation or Ze80 §9.3 theorem enters the compactness or integral construction. |
| Multisegment special-head exhaustion | Absent. |
| Ordered strong-head existence | Absent. |
| Quotient coverage | Absent. |
| Ordered conversion | Absent. |
| Tempered uniqueness | Absent. |
| `SquareIntegrableLanglandsClassification` | Absent; the generic coefficient integral contains no Langlands classification. |
| Square-integrable exhaustion | Absent. |
| Regular exhaustion | Absent. |
| Special-head product irreducibility | Absent; no induced-product irreducibility is used. |
| `GenericSegmentProductUniqueness` | Absent. |
| `OrderedMultisegmentSocleExistence` | Absent. |
| `MultisegmentSocleExhaustion` | Absent. |
| `SegmentSocleProductIrreducibility` | Absent. |
| Adjacent socle commutation | Absent. |
| `SegmentFullJacquetFormula` and its proof | Absent; the lower closure uses generic parabolic and refinement coinvariants, and the adapter uses the one-block cuspidality comparison. No segment Jacquet formula enters either route. |
| `SegmentHeadJacquetFormula` | Absent. |
| `SegmentSocleJacquetFormula` | Absent. |
| `SegmentSpecialJacquetExponentNormFormula` | Absent; real exponents come from smooth characters of field units. |
| Ze80 segment derivative formulas §§3.5 and 9.6, and assumed BZ77 derivative results | Absent; no derivatives are used. |
| Ze80 segment product irreducibility §§4.2 and 9.7 | Absent; there is no product-irreducibility argument here. |
| Ze80 analytic or square-integrability result §9.3; any classification or exhaustion theorem | Absent; only generic Haar integration and cuspidal coefficient compactness are used. |
| Segment-socle and cuspidal-derivative results | Absent. |

This module proves the real unitarization input. The common compact model,
analytic family of Hermitian forms, continuation of positivity,
large-parameter unbounded coefficient, swapping the two induced factors,
and adjacent reducibility are separate inputs of the consumer, not part of
this proof.
