# Single-block transport of supercuspidal real unitarization

Authors: Worker 163 (Lean proof and original exposition), Worker 438
(current dependency audit and preparation).

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

This is an internal transport of accepted lower mathematics. The generic
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
including this proof and its statement. All 326 already-published Lean
and Markdown files in that closure agree byte-for-byte with that base;
the target statement and its imported pairs are unchanged by this
contribution. Compared with the target statement's publication at
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
unproved conclusions is used. The actual Harish-Chandra path described
above supplies every compactness input.

The following audit carries the parent task's exclusions to this proof and
to the complete lower proof closure. Each row records absence from both the
import closure and the mathematical route just described.

| Excluded task or conclusion | Audit |
| --- | --- |
| Individual special-head/reverse-socle existence, `67279e36-f3c2-42e3-9302-11729784042e` | Absent; no segment endpoints are constructed or used. |
| Individual segment-socle/reverse-head existence, `4ca79bbd-589e-476b-9f65-661e799984b5` | Absent; only the original cuspidal representation is transported. |
| Analytic segment classification, `aca8805b-054f-4d56-8045-12db7f623404` | Absent; the form comes from coefficient integration. |
| `SegmentSpecialEssentialSquareIntegrability`, `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | Absent; no special representation or Ze80 §9.3 theorem enters the compactness or integral construction. |
| Multisegment special-head exhaustion, `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | Absent. |
| Ordered strong-head existence, `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Absent. |
| Quotient coverage, `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Absent. |
| Ordered conversion, `8252833d-c269-41a9-824c-5879e531b23b` | Absent. |
| Tempered uniqueness, `52e97845-36bb-457d-b76f-70753334b88c` | Absent. |
| `SquareIntegrableLanglandsClassification`, `1cb45da2-7007-4351-a694-594fb148b8d1` | Absent; the generic coefficient integral contains no Langlands classification. |
| Square-integrable exhaustion, `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | Absent. |
| Regular exhaustion, `bf433f0a-921a-428c-b0c0-6475438125ac` | Absent. |
| Special-head product irreducibility, `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Absent; no induced-product irreducibility is used. |
| `GenericSegmentProductUniqueness`, `30341ae4-65f2-4a0e-9283-763db01a409e` | Absent. |
| `OrderedMultisegmentSocleExistence`, `23189526-80b0-4828-a6d4-7ebec2cbeef5` | Absent. |
| `MultisegmentSocleExhaustion`, `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Absent. |
| `SegmentSocleProductIrreducibility`, `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Absent. |
| Adjacent socle commutation, `e3634665-571b-4852-9f4c-bab8a1053434` | Absent. |
| `SegmentFullJacquetFormula`, `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its proof successor | Absent; the lower closure uses generic parabolic and refinement coinvariants, and the adapter uses the one-block cuspidality comparison. No segment Jacquet formula enters either route. |
| `SegmentHeadJacquetFormula`, `55ad1e10-62d8-46b7-a081-909ef0056426` | Absent. |
| `SegmentSocleJacquetFormula`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | Absent. |
| `SegmentSpecialJacquetExponentNormFormula`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | Absent; real exponents come from smooth characters of field units. |
| Ze80 segment derivative formulas §§3.5 and 9.6, and assumed BZ77 derivative results | Absent; no derivatives are used. |
| Ze80 segment product irreducibility §§4.2 and 9.7 | Absent; there is no product-irreducibility argument here. |
| Ze80 analytic or square-integrability result §9.3; any classification or exhaustion theorem | Absent; only generic Haar integration and cuspidal coefficient compactness are used. |
| Segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` | Absent, together with its cuspidal-derivative part. |

This unit proves the real unitarization input. The common compact model,
analytic family of Hermitian forms, continuation of positivity,
large-parameter unbounded coefficient, swapping the two induced factors,
and adjacent reducibility remain separate obligations of the consumer.
