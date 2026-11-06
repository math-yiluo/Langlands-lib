# Generic segment product exhaustion

Author: Worker 1732.

The theorem `Langlands.Classification.genericSegmentProductExhaustion` proves
the published proposition
`Langlands.Classification.GenericSegmentProductExhaustion.{uF,uV} F T`
from `Classification.SegmentGenericStatement`. For every positive rank
`n + 1`, every allowed continuous nontrivial unitary additive character, and
every actual smooth complex representation, genericity is equivalent to an
actual isomorphism with the entire induced product of supplied special segment
heads whose multisegment is unlinked. Repeated segments retain their
multiplicities. Field and representation universes remain independent; the
classified representation and the cuspidal bases have carrier universe
`max uF uV`, as in the published target.

The special head is the irreducible quotient of the increasing segment
product. The induction, topology, actions, upper-unipotent subgroup and
standard character are the existing Library constructions. The theorem
supplies an isomorphism in `SmoothRep`, not merely equality of constituent
classes or cuspidal supports.

## Finite cuspidal content

The auxiliary theorem
`PadicField.TopologicalData.Multisegment.exists_unlinked_of_cuspidalContent`
is an internal derivation from the published integral-twist-freeness,
linkage-orientation and union/intersection replacement results. Its explicit
twist-freeness premise is discharged by
`Classification.cuspidalIntegralTwistFreeness` in the exhaustion proof.

For a multisegment, define its weight to be the sum of the squares of all
segment lengths. Induction bounds this weight by the square of the cardinality
of its cuspidal content. Singleton segments realize every finite cuspidal
multiset. Among all realizations of a prescribed content, `Nat.find` chooses
one minimizing the difference between that fixed bound and its weight.

Suppose this multisegment contains a linked pair. The segments are distinct,
so one occurrence of each can be removed. Orient the linkage and replace the
pair with its union and optional intersection. The published replacement
identity preserves every cuspidal multiplicity, including the intersection.
The union is longer than either original segment; the sum of the replacement
lengths is unchanged. A quadratic inequality therefore shows that the sum of
squares strictly increases. The replacement still satisfies the same bound,
so its difference from that bound strictly decreases, contradicting
minimality. The chosen multisegment is unlinked.

## Functionals and the top derivative

The private lemma `functional_iff_top_nontrivial` proves, in every positive
rank including rank one, that a nonzero standard Whittaker functional exists
exactly when the whole top derivative is nonzero. It uses the published
`Whittaker.functionalsLocalizationDualEquiv` to identify functionals with the
linear dual of the actual character-localization quotient, and
`TopLocalization.topLocalizationIso` to identify that quotient with the top
derivative after its rank transport. A complex vector space has a nonzero dual
exactly when it is nontrivial. The proof also converts existence of a nonzero
functional into nontriviality of the corresponding functional subspace.
The harmless rank transport from `(n + 1) - (n + 1)` to zero is handled by
the private `rankCastLinearEquiv`.

## Exhaustion and its converse

Starting with a generic representation, `glSupercuspidalEmbedding` gives its
actual supercuspidal support. Apply the finite construction to that multiset.
The sum of cuspidal ranks shows that the resulting unlinked multisegment has
degree `n + 1`. Pass to its occurrence list and use
`segmentHeadDatumOfList` to choose actual special heads without changing its
multiset or degree.

`segmentHeadProductIrreducibility` makes the whole resulting induced product
irreducible. `segmentHeadProductCuspidalSupport` identifies its exact support
with the original multiset. Its top derivative is nonzero by
`segmentHeadProductTopDerivativeNontrivial`, and the original representation
has nonzero top derivative by the functional comparison above.
`CuspidalSupport.fixedSupportDetectedEquiv` then gives an actual equivariant
linear equivalence between the two irreducible representations with this
support. `SmoothRep.mkIso` supplies the isomorphism required by the target.

Conversely, an unlinked product of special heads is irreducible by the same
irreducibility theorem. The published cuspidal-embedding theorem supplies its
admissibility, and the nonzero top derivative supplies a Whittaker functional.
These three properties give genericity of the product. Transport genericity
across the supplied isomorphism using
`Whittaker.isGeneric_iff_of_equiv`.

## Provenance and scope

The result corresponds to Zelevinsky, *Induced representations of reductive
p-adic groups II* (1980), Theorem 9.7(b), printed p.199, and section 9.10,
p.201; the converse uses Theorem 9.7(a). Registered source:
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The statement's paired Markdown records the original conventions and source
comparison. This proof follows the finite content maximization and
fixed-support detected-constituent route described above rather than claiming
to reproduce the source's proof verbatim.

The localization and admissibility inputs correspond to
Bernstein--Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), sections 1.8--1.9, Theorem 2.5, and sections 4.5--4.7, as documented
in the imported results and `SegmentGenericStatement.md`. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The present proof imports these established results by Lean name and adds no
classification hypothesis. It proves generic segment exhaustion only; unitary
exhaustion, analytic square-integrability of normalized blocks, and strict
real-exponent bounds remain separate obligations.
