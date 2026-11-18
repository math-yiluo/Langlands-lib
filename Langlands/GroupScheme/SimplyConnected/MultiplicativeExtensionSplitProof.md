# Multiplicative-type extensions of simply connected semisimple groups split

`Langlands.GroupScheme.simplyConnectedMultiplicativeExtensionSplit.{u}`
proves the exact unchanged
`SimplyConnectedMultiplicativeExtensionSplitStatement.{u}`.
The theorem applies the full reduction
`simplyConnectedMultiplicativeExtensionSplit_of_connectedAction` to
`multiplicativeTypeConnectedAction`.

For a faithfully flat homomorphism from an arbitrary affine finite-type
source onto a simply connected semisimple group over any field, the
reduction first passes to the full, possibly nonsmooth identity component
of the source. Its inclusion is open and closed. The restricted quotient
remains flat and its actual kernel remains of multiplicative type.
Connected-action rigidity makes that normal kernel central.

Over an algebraic closure, the reduced identity core of this source
remains faithfully flat onto the target and is connected reductive.
The induced map from its semisimple derived subgroup to the perfect
target is a central isogeny. Simple connectedness makes that map an
isomorphism, yielding a homomorphic section there.

The section descends to the original field: perfectness of the target
persists on the actual affine fpqc double overlap, including nilpotents.
Two lifts differ by a homomorphism to the separated commutative central
kernel. Perfectness kills that difference. Thus the two pullbacks agree
on the whole overlap, and fpqc homomorphism descent supplies a section
over the original field. Composing with the original identity-component
inclusion gives the required section into the full source.

## Provenance

The implemented proof is an internal derived-group and fpqc-descent
argument using the Library constructions described above. It proves the
published splitting proposition without altering that proposition or
its imports. It has no smoothness or connectedness assumption on the
original source and no smoothness assumption on its multiplicative-type
kernel.
