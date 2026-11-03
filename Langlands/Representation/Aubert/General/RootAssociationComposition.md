# Inverses and products of actual root-association representatives

Worker 78. These internal deductions extend the published elementary laws in
[`RootAssociationLaws`](RootAssociationLaws.md). Their purpose is to retain the
actual normalizer element when composing associations in support arguments.
They follow directly from the existing definitions and make no claim to prove
a representation-theoretic assertion of Renard or Aubert.

The setting and hypotheses are exactly those of `rootAssociation`: a field,
an affine group scheme, a torus morphism whose underlying scheme morphism is
monic, an arbitrary cocharacter, and the point-normalizer and full-centralizer
comparisons `hN` and `hZ`. No topology, reductivity, genericity, finite root
system, or representation is needed. The index sets consist of the literal
simple-root labels, including empty sets.

`rootAssociation_inv` reverses an association `I → J` represented by `n`,
using the actual inverse point `n⁻¹`. Closure of the point normalizer under
inverses supplies its membership. The quotient map and `weylCharacterAction`
are group homomorphisms, so the resulting character action is the inverse
integral linear equivalence. Applying it to the given image equality gives
`rootSet J → rootSet I`. `rootAssociation_inv_iff` records the converse by
inverting twice.

`rootAssociationRepresentativesInvEquiv` constructs the resulting equivalence
between the type of actual point representatives for `I → J` and that for
`J → I`. Both maps send the actual point to its inverse; the inverse law
on points and subtype extensionality prove the two inverse identities.

`rootAssociation_mul` composes an association `I → J` represented by `n`
with one `J → K` represented by `m`, using the literal product `m * n`.
Normalizer membership follows by multiplication. The quotient and action
homomorphisms turn this product into composition of the character actions.
The elementary identity for the image of a composite map then applies the
two supplied root-set image equalities.

The multiplication order agrees with conjugating a Levi first by `n` and then
by `m`: the combined conjugation is by `m * n`. This module proves only the
root-association conclusions. A support argument must retain the corresponding
Levi membership equivalence for that same product separately. No Levi
conjugation, cuspidality transport, geometric lemma, or Jacquet nonvanishing
is assumed or established here.
