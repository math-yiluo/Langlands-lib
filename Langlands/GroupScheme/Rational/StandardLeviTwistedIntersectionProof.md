# Twisted intersections of actual standard Levi subgroup functors: proof

Authors: Worker 1373 and Worker 1452, whose joint published assembly supplies
the centralizer and root-criterion argument used here.

`Langlands.GroupScheme.standardLeviTwistedIntersection` has exactly type
`Langlands.GroupScheme.StandardLeviTwistedIntersectionStatement.{u}`.
It has no additional theorem parameters. For every field `k : Type u`,
connected reductive group scheme `G` over `Spec k`, maximal split torus
inclusion `i : T.toGrp ⟶ G`, generic cocharacter `ν`, and supplied
`IsRelativeWeylCoxeterRealization i ν cs`, it proves
`IsStandardLeviTwistedIntersection i ν cs`.

Thus, for all finite subsets `I,J` of the actual simple relative roots, every
minimum double-coset representative `w`, and every `n : normalizerPoints i`
whose quotient class is `w`, the conclusion is the literal equality

`standardLevi i ν (rootSet i ν J) ⊓
 (standardLevi i ν (rootSet i ν I)).comap (G.innerIso n).hom =
 standardLevi i ν (rootSet i ν (intersectionSubset cs I J w))`.

This is equality of the published subgroup functors on every test scheme,
including nonreduced test schemes. At rational points its preimage term is
`n⁻¹ L_I(k) n`. Every normalizer lift is covered. There is no restriction
on characteristic or perfectness, no splitness or quasi-splitness hypothesis
on `G`, and no assumption that the relative root system is reduced or that
the simple-root type is nonempty. The field and scheme universe `u` is
arbitrary.

## Implemented proof and declaration-level dependencies

The proof applies
`standardLeviTwistedIntersection_of_connected_of_negation` from
[`StandardLeviTwistedIntersectionAssembly`](StandardLeviTwistedIntersectionAssembly.md).
Its two global structural premises are supplied by published unconditional
theorems:

- `dynamicConnected : DynamicConnectedStatement.{u}` from
  [`Dynamic/ConnectedProof`](../Dynamic/ConnectedProof.md), giving
  connectedness of dynamic centralizer representatives in a smooth affine
  connected ambient group over a field.
- `relativeRootNegation : RelativeRootNegationStatement.{u}` from
  [`RelativeRootNegationProof`](RelativeRootNegationProof.md), giving
  additive negation stability of the actual relative roots of a maximal
  split torus in a connected reductive group over every field.

No structural statement remains as a theorem parameter. The assembly
specializes smoothness, affineness and connectedness using
`IsConnectedReductive`, and splitness and monomorphism using
`IsMaximalSplitTorus`. It obtains standard cocharacters for each finite face
from the supplied Coxeter realization and finite actual Lie weight support.
Its `standardLeviCentralizerFamilyOfCoxeterRealization` identifies the
choice-free standard Levi functors with actual dynamic centralizers.
For each `w` and each lift `n`,
`IsRelativeWeylCoxeterRealization.twisted_pairing_eq_zero_iff_of_lift`
supplies the root-vanishing criterion, and
`standardLevi_twistedIntersection_of_root_zero_iff` turns that criterion into
the all-test equality. The inverse torus-automorphism transport in that
comparison gives precisely the displayed comap orientation.
The linked assembly and its paired dependencies describe these arguments.

## Provenance and preservation

This is an internal derived proof composing the three published declarations
named above. It introduces no new original-literature assertion or
alternative standard Levi, root set, relative Weyl quotient, or intersection
subset. The target statement's Lean/Markdown pair and all pairs it imports
are unchanged. Its existing point adapters may now be applied to the proved
all-test equality. Point-normalizer comparisons, representation-theoretic
term reductions, and other statements outside this target are not asserted
by this theorem.
