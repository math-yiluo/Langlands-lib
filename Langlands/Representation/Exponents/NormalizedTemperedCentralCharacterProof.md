# Unitarity of central characters of nonzero normalized-exponent tempered representations

Authors: Worker 1597 and Worker 1598.

`Langlands.Aubert.General.RepresentedParabolic.normalizedTemperedCentralCharacter`
proves exactly the published
`NormalizedTemperedCentralCharacterStatement.{u, v}`. Every prescribed scalar
central character of a nonzero normalized-exponent tempered representation has
complex norm one at every element of the full center of the actual
rational-point group.

## Implemented proof

The proof introduces the unchanged target's field, connected reductive group,
nonzero smooth representation, prescribed character and two representation
premises. Connected reductivity supplies the affine instance, and the point
group receives its specified canonical rational-point topology.

The existence part of `splitComponentStatement` supplies an actual split
component `a : A.toGrp → G`. Applying
`normalizedTempered_splitComponentCentralCharacter_norm` proves norm one for
the original character at every image of an actual point of `A`. That
published theorem uses the canonical identity-parabolic and rational-Levi
data, its unit unipotent radical and multiplication isomorphism, the
identity-Jacquet comparison, and `normalizedTemperedFullGroupExponent`.
The scalar action and nonzero representation produce the required occurring
Jacquet exponent. These comparisons and full-group unitarity are proved
dependencies.

The published `centerSplitComponentCompactness` then gives compactness of the
full scheme-center point quotient by the literal image of this same split
component. It retains the full schematic center, including its possible
nonsmooth or disconnected factors, and the prescribed inherited quotient
topology.

Finally, `centralCharacter_norm_eq_one_of_splitComponent` applies to this
compactness and the proved norm equality. Its scalar-character regularity
argument derives local constancy from smoothness and a nonzero vector.
Pullback to scheme-center points is continuous, and the character's norm is
trivial on the actual split-component image. The compact-quotient norm
argument therefore gives norm one on all scheme-center points. The proved
`rationalCenterComparison` equality covers every element of the full abstract
point-group center, including the arbitrary central point introduced by the
present proof.

## Scope and provenance

This is an internal composition of the published proofs and constructions
imported by the Lean file. Worker 1598 contributed the identity-Jacquet and
split-unitarity arguments; Worker 1597 contributed the identity-parabolic
data, regularity, full-center extension and final composition. The final
theorem adds no structural or representation-theoretic premise.

The target retains arbitrary characteristic and nonsplit ambient groups,
field Hausdorffness, the canonical point topology, local compactness and the
nonarchimedean ambient group hypothesis, and independent field/group and
representation-carrier universes `u` and `v`. It retains `[Nontrivial π]` and
the actual normalized temperedness predicate, without adding irreducibility,
finite dimensionality, or character regularity.

The original-source locators and necessary nonzero correction remain in
[NormalizedTemperedCentralCharacterStatement.md](NormalizedTemperedCentralCharacterStatement.md).
This proof uses the normalized exponent parameter throughout. The separate
corrected-source comparison with the raw-log parameter in Renard V.3.20
remains a distinct obligation.
