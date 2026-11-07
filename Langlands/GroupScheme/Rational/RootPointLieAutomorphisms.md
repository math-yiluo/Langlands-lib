# Root-point Lie comparison under torus-fixing automorphisms

This internal construction acts on the actual intrinsic root subgroup points
by postcomposition with an actual ambient group-scheme automorphism fixing the
torus map. Its inverse is postcomposition with the inverse automorphism. This
construction, `rootPointsAutOfFixesTorus`, works over every base scheme and on
every test scheme.

`rootPointsActionOfFixesTorus` restricts any actual automorphic action fixing
the torus map to these intrinsic subgroup points. It uses the proved all-test
stability of the root subgroup. `basePointIso_fixes_torus` shows that evaluating
such an action at any point over the base gives an actual torus-fixing
automorphism. These facts also hold over arbitrary base schemes.

Over an arbitrary field, assume the ambient group is smooth and affine, the
acting torus is split, and the character is nonzero with no higher roots.
`representedRootPointLieEquiv_aut_apply` proves that the represented
point-to-Lie comparison intertwines the root-point automorphism with the actual
ambient differential. The proof restricts the ambient automorphism to the
representative, applies equivariant isomorphism naturality for its nonzero
weight coordinates, and uses naturality of the rational/coefficient point
comparison and the equality of the inclusion composites.

`rootPointLieEquiv_aut` obtains the same formula for the intrinsic chosen
comparison by using its actual chosen-representative specification. There are
no supplied coordinates and no restriction on the field characteristic or
common universe.

`rootPointLieEquiv_act` then gives the formula for the original action by every
rational point of the acting group, with the actual differential of that action
at the same point under the rational/coefficient comparison. The proof evaluates
the action as a group-scheme automorphism, applies the preceding automorphism
formula, and identifies its differential with the action differential. The
acting group has no affineness or smoothness assumption. Its all-test fixedness
on the torus map remains an explicit hypothesis.

This is an internal consequence of the imported represented root automorphism,
root stability, action evaluation and point-to-Lie constructions. Galois
transport and the root-field and apartment existence results remain separate
obligations.
