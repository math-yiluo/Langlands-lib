# Largest subtori over arbitrary base schemes

Worker 584 and Worker 632.

The theorem `relativeMultiplicativeTypeLargestSubtorus` proves exactly the
published proposition
`Langlands.GroupScheme.RelativeMultiplicativeTypeLargestSubtorusStatement.{u}`,
for every universe. For every group scheme of relative multiplicative type
over an arbitrary base scheme, it gives a largest closed relative subtorus.
Every closed relative subtorus with that largest property remains largest
after every base change in the same universe. The target and its imports
are unchanged.

The construction implements the torsion-free character quotient and fppf
descent described in Conrad, *Reductive group schemes* (2014),
Remark B.1.2, pp.280–281. The Lean proof uses the following stronger internal
property: a universal subtorus is a closed relative torus whose pullback
absorbs every homomorphism from every relative torus after arbitrary base
change.

For a diagonalizable group with finitely generated character group, choose
a decomposition of that group into a finite free part and a finite torsion
part. The free-character factor is a closed split torus and is the full
kernel of the projection to the finite-character factor. The latter group
scheme is killed by a nonzero integer. Nonzero multiplication on a relative
torus can be cancelled, so every homomorphism from a relative torus to
that finite factor is trivial. This proves the universal property, including
after arbitrary base change.

The defining fppf cover of a group of multiplicative type makes it
diagonalizable on each cover member. The helper
`IsMultiplicativeType.exists_universalSubtorus` chooses the local universal
subtori and applies `UniversalSubtorusDescent.representative` and
`UniversalSubtorusDescent.universal`. On each pairwise overlap the two local
subtori absorb one another, so their all-test ranges agree. Effective
descent of closed subgroup functors gives a global closed group scheme.
Its relative-torus property descends by fppf descent of smoothness,
relative affineness and commutativity, reflection of torus residue fibres,
and the published criterion that a commutative reductive group scheme is
a relative torus. Its universal property descends by checking range
containment on the pulled-back fppf cover for every further base change.

Finally,
`relativeMultiplicativeTypeLargestSubtorus_of_exists_universal` first
forgets the stronger property to obtain a largest closed subtorus. Any
other largest closed subtorus absorbs this universal one. Composing the
universal factorizations with that comparison transfers the stronger
property directly to the other representative. Its arbitrary base changes
are therefore largest as well, as required by the exact statement.

No affine, nonempty, reduced or noetherian condition is imposed on the
base or the fppf cover members, and no global bound on the local torsion
exponents or torus ranks is needed.
