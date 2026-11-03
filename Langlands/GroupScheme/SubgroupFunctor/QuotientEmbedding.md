# Subgroup embeddings on supplied quotients

Author: Worker 1369.

This internal derived unit constructs the induced subgroup morphism on two
supplied fpqc quotient groups over an arbitrary base scheme in universe
`u`. It constructs no quotient scheme.

Let `i : B → G`, `q : G → Q` and `qB : B → BQ` be group-scheme
homomorphisms, with `qB` flat, surjective and quasi-compact. If the actual
kernel range of `qB` is contained in the inverse image under `i` of the
actual kernel range of `q`, then `kernel_comp_quotient_eq_zero` proves
that `i ≫ q` kills the scheme-theoretic kernel of `qB`.
`quotientSubgroupHom` descends this composite by the published
`FpqcHomDescent.hom`, producing an actual group-scheme homomorphism
`j : BQ → Q`. The square `i ≫ q = qB ≫ j` commutes and uniquely
determines `j`.

If the two kernel subgroup functors are equal after inverse image, the
induced map is monic as a morphism over the base. The proof first shows
that every test point of its kernel is the identity. A point lifts along
`qB` after an fpqc cover, where the square and the reverse kernel
containment show that its lift is killed by `qB`. Thus the original
point is locally the identity, and effective epimorphism cancellation
gives the equality globally. Applying this to the right difference of
two points proves monicity.

Assume also that `i` is monic and that the ambient kernel range is
contained in `range i`. `quotientSubgroupHom_isPullback` proves that the
commuting square is cartesian on actual schemes over the base. The
inverse-image theorem in `QuotientPreimage` supplies a point of `B`
above each compatible pair. Monicity of `j` makes its quotient image
the specified point of `BQ`, and monicity of `i` proves uniqueness.

If `q` is also flat, surjective and quasi-compact and `i` is closed,
`quotientSubgroupHom_isClosedSubgroup` descends the closed immersion
along this cartesian square to prove that `j` is a closed subgroup.
The implemented proof separately descends universal closedness and local
finite type. Monicity gives separatedness, so `j` is proper. The theorem
that a proper monomorphism is a closed immersion finishes this step.
`quotientSubgroupHom_comap_range` gives the exact inverse-image equality
on every original scheme test; it needs only the forward kernel
containment and containment of the ambient kernel in `B`.

The provenance is actual fpqc homomorphism descent, local lifting,
scheme-theoretic kernel membership, represented subgroup descent and
fpqc descent of closed immersions. The intended application is the
central quotient branch of Borel normalizer induction. Existence of
`Q` and `BQ`, and the Borel property of the resulting closed subgroup,
remain separate geometric obligations.
