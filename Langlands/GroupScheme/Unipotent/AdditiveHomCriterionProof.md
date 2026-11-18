# Unipotence detected by additive characters of closed subgroups

`Langlands.GroupScheme.unipotentAdditiveHomCriterion` proves the published
`UnipotentAdditiveHomCriterionStatement.{u}`. An affine algebraic group over
an arbitrary field is unipotent exactly when every nontrivial closed subgroup
has a nonzero homomorphism to the additive group.
[Statement and source comparison](AdditiveHomCriterionStatement.md)

The source is J. S. Milne, *Algebraic Groups* (2017), Proposition 14.22,
printed p. 285, registered as `milne-2017-algebraic-groups` with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The proof uses Milne's descent through kernels. It implements the descending
chain condition of Corollary 1.42 by induction on ideals of a Noetherian ring.

## Lean proof

In the forward direction, a closed subgroup of a unipotent group is
unipotent by `unipotentClosedSubgroup`. Its inclusion is a monomorphism, so
`SubgroupFunctor.range_comp_eq_bot_iff` transfers nontriviality of its range
to the range of its identity map. The subgroup is affine since it is closed
in an affine scheme. `Unipotent.exists_additive_character` gives a
homomorphism distinct from zero, which exhibits the required
`Nontrivial` instance. [Additive characters](AdditiveCharacter.md)

For the converse, let \(J\) be the ideal defining a closed subgroup \(H\)
in \(G\). The coordinate ring \(\Gamma(G,\mathcal O_G)\) is Noetherian
because \(G\) is affine and locally of finite type over a field. The proof
uses well-founded induction with respect to strict reverse inclusion on its
ideals. When the range of the inclusion is trivial, the range comparison
gives a split series of length zero for \(H\). Its unipotence follows by
`RelativeRoot.HasSplitSeries.isUnipotent`.

Otherwise the hypothesis gives a nonzero map \(f:H\to\mathbb G_a\).
The composite inclusion of \(\ker f\) into \(G\) is closed, and its defining
ideal contains \(J\). If the ideals were equal, the two closed immersions
into \(G\) would have equal kernel ideal sheaves because \(G\) is affine.
The inclusion \(\ker f\to H\) would then be an isomorphism, and the kernel
pullback equation would force \(f\) to be zero. Thus the defining ideal
strictly increases, and the induction hypothesis gives unipotence of
\(\ker f\). The comparison uses the complete defining ideals, so it also
applies to nonreduced closed subgroups.

The helper `isUnipotent_of_additive_kernel` uses `affineHomImage` to obtain
\(H\xrightarrow{q} I\hookrightarrow\mathbb G_a\) with \(q\) an fppf quotient.
The kernels of \(q\) and \(f\) represent the same subgroup functor and
are isomorphic. The image \(I\) is unipotent because it is closed in
\(\mathbb G_a\), which is unipotent by `VectorGroup.isUnipotent`.
The quotient map is quasi-compact since \(H\) and \(I\) are affine over the
field. Applying `isUnipotent_of_kernel_of_quotient` yields unipotence of
\(H\). The identity inclusion then gives the claim for \(G\).
[Affine homomorphism images](../AffineHomImageProof.md)
[Unipotent extensions](../Reductive/UnipotentExtension.md)
