# Quotient and kernel comparison for actual semigroup subgroups

Worker 1372.

This is internal infrastructure for the radical and centre reductions in the
normal-subgroup branch of semigroup comparison. It specializes the generic
`SubgroupFunctor.IsFppfImage` and kernel-intersection descent lemmas to the actual
`semigroupSubgroup` construction, using the published equivariant functoriality
proof. It uses no additional external structural theorem.
`SemigroupQuotientTransportPrerequisites` names the conjunction of the two
independent realization and smooth-quotient inputs used to supply fppf images.

The first three lemmas work over any field `k : Type u`, with smooth affine groups,
a split torus, compatible actual actions, and an actual equivariant smooth
surjective group-scheme homomorphism `q : G ⟶ Q`. The additive character
semigroup `A` is unrestricted; it need not contain zero.

`isFppfImage_semigroupSubgroup` explicitly retains both
`SemigroupRealizationStatement.{u}` and `SemigroupSmoothQuotientStatement.{u}`
as premises. The former supplies monic representatives of the two subgroup
functors. The latter supplies a commuting homomorphism between them which is
smooth and scheme-surjective. Smoothness supplies flatness and local finite
presentation, so these data satisfy `SubgroupFunctor.IsFppfImage`. No claim of
surjectivity on points of every original test scheme is made.

`semigroupSubgroup_comap_eq_of_kernel_le` additionally requires containment of
the range of the full actual kernel inclusion `kernelι q` in the source
semigroup subgroup. It then identifies that subgroup with the full inverse
image of the quotient semigroup subgroup on every test scheme. Its proof
applies the generic fppf-image kernel lemma, which constructs local lifts by
pullback and descends membership in a monic representative. This retains the
entire scheme-theoretic kernel, including infinitesimal points.

`semigroup_comap_eq_of_smooth_quotient_square` applies this identity twice to
a commuting square `j ≫ q = p ≫ j'`. Both vertical maps `q` and `p` must be
equivariant smooth surjections, and the relevant source semigroup subgroups
must contain their full kernels. The intersection equality along `j'` then
implies the equality along `j`. The horizontal maps need not separately be
assumed equivariant, closed or normal for this formal transport argument.

The remaining three lemmas instead use comparison on the full represented kernel.
Fix a commuting square `j ≫ q = p ≫ j'`, with `j : H ⟶ G`,
`p : H ⟶ H'`, `q : G ⟶ G'`, and `j' : H' ⟶ G'`. Give all four groups actual
torus actions, and give another smooth affine group `U` an action and a map
`r : U ⟶ H`. Require equality of the all-test ranges
`range (kernelι p) = range r`. Thus `r` represents the full scheme-theoretic
kernel range, including its values on nonreduced tests. Require all-test
equivariance of `j`, `q` and `r`.

`semigroup_comap_eq_of_fppfImage_of_kernel_comparison` assumes:

- an actual `IsFppfImage` from the semigroup subgroup of `H` to that of `H'`
  along `p`;
- the semigroup intersection comparison along `j'`;
- the semigroup intersection comparison along `r ≫ j`.

It concludes the comparison along `j`, for arbitrary `A`. The groups
`G`, `H`, `G'` and `U` are smooth affine; `H'` is affine, with no smoothness
premise for this lemma. Neither vertical morphism is separately assumed smooth
or surjective. No equivariance premise on `p` or `j'` is needed beyond the
displayed fppf-image and quotient-comparison hypotheses.

The proof applies the generic commuting-square kernel-intersection descent
lemma. Equivariant semigroup functoriality supplies the ordinary image
containments along `j` and `q`. The range equality for `r` reduces containment
of the kernel intersection to comparison after inverse image along `r`.
The supplied kernel comparison and functoriality along `r` establish precisely
that containment. The generic proof then corrects a lift on an actual fppf
cover and descends membership. Containment of the entire kernel in either
semigroup subgroup is not needed.

`semigroup_comap_eq_of_smooth_quotient_of_kernel_comparison` additionally makes
`H'` smooth, assumes that `p` is an equivariant smooth scheme-surjection, and
retains the exact realization and smooth-quotient propositions. It constructs
the required fppf image with `isFppfImage_semigroupSubgroup`, then applies the
preceding comparison. The ambient vertical map `q` still only needs the stated
equivariance and the commuting square.

`semigroup_comap_eq_of_smooth_quotient_of_solvable_kernel` supplies the kernel
comparison conditionally when `U` is connected and solvable, `r` and `j` are
closed subgroup embeddings, and `0 ∈ A`. It retains the independent proposition
`Torus.SolvableFixedContainmentConnectedStatement.{u}` as a premise. The proof
derives closedness and all-test equivariance of `r ≫ j` and uses the existing
conditional solvable intersection theorem on this composite, before applying
the smooth-quotient consumer. It imposes neither normality of `j` nor algebraic
closure of the field. It does not prove solvable connectedness.

The realization and smooth-quotient propositions remain explicit inputs where
used. These lemmas do not construct radical or centre quotients, identify their
full kernels, prove the kernel connectedness input, or prove the requisite
quotient comparison. They do not reduce the full normal intersection case
without those independent structural inputs, and do not prove the unrestricted
`SemigroupComparisonStatement`.
