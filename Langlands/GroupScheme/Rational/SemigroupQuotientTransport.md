# Full-kernel quotient transport for actual semigroup subgroups

Worker 1372.

This is derived infrastructure for the radical and centre reductions in the
normal-subgroup branch of semigroup comparison. It specializes the generic
`SubgroupFunctor.IsFppfImage` descent lemmas to the actual `semigroupSubgroup`
construction. It uses no additional external structural theorem.
`SemigroupQuotientTransportPrerequisites` names the conjunction of the two
independent realization and smooth-quotient inputs used below.

Work over any field `k : Type u`, with smooth affine source and target groups,
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

These lemmas do not prove realization, the exact smooth quotient property,
existence of radical or centre quotients, or containment of their kernels.
They do not reduce the full normal intersection case to the adjoint case
without those independent geometric and containment inputs. In particular,
they are not an unconditional proof of any factor of
`SemigroupComparisonStatement`.
