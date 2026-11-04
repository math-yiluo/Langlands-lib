# Affine-line rigidity and split-unipotent source homomorphisms

Author: Worker 1478.

This construction works over every field `k : Type u`. The Prop-valued
condition `HasConstantAffineLineMaps G` means that every actual morphism
over `Spec k` from the affine line to `G.X` factors through the terminal
object of `Over (Spec k)`, with a specified existential `k`-rational value.
It is stated for any actual group scheme. It does not assert affineness,
smoothness, connectedness or unipotence.

For a smooth connected unipotent group this is the constancy property in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Definition B.2.1, printed p.568, one-based PDF p.594. The registered source
is `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Our definition extends that formula to arbitrary group schemes rather than
using the word wound for this larger class.

`exists_constant_of_isVectorGroupOfDimension_one` uses the existing natural
vector coordinates and `RelativeRoot.AdditiveGroupQuotient.lineIso` to
transport the condition to any one-dimensional vector group. For an actual
group homomorphism from this group, evaluating its constant value at the
identity section identifies the value with the identity section of `G`.
This proves `hom_eq_zero_of_isVectorGroupOfDimension_one`. Neither result
assumes geometric properties of `G`.

`hom_eq_zero_of_hasSplitSeries` proves by induction that every actual
homomorphism from an affine group carrying the published finite Ga-series
to `G` is zero. At series length zero, bottom range of the source identity
homomorphism makes its identity scheme morphism the identity-valued constant
map, which kills every homomorphism from that source.

At a successor step, the next closed subgroup is affine because the source
is affine. Induction kills the restriction of the homomorphism to that
subgroup. The series gives equality between its full subgroup-functor range
and the range of the actual scheme kernel of the quotient. Evaluating that
equality on the kernel scheme supplies an actual factorization of the
kernel inclusion, so the full scheme kernel is killed.

The supplied quotient is flat and surjective. Its source is affine, and
its target is affine by its one-dimensional vector coordinates; in
particular its target is quasi-separated over the field. Quasi-compactness
of the source structure map therefore implies quasi-compactness of the
quotient. `FpqcHomDescent.hom` descends the original homomorphism through
this fpqc quotient. The one-dimensional result kills the descended
homomorphism, and its factorization equality kills the original one.
This argument does not assert surjectivity on the points of each test
scheme and uses no torsor-triviality or rational-point-lifting result.

`hom_eq_zero_of_isSplitUnipotent` chooses the finite series from the
existing `RelativeRoot.IsSplitUnipotent` predicate. Its source is assumed
affine, and its target satisfies `HasConstantAffineLineMaps`.
`hasNoNontrivialSplitUnipotentSubgroup` then applies this result to every
smooth connected split-unipotent closed subgroup of an affine `G`. Such a
subgroup is affine; its inclusion is zero, hence its full range is bottom
on every relative scheme test. Normality of the subgroup is not required.

Finally, `splitTorus_action_eq_trivial` applies the published
`AutomorphicAction.eq_trivial_of_no_split_unipotent_subgroup`. On a smooth
connected affine `G` satisfying the constancy condition, every actual
split-torus action equals the trivial action as an `AutomorphicAction`,
so its action morphism is the second projection. This retains arbitrary
universe `u`, every field, and all relative scheme tests.

The homomorphism induction and application are derived constructions using
the existing vector-group, finite-series, fpqc descent and actual-action
interfaces. The endpoint gives the split-torus case motivated by CGP
Proposition B.4.4, printed pp.577–578, PDF pp.603–604, with a potentially
more general ambient group and an explicit affine-line constancy premise.
CGP's proposition allows arbitrary tori on wound unipotent groups; descent
from a splitting field for a nonsplit torus is not claimed here. No
converse to the constancy condition is proved. Establishing it for the
ordinary unipotent radical modulo the split radical, and proving the host
pseudo-parabolic rational-lifting statement, remain separate obligations.
