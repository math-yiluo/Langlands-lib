# Parabolic recognition with a full unipotent radical

This derived supporting unit concerns smooth connected affine groups over a
field, at arbitrary universe `u`. It does not assume that the ambient group is
reductive. The containing subgroup is required to be smooth and closed.

`Dynamic.quotientParabolicPreimage χ q` constructs the actual inverse-image
group scheme of the closed dynamic parabolic representative `P_Q(χ ≫ q)`.
`quotientParabolicPreimageInclusion` is its canonical inclusion in `G`.
The range theorem identifies its subgroup functor with the full inverse image
of `P_Q(χ ≫ q)` on every scheme test, including nonreduced tests.
The construction itself requires only that `Q` be affine.

`isParabolicSubgroup_of_dynamic_le_of_unipotentQuotient_kernel_le` assumes an
actual fppf homomorphism `q : G ⟶ Q`, a connected reductive target `Q`, and a
smooth connected unipotent full scheme kernel. Suppose the smooth closed
subgroup `H` contains both `P_G(χ)` and the entire kernel of `q`, on every test.
The theorem proves that `H ⟶ G` is a geometric parabolic subgroup in the
Library's Borel-containment sense.

The implemented proof uses the published smoothness theorem for this quotient
and `Dynamic.parabolic_isFppfImage`. The full inverse-image containment lemma
`SubgroupFunctor.IsFppfImage.comap_le_range` puts the inverse image of the
quotient dynamic parabolic inside `H`. This step lifts points on fppf covers;
it does not require surjectivity on the points of each original test.
The reductive dynamic-recognition theorem makes the quotient dynamic subgroup
parabolic, and `UnipotentQuotientParabolics.isParabolicSubgroup_preimage` makes
its full inverse image parabolic in `G`. The published
`IsParabolicSubgroup.of_smooth_overgroup` then proves the result for `H`.

`isParabolicSubgroup_of_dynamic_le_of_radical_le` specializes the criterion
over an algebraically closed field. It accepts a supplied representative of
the full ground-field unipotent radical and assumes that its entire all-test
image lies in `H`. The published `unipotentRadicalQuotient` constructs an actual
fppf pseudo-reductive quotient. Over this field the quotient is connected
reductive. `HasSmoothConnectedUnipotentKernel.of_representative` transfers the
radical's smoothness, connectedness and unipotence to the actual kernel. Its
exact kernel range identity supplies the required kernel containment.

The final theorem replaces dynamic parabolic containment by two separate
inputs: full centralizer containment for a split torus and positive dynamic
containment for a cocharacter generic for the actual adjoint roots of that
torus in `G`. The smooth affine generic-centralizer comparison and dynamic
factorization give `P_G(χ) ≤ H`, so the preceding radical criterion applies.
All three containments remain explicit hypotheses.

The provenance is internal and derived from the cited Library results; no
new assertion is attributed to external literature. This module does not
construct a radical representative, prove that a particular special-fibre
image contains it, or establish an integral reduction-preimage identity.
