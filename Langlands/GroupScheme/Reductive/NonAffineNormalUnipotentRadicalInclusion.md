# Radicals of normal subgroups in smooth nonaffine ambient groups

This internal derived construction works over an algebraically closed field
`k` in arbitrary universe `u`. Let `G` be a smooth group scheme, let
`i : H ⟶ G` be a normal closed subgroup, and let `s : V ⟶ H` be a supplied
represented unipotent radical. The group `H` need not be affine, connected,
or smooth. There are no quasi-compactness hypotheses on `G` or `H`.

`IsUnipotentRadical.normalAmbientActionOfSmooth` constructs an actual
`AutomorphicAction G V`. Normality first restricts ambient conjugation to
`H`; the smooth ambient acting group then acts on the represented radical by
`actionOfSmooth`. The theorem `normalAmbientActionOfSmooth_act_comp` identifies
this action after the composite inclusion `s ≫ i` with ambient conjugation on
every relative test scheme.

`isNormal_comp_of_smooth` uses that inclusion equation to lift the conjugate
of every point in the range of `s ≫ i`. It therefore proves normality of the
full range subgroup functor, including on nonreduced test schemes.
`range_comp_le_of_smooth` applies greatestness of any supplied ambient radical
to that normal closed composite. The source retains the supplied radical's
smoothness, connectedness and existing fixed-vector unipotence.

The argument follows the published `NormalUnipotentRadicalInclusion` proof,
replacing its affine radical-action input with the direct closed-factorization
construction in `NonAffineUnipotentRadicalAction`. The latter requires only
smoothness of the acting group. This removes the earlier affine, smooth and
connected hypotheses on the target subgroup without changing either radical
predicate. This module does not assert radical existence or preservation under
field extension.
