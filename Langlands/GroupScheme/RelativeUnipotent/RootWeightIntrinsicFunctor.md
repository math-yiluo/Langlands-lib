# Intrinsic root-weight subgroup functors on all scheme tests

This derived module extends the intrinsic root-weight cutoff comparison to an
actual subgroup functor on every scheme over the arbitrary affine base. It uses
`RootWeightIntrinsicCutoff` and the published all-test corepresentation of an
actual polynomial scheme chart with its original group law.

`intrinsicPoints` is a group equivalence from U-points on T to the actual affine-
point group over the relative global sections of T. It is formed from
`AffineLinearEmbedding.pointsMulEquiv` and `Corepresented.pointsEquiv`; the scheme
chart itself is not assumed additive. Its naturality is proved along every map
of test schemes. `intrinsicPoints_coord` proves that these points have exactly
the original ordered root coordinates.

`intrinsicCutoff` is the subgroup functor obtained by pulling back the intrinsic
cyclic weight subgroup through this actual group equivalence. Its restriction
law follows from naturality and preservation of weight subgroups by algebra maps.
It is defined for every cutoff and cocharacter, without a positivity premise.

When the specified cocharacter pairings give supplied natural root weights,
`mem_intrinsicCutoff_iff` identifies each positive intrinsic cutoff with the
corresponding supported root coordinates on every test scheme. Consequently,
`intrinsicCutoff_eq_weightSubgroup` proves equality of subgroup functors with
W.subgroup d when the pairings are q times W's weights and the intrinsic cutoff
is q*(d+1), for q > 0. This preserves the original unscaled filtration.

The test schemes need not be affine, reduced or connected. The identification
here is inside the supplied root-chart group U. Transferring it between different
chart groups, proving the required ambient parabolic normalization and changes of
torus, and performing effective descent remain separate steps of Task 7200.
