# Open chart on the off-diagonal base change

This internal adapter supplies actual recursive chart data for the
schemehood proof. It uses the separately reviewed `EtaleImageSaturation`
constructions and the universal properties of scheme and fppf sheaf
pullbacks. All constructions are at arbitrary universe `u`.

Let `e : B → T` be separated, and let `w : V → B`. Suppose the actual
fppf sheaves `G` and `F` fit into a cartesian presheaf square with
projections `π : G → F` and `p : G → h_B`, bottom arrows `f : F → h_T`
and `h_e`. Let `a : h_V → G` be an open immersion satisfying
`a ≫ p = h_w`. The structure `OffDiagonalImageChart e w sq a ha`
retains an actual fppf sheaf `H`, its two projections, its cartesian
square over `p` and `h_(offι e ≫ left e)`, and an open chart from the
fixed scheme `offChart e w`.

The theorem `nonempty_offDiagonalImageChart` constructs this data.
`H` is the sheaf pullback along the first relation coordinate. The
relation equation supplies a map from `H` to `G` using the second
coordinate, and pullback pasting proves that this second square is
also cartesian. The lifted chart is the base change of `a` along this
map, so it is open. Its first projection is exactly the off-diagonal
restriction of `translate`, and its base projection is exactly the
Yoneda map of `pullback.fst (offι e ≫ right e) w`.

`isAffine_offDiagonalChart` proves that the fixed chart source is affine
when `e` is etale and `B`, `T`, and `V` are affine: the off-diagonal is
affine by `EtaleOffDiagonal`, and its pullback with `V` over `B` is
affine. `locallyOfFiniteType_offDiagonalChart` proves that its map to
the off-diagonal is locally of finite type whenever `w` is, by base
change. No monomorphy hypothesis on `f` is needed for these constructions.
This module does not assert the induction or representability conclusion.
