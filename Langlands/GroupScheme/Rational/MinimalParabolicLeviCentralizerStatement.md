# Rational Levis of a minimal parabolic as split-torus centralizers

Authors: Worker 1361 and Worker 1348.

`MinimalParabolicLeviCentralizerStatement.{u}` is an unproved structural
proposition for every field in universe `u` and every connected reductive
group scheme `G`. Given an actual minimal rational parabolic `j : P → G`,
an actual rational Levi `l : L → P`, and a represented geometric solvable
radical `r : R → P`, it asserts the existence of a commutative group scheme
`B` and a morphism `bR : B → R` such that:

- `bR ≫ r ≫ j` is a maximal split torus of the ambient group `G`;
- its whole-torus centralizer on every test scheme equals the image of
  `l ≫ j`.

In particular, maximal splitness is in `G`, not just in `P` or `R`. The
map through `R` retains radical containment. Splitness of `B` and closedness
of its ambient embedding are included in `IsMaximalSplitTorus`. The equality
is an equality of subgroup functors on all test schemes, rather than an
equality of rational or geometric point sets. The Levi predicate includes
an actual isomorphism of schemes for its multiplication with a geometric
unipotent radical.

The original source is Borel and Tits, *Groupes réductifs* (1965),
registered as `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
Corollary 4.16, printed pp.91–92/PDF pp.38–39, states that minimality of a
rational parabolic is equivalent to its rational Levis being precisely the
centralizers of ambient maximal split tori contained in its radical.
The present proposition is the implication (i) to (iii), with a specified
Levi and a specified radical representative. Theorem 4.15(b), printed
p.91/PDF p.38, gives the corresponding centralizer description for maximal
split tori of the radical of an arbitrary rational parabolic. The
implication (i) to (ii) in 4.16 upgrades radical maximality to ambient
maximality.

This is a derived scheme formulation of the cited implication. Its proof
must supply the all-test centralizer equality and actual factorization
through the chosen radical representative. It assumes neither that `G`
splits nor that the field is perfect. It asserts no result about a
specified maximal torus of `G`, so using it for the split-part theorem
still requires the separate radical/torus/Levi construction and formal
factorization and transfer arguments. No geometric theorem is proved by
this statement declaration. Worker 1348 contributed the structural
decomposition; Worker 1361 authored the interface and source comparison.
