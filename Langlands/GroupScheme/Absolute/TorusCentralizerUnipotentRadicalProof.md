# The unipotent radical of a torus centralizer

This proof establishes the existing
`TorusCentralizerUnipotentRadicalStatement` at arbitrary universe `u`.
It retains the supplied torus map `s`, centralizer inclusion `c`,
ambient radical inclusion `u`, and centralizer radical inclusion `v`.
The equality is an equality of subgroup functors on all relative test
schemes, including nonreduced tests.

Over the algebraically closed base field the torus is split, by the
published finite Galois splitting theorem and split reflection. Choose
a cocharacter through `s` having exactly the same full centralizer.
The published torus-centralizer geometry makes `C` smooth and connected.

For the inclusion from the radical of `C` into the radical of `G`,
extend the supplied torus to a maximal torus of `G`. Every Borel
containing this maximal torus contains the chosen cocharacter. The
published centralizer Borel-containment theorem therefore places the
image of `v` in every such Borel. The published Chevalley unipotent
envelope supplies a smooth connected normal unipotent closed subgroup
of `G` containing that image. The greatest property of the supplied
ambient radical then gives the inclusion. The image of `v` under `c`
also lies in the range of `c` by composition.

For the reverse inclusion use the actual scheme-theoretic pullback
`U ×_G C`. Normality of `U` provides normalization by the cocharacter
and by `C`. Published fixed-subgroup smoothness and normal-unipotent
centralizer connectedness make the pullback smooth and connected.
Its closed inclusion into `U` makes it unipotent, and its second
projection has normal image in `C`. The greatest property of the
supplied radical of `C` bounds this second projection by the range
of `v`. Composing with the unchanged `c` and using the pullback range
equality yields the required reverse inclusion on every test.

The proof's provenance is internal composition of published Library
results. The source statement attributes the mathematical result to
Milne, Corollary 17.57; this file introduces no new literature claim
or additional structural premise.
