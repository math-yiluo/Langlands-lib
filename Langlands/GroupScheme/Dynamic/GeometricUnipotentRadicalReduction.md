# Dynamic geometric radicals from reductivity of the centralizer

This internal reduction uses the published torus-action unipotence theorem
to remove the two general unipotence assumptions from the earlier
`Dynamic.UnipotentStructure` reduction. It proves unipotence of actual
identity-limit representatives in a smooth affine ambient group and reduces
the full geometric radical target to the separately owned dynamic-centralizer
reductivity statement. It does not prove that remaining statement.

## Unipotence for smooth affine ambient groups

`Dynamic.isUnipotent_unipotentRepresentative` applies over every field to
every cocharacter of a smooth affine group scheme and every group scheme
representing its actual dynamic identity-limit functor. Affine dynamic
representability implies that the representing inclusion is closed. The
published `Dynamic.isUnipotent_of_torusActionUnipotence`, applied to the
actual theorem `RelativeRoot.torusActionUnipotence`, then proves unipotence
in the existing representation-theoretic sense.

The action used by that imported adapter is conjugation by the original
cocharacter on the actual representative. Its zero Lie weight space is
trivial, and the representative is smooth and connected by the published
dynamic structure results. No general closed-subgroup unipotence or
unitriangular unipotence proposition is assumed here. Smoothness of the
ambient group is an essential hypothesis of this route.

## Full geometric structure

`Dynamic.isGeometricUnipotentRadical_of_centralizer` assumes that the ambient
group is smooth and affine, that `p : P → G` represents its dynamic
parabolic, that `r : U → P` has composite representing its dynamic
identity-limit subgroup, and that `z : Z → G` represents its dynamic
centralizer. Its only further input is `IsConnectedReductive Z`.

Closedness of the dynamic inclusions implies closedness of `r`.
Published dynamic smoothness and connectedness give the corresponding
properties of `U`. The first lemma gives unipotence. The normality theorem
from `Dynamic.UnipotentStructure` gives normality in `P`.

Base change to the algebraic closure preserves smoothness and affineness of
the ambient group. The base-changed composite represents the actual
identity-limit subgroup of the base-changed cocharacter. Apply the same
connectedness and unipotence results there. Finally,
`Dynamic.isGeometricUnipotentRadical_of_reductive_centralizer` supplies
geometric normality and the full greatestness clause: every smooth connected
normal unipotent closed subgroup of the base-changed parabolic factors
through the base-changed `U`. Such a subgroup need not descend to the
ground field.

## Universal reduction and provenance

`DynamicGeometricUnipotentRadicalFromCentralizerStatement` is the
Prop-valued implication from `DynamicCentralizerReductiveStatement` to the
existing exact `DynamicGeometricUnipotentRadicalStatement`.
`dynamicGeometricUnipotentRadical_of_centralizer` proves this implication
using the canonical affine centralizer representative and the preceding
assembly. The centralizer proposition remains an explicit hypothesis; this
is not an unconditional proof of the full radical target.

All fields, universe parameters and compatible representatives are arbitrary.
The subgroup representation hypotheses and greatestness conclusions concern
every test scheme, including nonreduced tests. No splitness or characteristic
restriction is imposed on the ambient group or field.

This is a derived internal consequence of the imported published theorems,
base-change instances and the existing radical predicate. It introduces no
additional external structural assertion. The external mathematical input
used through `RelativeRoot.torusActionUnipotence` is documented in its
published proof pair; this reduction adds no new citation.
