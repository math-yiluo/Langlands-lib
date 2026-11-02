# Characters of the actual rational-character valuation image

Author: Worker 200.

This is a derived construction toward Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, I.1, printed pp.239–240
(PDF pp.5–6), source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source defines unramified characters through the common norm kernel and
identifies the unitary subgroup. Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 version, V.2.3–V.2.4, printed pp.105–107
(PDF pp.111–113), source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
defines the actual integer image Λ(G) and factors unramified characters
through it. The declarations here implement the character groups of that
actual image. The topology assigned to the image is explicitly discrete;
comparison with a topology on rational points has a separate premise.

The field uses the existing `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` interface, without a characteristic restriction.
The shared `GroupScheme` is arbitrary because only actual character evaluation
and the resulting group homomorphism are used. The construction does not
assume connectedness, reductivity or a finite-rank character group.

`rationalDiscreteValuationImage G` is a copy of the existing actual range
`rationalCharacterValuationImage G`, with its existing commutative group
operations and the discrete topology. It changes neither its elements nor
its integer coordinates. `rationalValuationImageProjection` is the existing
valuation with codomain restricted to this range. Its surjectivity follows
from being a range restriction; its kernel is proved equal to the actual
`rationalCommonNormKernel` using the existing valuation-kernel equality.
No topology is assigned to rational points by these definitions.

`rationalImageCharacters G` is the group of continuous homomorphisms from
this discrete image to the usual complex units. It has the compact-open
topology, a Hausdorff topological commutative group structure, and includes
every algebraic homomorphism because the domain is discrete.
`rationalUnitaryImageCharacters G` is the Mathlib Pontryagin dual of the same
discrete image, hence the circle-valued continuous character group with the
compact-open topology. Mathlib supplies its Hausdorff topological commutative
group structure and compactness. This compactness holds for any discrete
group; it does not rely on an unproved finite-rank lattice theorem.

`rationalUnitaryImageInclusion` composes circle-valued characters with the
usual inclusion of the circle into complex units. The value lemma records
exactly that inclusion. `rationalUnitaryImageEquiv` constructs the inverse by
bundling each norm-one complex value in the circle. Its inverse laws use
pointwise extensionality. The inclusion is continuous for compact-open
topologies; compactness of its domain and the Hausdorff target prove continuity
of the inverse in `rationalUnitaryImageContinuousEquiv`.
`compactSpace_unitaryRationalImageCharacters` transports compactness to the
existing norm-one subgroup `unitaryCharacters` of complex characters of the
image. This is an intrinsic law of the constructed character groups.

`rationalImageCharacterPullback` composes with the actual valuation-image
projection as an algebraic homomorphism on rational points. Surjectivity of
the projection proves injectivity of pullback and the equivalence between
norm one on the image and norm one on all rational points. The kernel equality
proves that every pulled-back character is trivial on the actual common norm
kernel. These assertions require no rational-point topology.

The final section accepts a topology on the actual rational-point group and
displays the premise `Continuous (rationalValuationImageProjection G)`.
Under that premise, `rationalImageUnramifiedPullback` produces an element of
the previously constructed continuous `unramifiedCharacters` group for the
actual rational norm family. `rationalImageUnramifiedDescend` uses the
existing canonical quotient-to-image equivalence to descend any such
unramified character. Descent is continuous because its domain is the
discrete image. The representative formula is proved using the existing
quotient equivalence's formula, and surjectivity of the projection proves
the two inverse laws in `rationalImageUnramifiedEquiv`. This last equivalence
is algebraic: it asserts no comparison of compact-open topologies on the
character group of rational points.

The discrete image is not asserted here to have its subspace topology in an
integer dual or to have finite rank, full rank or a specified split-center
index. These remain proof obligations. In particular this module does not
yet identify these groups as finite-dimensional complex or compact Lie tori,
construct an exponential parameterization or a real-part map, prove a
finite-kernel restriction to the split center, or choose Haar measures.
Continuity of the actual projection for the canonical rational-point topology
and the corresponding unconditional character-group comparison remain
separate obligations. The construction provides actual-image objects toward
those comparisons and introduces no replacement group-scheme or
representation framework.
