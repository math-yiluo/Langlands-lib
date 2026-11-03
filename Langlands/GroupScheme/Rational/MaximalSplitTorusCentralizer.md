# Testing maximal splitness in closed subgroups and centralizers

Author: Worker 1445.

This is an internal consequence of the published definitions of split-subtorus
maximality and the all-test centralizer. It supplies formal steps for the
ambient-maximality argument of `MinimalParabolicLeviCentralizerStatement`.
It does not prove that statement, construct a rational Levi, or prove a
geometric parabolic refinement theorem. The target and its imports are unchanged.

For any base scheme, `range_le_torusCentralizer_of_factor` proves that a
commutative subgroup containing another commutative subgroup centralizes the
smaller subgroup. It combines self-centralization with the published
contravariance of the centralizer under factorization. All containments test
every scheme over the base and every refinement of it.

Over an arbitrary field in universe `u`,
`IsSplitSubtorus.factorInClosedSubgroup` constructs the canonical factor of a
split subtorus `b : B → G` through a closed subgroup `j : H → G` containing
its range on every test scheme. The result bundles the actual homomorphism
`bH : B → H`, its split-subtorus property, and the identity `bH ≫ j = b`.
The construction applies the published represented-subgroup `factorHom` to
the range of `j`; closedness descends from the ambient embedding.
`factorInClosedSubgroup_comp` and
`isSplitSubtorus_factorInClosedSubgroup` expose the two properties. This
requires splitness, without requiring maximality of `b`. Both ambient
maximality criteria below use this construction.

Over an arbitrary field in universe `u`,
`IsMaximalSplitTorus.comp_of_torusCentralizer_le_range` upgrades maximality in
a closed subgroup `j : H → G` to maximality in `G`, provided `H` contains
the whole ambient centralizer of the torus. Any larger ambient split torus
centralizes the original torus, so its all-test image factors through `H`.
Closedness descends to that factor, and maximality in `H` makes the original
factor map an isomorphism. The converse is the existing closed-subgroup
restriction theorem; `isMaximalSplitTorus_comp_iff_of_torusCentralizer_le_range`
packages both directions. Applying this to a closed representative of the
centralizer gives `isMaximalSplitTorus_torusCentralizerFactor_iff` for the
published canonical factor `torusCentralizerFactor`. These results require no
smoothness, connectedness, affineness, finite type, or reductivity hypotheses.
They assume the stated centralizer containment or representative explicitly.

`IsMaximalSplitTorus.comp_of_maximal_extension_contained` instead assumes one
ambient maximal split torus containing the original torus, whose range is
contained in `H`. Its canonical lift to `H` makes the original factor map an
isomorphism by maximality in `H`. Inverting this map expresses the ambient
maximal torus inside the original ambient embedding, and the existing
`IsMaximalSplitTorus.of_factor` proves maximality of that embedding.
`comp_of_maximal_extensions_contained` obtains an ambient maximal extension
from the published extension theorem when `G` is affine and locally of finite
type, retaining the containment of those extensions as an explicit hypothesis.

The motivating original source is Borel and Tits, *Groupes réductifs* (1965),
registered as `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`,
Corollary 4.16(i) ⇒ (ii), printed pp.91–92 / PDF pp.38–39. The source first
extends a maximal split torus of the radical to one of the ambient group,
then uses a compatible-order parabolic and minimality to force that extension
back into the radical. The final two lemmas formalize only the extension and
containment step. The compatible parabolic, its Levi-centralizer description,
and the radical containment remain geometric proof obligations. The
centralizer criterion is a derived alternative local test, rather than a
claim that the source uses that exact formulation. None of these lemmas adds
an assumption to or proves the exact target statement.
