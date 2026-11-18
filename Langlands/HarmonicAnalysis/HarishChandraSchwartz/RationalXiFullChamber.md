# Transporting the Xi upper estimate to the full chamber

This internal transport derives a full actual-chamber Xi upper bound
from the Library's lattice-section `RationalXiUpperBoundStatement`.
The substantive Xi upper theorem remains an explicit hypothesis.

The generic compact-extension lemma preserves the polynomial exponent
and exact Iwasawa half-weight when a subset is multiplied on the left
by a compact subset of the parabolic. Uniform Xi translation bounds
become uniform on that compact set using open-compact invariance.
Continuity bounds the height and the reciprocal of the positive Iwasawa
weight there. Subadditivity and inverse symmetry compare the original
height with the section height, and real-power comparison absorbs their
ratio into one finite constant.

The actual structural lemma proves that the maximal split torus itself,
with its identity inclusion into that torus, is a compatible split
component of the minimal Levi. It uses the published equality of the
minimal Levi with the torus centralizer, represented centralizer
structure, connected reductivity and the split-component factorization.

The full-chamber theorem applies the lattice Xi upper statement to this
identity component, then uses the exact compact-kernel-times-section
decomposition of `RationalMinimalChamberSection`. Positivity,
continuity, translation bounds and compact invariance of the actual Xi
and matrix height are published inputs. No identification of the lattice
section with the full chamber is made.

The resulting bound holds on the full chamber before intersecting with
the ambient common norm kernel. The construction keeps the structural
subgroup and Xi-defining Iwasawa subgroup separate, and imposes no
height-adaptation premise. It does not prove the lattice Xi upper
statement or the closed cuspidal conjugation bound.

`RationalXiFullChamberUpperBoundStatement` records this full-chamber
conclusion with the same structural hypotheses and arbitrary universe,
local field, group and compact/matrix choices as the original Xi upper
statement. `rationalXiFullChamberUpperBound_of_upperBound` proves the
implication from that original statement. An unconditional proof of the
original Xi upper statement is still needed to close this new statement.
