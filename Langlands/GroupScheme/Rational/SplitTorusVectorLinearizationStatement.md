# Linear coordinates for actual split-torus actions on vector groups

`SplitTorusVectorLinearizationStatement` requests natural coordinates in which
an actual split torus acts linearly on a finite-dimensional vector group over
an algebraically closed field, in arbitrary universe `u`. It is a proposition
target, not a proof.

The input `IsVectorGroup V` means that the actual group scheme has natural
additive coordinates on every scheme test for some finite dimension. The
output chooses a natural number `n` and a new family of coordinate group
equivalences `e`. The existing `IsLinearVectorCoordinates b e` requires both
naturality under every test morphism and scalar compatibility of the actual
action over each test's ring of global functions. Additivity already follows
from the coordinate group equivalences and the automorphic action laws.
There is no assertion that arbitrarily supplied initial coordinates are
linear for the action. Such an assertion fails in positive characteristic.

The source route is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second
edition (2015), Definition A.1.1 and Example A.1.2, printed p.466 / PDF p.492,
and Proposition B.4.2 and Theorem B.4.3, printed pp.576–577 / PDF pp.602–603.
In characteristic zero, the source records uniqueness of the linear structure
and linearity of every homomorphism between vector groups. In positive
characteristic a vector group is smooth commutative affine and killed by the
characteristic prime, so B.4.3 applies. It decomposes the group as its torus
fixed subgroup times a complementary vector group carrying a linear torus
action. For a connected group over an algebraically closed field, the fixed
factor is smooth connected commutative and killed by that prime; B.1.10,
printed pp.565–566 / PDF pp.591–592, makes that factor a vector group as well.
Choosing coordinates on it with the trivial torus action and combining them
with the linear coordinates on the complement gives the requested whole-group
linear structure. These steps explain the intended consequence of the cited
source; their formal proofs remain required.

The target permits multiple weights, the zero weight, and dimension zero.
It imposes no assumption that the torus fixed subgroup is trivial and no
single-character weight condition. It uses an actual scheme action and all
scheme tests, including nonreduced, nonaffine and empty tests. It neither
constructs a vector structure on an arbitrary unipotent group nor proves the
central-subgroup or exact ordered-product statements. The positive-
characteristic fixed-part argument uses algebraic closedness; this pair makes
no arbitrary-field linearization claim.

Source: registered `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The stated source locations were read directly. A bounded check of the current
Library's notes and wiki paths found no CGP-specific errata file; the registered
author-books-page navigation note records only that no dedicated errata link
was found in that section.
