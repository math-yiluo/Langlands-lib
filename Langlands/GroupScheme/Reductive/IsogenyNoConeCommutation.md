# No-cone commutation under a root-datum isogeny

This derived module proves the actual-target commutation law needed
in the split isogeny construction. Let `f` be a root-datum isogeny
from the target datum `Q` to the source datum `P`, with exponent `p`.
Assume the coefficient ring is local and satisfies the host condition
that `p` vanishes whenever some root factor is not one. The actual
target group is reductive, its closed coordinate split torus is
maximal on every fibre, and `Q` is its full fibrewise root datum.
Both abstract integral root data are finite and reduced.

`IsogenyNoConeCommutationStatement` says that any actual target root
parametrizations corresponding to source roots `x`, `y` commute
over every affine test, provided the source roots are not opposite
and have no positive integral mixed root. The latter condition is
defined by `NoMixedRoot`: no source root equals `s*x + t*y` for
natural numbers `s`, `t` both at least one. The roots may coincide.
The theorem `isogenyNoConeCommutation` proves this statement.
`pointsCommute_correspondingRoots` is the direct source-indexed API;
`pointsCommute_of_noMixedRoot` instead uses target indices.

No ambient source group or freeness hypothesis is needed. The
statement does not require that the target cone be empty. Locality
of the coefficient ring is retained; passage from local tests to
the arbitrary affine base of the host isogeny theorem remains a
separate assembly step.

The proof chooses corresponding bases from the supplied isogeny.
The published local normalized-family construction gives actual
target simple-root maps, their Weyl reflections and rank-one
normality. A target pair of distinct, nonopposite roots is reduced
by one simultaneous Weyl word to a simple root and a positive
integral combination of two distinct simple roots. Reflection
compatibility of the root bijection transports the original
source no-mixed-root and non-opposition conditions to this pair.

A source pair with no mixed root and which is not opposite has
nonnegative Cartan pairings: otherwise its sum is a root. The
weighted Cartan identity for `f` therefore forces nonnegative
target pairings as well. The finite rank-two root lists then
exclude every potentially noncommuting standard pair except
two cases.

In target type B₂ the remaining pair is the short simple root
`a` and `s_c(a) = a+c`. If the source Cartan entries have the same
orientation, the corresponding source roots have a sum equal to
a root, contradicting the hypothesis. The exchanged orientation
forces the root-factor ratio two, hence `p = 2`, and the host
characteristic condition gives `2 = 0` in the original ring.
The genuine target B₂ relation for this pair has one term with
coefficient two, so its two root maps commute.

In target type G₂ the remaining pair is the short simple root
`a` and `s_a(s_c(a)) = 2a+c`. The same-orientation case again
contradicts the source no-mixed-root condition. Exchanged lengths
force root-factor ratio three, hence `p = 3` and `3 = 0` in the
original ring. The genuine target relation is a singleton with
coefficient minus three and therefore gives commutation. Every
other allowed target pair has an empty target cone and uses the
published actual-root commutation theorem directly.

Simultaneous conjugation preserves commutation. Scalar rigidity
compares any two actual parametrizations of the same target root
by a base-ring unit, and independent scalar rescaling preserves
commutation. These facts transfer the standard calculations back
to the two arbitrary target maps. Coincident roots are handled
by additivity of their common additive-line parametrization and
the same rigidity comparison.

The provenance is an internal composition of the published
rank-two coefficient lists, actual local root-family and
commutator constructions, and scalar rigidity with the supplied
root-datum-isogeny arithmetic helpers. No exceptional isogeny or
ambient isogeny theorem is assumed. The unit supplies one
commutation prerequisite and does not prove the full host
`AffineSplitIsogenyTheoremStatement`.
