# Local Borel containment from a supplied split-solvable Borel

`HasZariskiLocalConjugateContaining t i` states the first local-containment
conclusion of `SplitBorelZariskiLocalConjugacyStatement`: at every base point,
an actual rational conjugate of the pulled-back subgroup `i` contains the
pulled-back range of `t` on an open neighbourhood. The definition works over
any scheme and for arbitrary represented subgroups. Conjugation is `g*x*g⁻¹`,
and containment concerns points on every test scheme.

The first lemma assumes a subgroup `i₀` containing `t` and Zariski-local
conjugacy from `i₀` to `i`. Invert the local conjugator to carry `i` back to
`i₀`. Base change preserves the given containment, so this inverse conjugate
contains the pulled-back range of `t`. This establishes the required
orientation of the conjugating point.

Over any commutative ring, the second lemma assumes a reductive ambient group,
two relative Borels `i₀` and `i`, and a supplied fppf quotient `q` of the source
Borel onto a split torus `Q`. A monomorphic affine kernel presentation `j`
represents its actual kernel range and has a finite affine vector series.
The quotient map is flat, surjective and locally of finite presentation.
Relative parabolicity makes the source Borel affine and smooth. The published
relative parabolic closedness theorem gives closedness; preservation of
parabolicity at every field-valued base point then permits the published
self-normalizer theorem. The split torus is affine. The affine conjugating
cover theorem supplies one affine etale surjective test scheme and an
all-test conjugating point, using the published etale Borel conjugacy theorem.
Etaleness supplies flatness, and the existing vector-series local-conjugacy
theorem gives local rational conjugators.

The final theorem combines these two lemmas. It applies to any supplied `t`
whose range is contained in the source Borel. No connectedness, nonzero-ring,
field, or further splitting hypothesis is imposed on the base ring. It does
retain the source Borel, its containment, quotient, and kernel series as
explicit inputs. In particular it does not construct the split Borel structure
from root data and does not prove the unchanged full target statement.

This is internal derived content: the proof composes the published subgroup
base-change and inversion APIs, affine conjugating covers, relative parabolic
closedness and self-normalization, and vector-series local descent. It follows
the split-solvable descent step of Conrad's proof of Corollary 5.2.13(1) while
keeping the structural construction as a separate premise. No transporter
representation is assumed or constructed here.
