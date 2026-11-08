# Averaging transitions for stable Jacquet lifts

Author: Worker 1775.

This derived supporting unit addresses the compatibility needed when Renard
VI.9.7 identifies the inverse system of stable compression images with the
inverse system of Levi-fixed Jacquet vectors. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, version dated 9 July 2026,
VI.9.7, printed pp.205–206 / PDF pp.211–212, with VI.9.1, Remark 2,
printed pp.197–198 / PDF pp.203–204. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The ambient topological group and the complex representation space have
independent universes. The representation is smooth, with no admissibility,
finite-dimensionality or stationarity hypothesis.

`leviCompactIndex M hM K` is the actual inverse image of the ambient compact
open subgroup `K` under `M.subtype`. Closedness of `M` makes this inverse
image compact; its openness follows from the subgroup topology. Its membership
criterion and monotonicity are proved directly. If a family contains an index
inside every open identity neighborhood of the ambient group, its Levi
intersections are cofinal among compact open subgroups of `M`. The proof
lifts an open subgroup of `M` to an open subset of the ambient group and
chooses an index there. No ambient compact-neighborhood existence is assumed
implicitly: the neighborhood property is an explicit input.

`exists_expandedLowerSubgroup_le_shift` assumes an Iwahori contraction for
`K` and an arbitrary open subgroup `L`. It uses the lower contraction for
`K` to obtain an exponent `s` such that every expanded factor
`g^b(K ∩ Nbar)g^-b` lies in
`g^(b+s)(L ∩ Nbar)g^-(b+s)`. Normalization of `Nbar` by `M` is explicit.
The witness is obtained by conjugating the original lower element by `g^-s`.

For compact open `L ≤ K` admitting `IsIwahoriContraction` for the same
`N, M, Nbar, g`, `averageMap_mem_stableImage` additionally assumes
`∀ m ∈ M, m * g = g * m`: the element `g` commutes with every element of
`M`. This is distinct from membership `g ∈ M` and is not supplied by
`IsIwahoriContraction`. Under this centrality hypothesis it proves that
`e_K` sends the stable image at `L` into the stable image at `K`.
For each `b`, a stable vector at `L`
has a witness in the range of compression to the power `b+s`. The
expanded-factor range identity expresses it as `e_L w` for a vector fixed
by that larger expanded factor. Therefore `e_K e_L w = e_K w` is in the
`b`-th range at `K`. Intersecting these ranges proves stable membership.
`stableAverageMap` is this actual restricted linear map with the same
centrality hypothesis. The imported expanded-factor range identity uses
that hypothesis. Closedness of the lower subgroup and opposite contractions
are not required for these claims.

`map_mk_averageMap_of_stableImage` treats a linear map on `N`-coinvariants
whose value at the class in question is invariant under `K ∩ M`. It also
assumes that `g` commutes with every element of `M`. Choose
a stable-power preimage and translate it by `g^s`, obtaining `u` fixed by
`K ∩ Nbar` and `L ∩ M`, with `v = e_L u`. Centrality lets the Levi action
commute past `g^s`, preserving the Levi fixedness of the preimage.
Apply the Iwahori factorization
to inverses: an element of either compact index is an upper element,
followed by a Levi element, followed by a lower element. The lower element
fixes `u`, the upper element disappears in the actual coinvariants, and
the relevant Levi invariance removes the remaining action. This first gives
`j_N(v) = j_N(u)` and then invariance under averaging to `K`.

Taking the linear map to be the actual `K ∩ M` average on the smooth
Jacquet action proves
`j_N(e_K v) = e_(K∩M) j_N(v)`.
Here `mk_averageMap_eq_leviAverage_of_stableImage` uses the published
`Jacquet.action`, `Jacquet.mk`, and `Compact.averageMap`, with the genuine
Levi index just constructed. Closedness of `M`, the upper normalizer
inclusion, and commutation of `g` with every element of `M` are explicit.
The average fixes the Jacquet class of any
`K`-fixed vector, and translation by an element of `K ∩ M` leaves the
average unchanged.

These results supply transition maps and their compatibility. They do not
prove stationarity, bijectivity of the stable-image Jacquet map, actual
parabolic contraction bases, or the exact represented-parabolic completion
theorem.
