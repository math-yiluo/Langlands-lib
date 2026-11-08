# Completion comparison at arbitrary Iwahori factorizations

Author: Worker 1775.

This derived supporting unit extends the averaging comparison used in David
Renard, *Représentations des groupes réductifs p-adiques*, version dated
9 July 2026, VI.9.7, printed pp.205–206 / PDF pp.211–212. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The ambient group and complex representation space have independent universes.
The representation is smooth. The source compact open index `L` admits
Iwahori contractions for `(N, M, Nbar, g)` and `(Nbar, M, N, g⁻¹)`.
The target compact open `K` contains `L` and has the factorization
`K = (K ∩ Nbar)(K ∩ M)(K ∩ N)`. The element `g` commutes with every
member of `M`; this is an explicit hypothesis separate from the contractions.
Both normalizer inclusions `M ≤ normalizer N` and `M ≤ normalizer Nbar`
and closedness of `Nbar` are explicit. No contraction for `K` is needed.

`map_mk_averageMap_of_opposite_stableImage` compares a linear evaluation of
the Jacquet class before and after averaging a stable vector from `L` to `K`.
The evaluation is invariant under `K ∩ M` at that class. The opposite
contraction at `L` exhausts `Nbar` uniformly on the compact set `K ∩ Nbar`;
compactness uses closedness of `Nbar`. Choose an exponent `s` that carries
that entire set into `L` by conjugation with `g⁻ˢ`. A compression-power
preimage of the stable source vector gives a translated vector `u` fixed
by `K ∩ Nbar` and `L ∩ M`. Centrality of `g` preserves the latter fixedness.
The source vector is `e_L u`. Apply the source and target factorizations
to inverses: lower fixedness removes the rightmost factor, the upper factor
disappears in the actual coinvariants, and the Levi factor is removed by
fixedness at `L` or the assumed evaluation invariance at `K`.

`mk_averageMap_eq_leviAverage_of_opposite_stableImage` specializes the
linear evaluation to the actual `K ∩ M` average. It additionally assumes
closedness of `M`, so the genuine Levi index is compact. The Jacquet class
of the `K`-average is fixed by `K ∩ M`, and the Levi average absorbs
translations from that subgroup. Thus `j_N(e_K v) = e_(K∩M) j_N(v)`.
All these maps are the existing actual compact averages and quotient maps.

`stableCompletionJacquetComponentMap` is the actual linear map taking the
Jacquet class of a stable-family component at any ambient compact index.
`stableCompletionJacquetMap_apply_of_factor` identifies it with the component
of the previously constructed completion comparison at `K ∩ M`, for every
compact open `K` having the indicated factorization. Its additional hypotheses
are the explicit ambient and Levi cofinality inputs of that comparison.
Choose a good source `L ≤ K`, apply the averaging identity above, and use
the ambient completion equation. Thus the component formula holds even when
`K` is certified by an unrelated contracting element; only its factorization
is used. No pointwise Jacquet bijectivity is needed for this formula.

This unit does not prove any structural basis, stationarity, or pointwise
Jacquet bijectivity. In particular it is not either exact parent proposition.
