# Jacquet nonvanishing along the coarse corner

Module `Langlands.BushnellKutzko.SplitTypeJacquet.CoarseInjectivity`.

Let `F` be a nonarchimedean local field with uniformizer `ϖ`, `π` a smooth representation of
`GL ι F`, `K` a compact open subgroup equal to `J1 F blk`, `ρ` a representation of `J0 F blk`
trivial on `J1 F blk`, `aElt = aElt blk j hϖ` the coarse contraction, and write
`upperC blk j Z` for the element of `coarseN` with corner `Z`.

- `averageMap_apply_normalizing`: averaging over `K` commutes with an element normalizing `K`;
  `mem_J1_iff_conj`: elements of `J0` normalize `J1`.
- `compression_intertwines`: compression `v ↦ e_K(π(aElt) v)` (`compressionMap`) carries
  intertwiners from `ρ` to intertwiners from `ρ`. With `x = l m u` from `coarse_factor`,
  `ρ(x) = ρ(m)`, `aElt` commutes with `m`, `m` normalizes `K`, and `l`, `u ∈ K` fix compressed
  vectors.
- `eq_zero_of_compression_eq_zero` (the vanishing test): let `f` take values fixed by `J1` and
  let `ψ` be a linear map with `ψ ∘ f = id`. Assume `ψ` is invariant under `J1` on the translates
  `π(upperC Z)(f w)` for integral corners `Z`, and kills these translates when `Z` is not
  congruent to zero. If compression kills `f`, then the source of `f` is zero. Proof: the
  average of `v = f w` over the conjugate `aElt⁻¹ K aElt` vanishes (`averageMap_conj`). An
  element of this conjugate is `h · upperC Z` with `h ∈ J1` and `Z` integral, by `coarse_factor`
  and the contraction properties. Hence each point of the orbit of `v` is `v` itself (when `Z` is
  congruent to zero) or is killed by `ψ`. Applying `ψ` to the orbit mean gives `|orbit|⁻¹ w = 0`.
- `not_subsingleton_coinvariants_coarseN`: let the space `W` of `ρ` be finite-dimensional. If
  every nonzero intertwiner from `ρ` into `π` admits such a `ψ` and some intertwiner is nonzero,
  then `Jacquet.Coinvariants π (coarseN F blk j)` is not a subsingleton. This combines the two previous results with
  `not_subsingleton_coinvariants_of_compressionContraction`.
