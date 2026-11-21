# Bounds for candidate approximations of a pure stratum

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, the termination argument after (2.4.6) in the proof of (2.4.1)(i), printed pp. 69–70 (PDF pp. 81–82). There the source uses that "the denominators `e(𝔄_m)` are bounded above", together with compactness, to stop an iteration with `r_m / e(𝔄_m)` strictly decreasing. `CandidateDepthBoundStatement` packages the two facts that let such a choice be made by a minimum instead, in the Library's chain model. This is a derived result, not a numbered statement of the source.

## Statement

`CandidateDepthBoundStatement` is a closed proposition over every nonarchimedean local field `F` and finite-dimensional `F`-space `V`. It asserts two things.

1. Every `𝒪[F]`-lattice chain on `V` has period at most `dim_F V`.
2. Let `S` be a pure stratum with element `β`. There is an integer `m` such that every pure stratum `T` satisfies `m · e(T) ≤ T.r` whenever `β ∈ T.coset` and `[F[T.b]:F] < [F[β]:F]`. Here `e(T)` is the period of `T.chain`, so `m` bounds the normalized depths `T.r / e(T)` of such candidates from below.

Together, the normalized depths of candidates lie in `(1/(dim V)!) ℤ` and are bounded below. So whenever at least one pure `T` satisfies the coset and strict degree conditions, a least normalized depth among such `T` exists. The statement itself allows the set of candidates to be empty, and then asserts nothing about them. For example, if `[F[β]:F] = 1` no pure `T` has smaller degree. In the source, the existence of a starting candidate in the critical-level, maximal-field case is the separate step (2.4.3), printed p. 67.

## Implemented proof

`period_le_finrank` transports the chain to coordinates along `(Module.finBasis F V).equivFun` with `LatticeChain.linearEquivMap`. This transport preserves the period. The Library's `LatticeChain.period_le_card` then applies.

For the depth bound, fix a uniformizer `π` and put `a = |S.n|`. By `elementAlgebra_smul`, `F[π^a β] = F[β]` is a field. `boundedApproximation_aux` for `π^a β` gives an integer `M`. Let `T` be a candidate. Since `β` lies in the cosets of both pure strata, `pureCosetSlope` gives `S.n · e(T) = T.n · e(S)`, hence `T.n ≤ a · e(T)`. The element `T.b` has valuation at least `−T.n`, so it lies in `𝔓_T^{−T.n}` (`mem_endFiltration_of_le_valuation`). So does `β = T.b + (β − T.b)`, using `T.r < T.n`. Multiplying by `π^a` moves both into the order of `T.chain`. Let `t` be the integer part of `(a·e(T) − T.r)/e(T)`. Then `π^{−t}(π^a β − π^a T.b) = π^{a−t}(β − T.b)` lies in the order, since `β − T.b ∈ 𝔓_T^{−T.r}` and `t·e(T) ≤ a·e(T) − T.r`. Scalar multiples have the same degree (`elementDegree_smul`), so the bound gives `t ≤ M`. Division with remainder then gives `(a − M − 1) · e(T) ≤ T.r`. The proof uses neither compactness nor conjugation.
