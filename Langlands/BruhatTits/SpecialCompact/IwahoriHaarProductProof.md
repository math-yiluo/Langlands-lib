# Proof of the Iwahori Haar-character product

Authors: Worker 103 (original proof draft), Worker 1648 (verification and submission).

This is an internal derivation of the published conditional statement from
`iwahoriRelativeIndex`, `compactOpenIndexHaar`, and Mathlib. It asserts no
additional correspondence with the literature.

The theorem `Langlands.BruhatTits.SpecialCompact.iwahoriHaarProduct` proves
`IwahoriHaarProductStatement` in every universe. It uses the supplied
simultaneous normal compact-open basis and compatible continuous
automorphisms of the three closed factors.

First, `iwahori_map` transports the unique ordered factorization through a
group automorphism. It constructs the induced equivalences on all three
literal intersection subgroups and compares the two ordered multiplication
maps. The comparison is an equality of functions, so bijectivity transports.

The lemmas `map_factor_eq` and `factor_map_comap` use compatibility with
inclusion and invertibility of the restricted automorphism. They identify
the ambient image of a factor with the same factor, and the image of a
restricted subgroup with the restriction of its ambient image.
`factor_haar_index` applies `Langlands.Haar.compactOpenIndexHaar` in a
closed factor. Closedness supplies local compactness and preserves
compactness of the restricted compact subgroup; preimages preserve
openness. Relative indices under the inclusion become the indices of the
literal intersections in `G`.

The main proof chooses a basis member `K`, then a basis member `J` inside
`K ∩ α⁻¹(K)`, and finally a basis member `H` inside `J ∩ α(J)`. Thus
`J` and `α(J)` lie in `K`, and `H` lies in both. Normality of `H` in
the fixed `K0` restricts to `K`. Since `H` is open and `K` is compact,
its relative index is finite and positive.

The theorem `iwahoriRelativeIndex` applies to `H ≤ J ≤ K` and to
`H ≤ α(J) ≤ K`. The factorization for `α(J)` follows from the transport
lemma and compatibility. The two resulting products express the ambient
indices in terms of the three factor indices. Applying the compact-open
Haar-index identity in `G` gives
`char(α) * [K:α(J)] = [K:J]`. The three factor identities give the same
equality with `char(αV) * char(αM) * char(αU)` in place of `char(α)`.
The common image index is positive, so cancellation proves the target.

Neither `J` nor `α(J)` needs to be normal in `K`. The proof supplies no
actual reductive-group basis, opposite reciprocity, torus centralization,
Cartan covering, or final rational-parabolic modulus theorem.
