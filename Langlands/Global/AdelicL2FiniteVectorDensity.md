# Density of the `K`-finite vectors in closed invariant subspaces of `L²([G])`

Module `Langlands.Global.AdelicL2FiniteVectorDensity` defines the `K`-finite vectors of
`L²([G])` and proves that they are dense in every closed subspace invariant under the right
regular representation of `G(𝔸)`.

| Declaration | Kind | Source |
| --- | --- | --- |
| `IsCanonicalL2FiniteVector` | definition | Getz–Hahn Definition 4.4.3 with Lemma 4.4.8; §5.3 |
| `canonicalL2BoundedRightAction` | definition | internal |
| `canonicalL2BoundedRightAction_apply` | theorem (proved) | internal |
| `norm_canonicalL2RightAction` | theorem (proved) | internal |
| `continuous_canonicalL2RightAction_orbit` | theorem (proved) | internal |
| `mem_closure_finiteLevel` | theorem (proved) | Getz–Hahn Lemma 5.3.7 |
| `mem_closure_finiteVector_of_fixed` | theorem (proved) | Getz–Hahn Proposition 4.4.7 |
| `subset_closure_canonicalL2FiniteVectors` | theorem (proved) | Getz–Hahn Proposition 4.4.7, Lemma 5.3.7, Lemma 9.7.2 |

All names are in the namespace `Langlands.Global`.

## Sources

Page numbers are printed pages, with one-based PDF pages in parentheses. J. R. Getz and H. Hahn,
*An introduction to automorphic representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`:

- Definition 4.4.3, p.115 (PDF p.130): the `K`-finite vectors; Lemma 4.4.8, p.116 (PDF p.131):
  `φ` is `K`-finite exactly when its translates `π(k)φ` span a finite-dimensional space.
- Proposition 4.4.7, p.116 (PDF p.131): for a Fréchet space representation of the real group,
  the `K`-finite smooth vectors are dense.
- Lemma 5.3.7, p.141 (PDF p.156): for a Hilbert space representation of a totally disconnected
  group, the vectors fixed by some compact open subgroup are dense.
- Lemma 9.7.2 with its proof, pp.264–265 (PDF pp.276–277): for an irreducible unitary
  representation of `A_G \ G(𝔸)` the `K`-finite vectors are dense; the proof combines the two
  results above through the tensor factorization of Theorem 6.6.1.

## Definition

`L²([G])` is `Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)` and
`R = RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter hG` is the right
regular representation of `G(𝔸)` on it.

`IsCanonicalL2FiniteVector hG K w`, for a subgroup `K` of `G(𝔸)` and `w ∈ L²([G])`, says that the
vectors `R(ofInfinite k) w`, `k ∈ K_∞ = K.comap (ofInfinite F G)`, span a finite-dimensional
subspace and that some open subgroup `L` of `G(𝔸_f)` fixes `w`: `R(ofFinite l) w = w` for `l ∈ L`.
By Getz–Hahn Lemma 4.4.8 the first condition is `K_∞`-finiteness; the second is the smoothness of
Getz–Hahn §5.3 for `G(𝔸_f)`. If `K` is a maximal compact subgroup of `G(𝔸)`, it is the product of
its projections `K_∞` and `K^∞`, and `K^∞` is a compact open subgroup of `G(𝔸_f)`; a vector fixed
by an open subgroup is `K^∞`-finite and conversely, and the two actions commute, so the predicate
describes the `K`-finite vectors of Getz–Hahn for `K = K_∞ K^∞`.

## Proved results

Throughout, `G` is connected reductive (`hG`), so that the canonical measure has the properties
proved in `Langlands.Global.AdelicRestrictionSplitCentreCanonical`.

- `canonicalL2BoundedRightAction hG`: `R` as a homomorphism to bounded operators, the published
  `RestrictionSplitCentre.rationalQuotientL2BoundedRightAction` for the canonical measure;
  `canonicalL2BoundedRightAction_apply` identifies it with `R` (by definition).
- `norm_canonicalL2RightAction hG g φ`: `‖R g φ‖ = ‖φ‖`, from
  `RestrictionSplitCentre.norm_rationalQuotientL2BoundedRightAction`.
- `continuous_canonicalL2RightAction_orbit hG φ`: `g ↦ R g φ` is continuous. Proof: the published
  orbit map `RestrictionSplitCentre.rationalQuotientL2OrbitMap` for the canonical split data
  (`canonicalSubgroup_eq_imageSubgroup`, `canonical_characterRestrict_injective`, the chosen split
  component of `G`, `canonical_finiteIndex` and the right invariance of the norm-one Haar measure
  `normOneHaarRightInvariant`) is a continuous map.
- `mem_closure_finiteLevel hG hVc hVinv hφ`: if `V` is closed and invariant and `φ ∈ V`, then `φ`
  is in the closure of the vectors of `V` fixed by an open subgroup of `G(𝔸_f)`. Proof:
  `RestrictionSplitCentre.quotientL2FiniteApproximation` (for the canonical split data) gives
  compact open subgroups `K_n` of `G(𝔸_f)` and the averages `A_n` over `K_n` for their Haar
  probability measures, with `A_n φ` fixed by `K_n` and `A_n φ → φ`. Each `A_n φ` is the Bochner
  integral of the `V`-valued orbit `k ↦ R(ofFinite k) φ` for a probability measure, so it lies in
  the closed convex set `V` (`Convex.integral_mem`); `mem_closure_of_tendsto` concludes.
- `mem_closure_finiteVector_of_fixed hG hKc hVc hVinv hwV hL hLw`: for compact `K`, if `w ∈ V` is
  fixed by an open subgroup `L` of `G(𝔸_f)`, then `w` is in the closure of the `K`-finite vectors
  of `V`. Proof: let `C = K ⊓ ker(finite)`, the compact group of points of `K` with trivial finite
  component; its elements are `ofInfinite` of their archimedean parts, so they commute with
  `G(𝔸_f)` (`factors_commute`), and `ofInfinite k ∈ C` for `k ∈ K_∞`. With the Haar probability
  measure `ν` of `C` (`Langlands.Analysis.compactProbabilityHaar`), the linear map
  `T a = ∫ a(c) R(c) w dν(c)` on `C(C, ℂ)` takes values in `V` (`Convex.integral_mem`), is fixed by
  `R(ofFinite l)` for `l ∈ L` (commute `R(ofFinite l)` with the integral by
  `ContinuousLinearMap.integral_comp_comm`, then with `R(c)`), and intertwines the left regular
  action of `C` on `C(C, ℂ)` (`Langlands.CompactRepresentativeWeights.leftRegular`) with `R`
  restricted to `C` (left invariance of `ν`, `integral_mul_left_eq_self`). Hence for a weight `b`
  with finite-dimensional span of left translates (`finiteWeights`), `T b` has a
  finite-dimensional orbit under `C` (`FiniteVectors.IsFiniteVector.map`), and so under `K_∞`:
  `T b` is `K`-finite. To approximate `w` within `ε`, take a normalized nonnegative weight `a`
  supported where `‖R(c) w − w‖ < ε/2` (`CompactSmoothAverage.exists_normalized_weight`), so that
  `‖T a − w‖ ≤ ε/2` (`CompactSmoothAverage.norm_integral_average_sub_le_of_support`); then a weight
  `b ∈ finiteWeights` with `‖a − b‖ < ε / (2(‖w‖ + 1))`, given by the uniform density of
  `finiteWeights` on `C` (`AdelicGroupPoints.dense_archimedean_finiteWeights`, Stone–Weierstrass
  for the faithful archimedean matrix representation of `C`), gives `‖T a − T b‖ < ε/2`
  (`norm_integral_le_of_norm_le_const`), so `T b` is within `ε` of `w`.
- `subset_closure_canonicalL2FiniteVectors hG hKc hVc hVinv`: for a compact subgroup `K` of
  `G(𝔸)` and a closed invariant subspace `V`,
  `(V : Set _) ⊆ closure {w | w ∈ V ∧ IsCanonicalL2FiniteVector hG K w}`. Proof: by
  `mem_closure_finiteLevel` each vector of `V` is in the closure of the vectors of `V` fixed by an
  open subgroup, and each of those is in the closure of the `K`-finite vectors of `V` by
  `mem_closure_finiteVector_of_fixed` (`closure_minimal`).

Correspondence. Getz–Hahn state the density for an irreducible unitary representation and prove
it through the tensor factorization `V ≅ V_∞ ⊗ V^∞` of Theorem 6.6.1, using Proposition 4.4.7 for
`V_∞` and Lemma 5.3.7 for `V^∞`. The implemented proof needs no factorization and no
irreducibility: it averages over compact open subgroups of `G(𝔸_f)`, which commute with the
archimedean action, and then approximates within the fixed vectors by weighted archimedean
averages, as in the proof of Proposition 4.4.7, with the Peter–Weyl density of finite weights
supplied by the Stone–Weierstrass theorem. Only the compactness of `K` is used.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
