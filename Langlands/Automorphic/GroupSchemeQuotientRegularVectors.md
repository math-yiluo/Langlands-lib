# Nonzero vectors with regular continuous representatives in closed invariant subspaces

Module `Langlands.Automorphic.GroupSchemeQuotientRegularVectors`. For an affine group scheme
`G` of finite type over a number field `F`, the module works with the positive-central rational
quotient `Q` with its measure `μQ`, and the right action `ρ = haarQuotientL2BoundedRightAction`
on `L²(Q, μQ)`. In a closed `ρ`-invariant subspace `A` it produces nonzero vectors whose
continuous representatives satisfy a mass bound and are invariant under a compact open subgroup
of the finite adelic points.

## Definitions

- `IsFiniteInvariant F G T i h L`: `h(q · l) = h(q)` for every `l` in the subgroup `L` of the
  finite adelic points `FiniteAdelicGroupPoints F G`, acting through
  `AdelicGroupPoints.ofFinite`.
- `IsRegularVector F G T i hi I e hc A L u`: `u ∈ A`, `u ≠ 0`, and `u` has a continuous
  representative `h` such that `QuotientMassBound … h S C` holds for some compact `S` and `C ≥ 0`
  and `IsFiniteInvariant … h L` holds.
- `levelParameter F G K`: a subgroup `K` of the finite adelic points, mapped continuously into
  `G(𝔸_F)`.

## Results

- `weightedQuotientOrbitIntegral_rightTranslate_of_commute` and
  `IsFiniteInvariant.weightedQuotientOrbitIntegral`: a weighted orbit integral along parameters
  that commute with a translation `g` is invariant under `g` whenever the integrated function
  is.
- `isFiniteInvariant_levelAverage`: averaging a continuous function over a compact subgroup
  `K` with a left invariant measure gives a `K`-invariant function. This is the substitution
  `k ↦ l k`.
- `orbit_near_mem_nhds`: the set of `g` with `‖ρ(g)φ - φ‖ < ε` is a neighbourhood of the
  identity, by continuity of orbits (`haarQuotientL2OrbitMap`).
- `exists_isRegularVector_convolution`: this theorem takes
  `GroupSchemeQuotientL2ContinuousRepresentativeStatement` as a hypothesis. Under it, a closed
  invariant `A` that contains a nonzero vector `x₀` contains a regular vector invariant under
  the trivial subgroup. Take a normalized bump `f` (`exists_normalized_bump`) supported where
  `‖ρ(g) x₀ - x₀‖ < ‖x₀‖ / 2`. The convolution `haarQuotientL2IntegratedAction … f x₀` lies in
  `A` (`integral_mem_of_isClosed`). It is nonzero (`integral_smul_ne_zero`). It has a
  mass-bounded continuous representative by `exists_quotientMassBound_representative`.
- `isRegularVector_levelAverage`: let `u` be a regular vector and let `K` be a compact subgroup
  of the finite adelic points on which `‖ρ(k) u - u‖ ≤ ‖u‖ / 2`. Then the probability Haar
  average `∫_K ρ(k) u dk` is a regular vector invariant under `K`. Its continuous representative
  is the corresponding weighted orbit integral. The Library's
  `groupSchemeQuotientL2IntegratedRepresentative` identifies its class, and
  `quotientMassBound_weightedQuotientOrbitIntegral` gives the mass bound.
- `exists_isRegularVector_level`: every regular vector yields a regular vector invariant under
  some compact open subgroup. Compact open subgroups form a neighbourhood basis of the identity
  by `finiteAdelicGroupCompactOpenBasis`.

## Provenance

These are internal steps of the Library's construction of nonzero forms attached to an
irreducible cuspidal summand, in `Langlands.Automorphic.GeneralLinearSummandFormsNonzero`. That
construction proves the Library's single-summand density consequence of Lemma 9.7.2 and (9.40)
in the proof of Theorem 9.7.3 of Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), printed pp. 264–266 (PDF pp. 276–278). The book works with `K`-finite
vectors and recovers each of them by a compact convolution (Lemma 9.7.2). It does not use
regular vectors. Here a vector of a cuspidal summand is replaced by convolutions that have
continuous, finite-level representatives with a conjugate mass bound. The module does not prove
the continuous-representative statement; `exists_isRegularVector_convolution` assumes it.
