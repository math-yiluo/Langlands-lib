# Upper fixed-space profiles of inertia Artin and Swan conductors

Lean module: `Langlands.LocalFactor.Ramification.InertiaConductorProfile`
(namespace `Langlands.Ramification.Padic`). Worker 4803 wrote it (Task 4803). It imports
`Langlands.LocalFactor.Ramification.Breaks`,
`Langlands.LocalFactor.Ramification.InertiaPresentationStatement`,
`Langlands.LocalFactor.Ramification.Herbrand.WeilBreakProof`,
`Langlands.Representation.Smooth.FixedVectors.OrderProof` and Mathlib's
`MeasureTheory.Integral.IntervalIntegral.Basic`.

## Main result

`inertiaConductors_eq_of_upperFixedDimension` compares two actual finite inertia
representations on the same finite-dimensional complex vector space. The two
p-adic fields may have independent universe levels `uL` and `uL'`; they share a
base field `K`. Equality of their upper fixed-space dimensions at every
nonnegative real index implies equality of both rational conductor expressions.
The precise hypotheses and conclusion are listed below under Comparison lemma.

The refinement application is exported once as
`Langlands.Ramification.Padic.finiteInertiaConductorRefinement` in
[InertiaConductorRefinementProof](InertiaConductorRefinementProof.md). That module
also proves independence of the finite-inertia presentation. This module retains
the general two-field comparison and its original profile helpers.

## Notation

In section `Profile`, `F : PadicField.{uL} p`, `T : F.TopologicalData`, and `K` is a field with
`Padic p → K → F.Carrier` a scalar tower. `G = F.Carrier ≃ₐ[K] F.Carrier`, `inertia T K` is its
inertia subgroup, and `V` is a finite-dimensional complex vector space with
`ρ : Representation ℂ (inertia T K) V`. Write:

- `g_i = lowerGroupOrder T K i`, the cardinality of the lower ramification group
  `G_i = lowerRamificationGroup T K i`;
- `φ = herbrandPhi T K` and `ψ = herbrandPsi T K`, Herbrand's functions;
- `N = ramificationCutoff T K`, the Library's chosen index with `G_i = 1` for `i ≥ N`;
- `V^(G^v) = inertiaUpperFixedVectors T K ρ v`, the vectors fixed by the upper group `G^v`
  regarded inside inertia;
- `Swan(ρ) = inertiaSwanConductor T K ρ` and `Artin(ρ) = inertiaArtinConductor T K ρ`, the
  Library's rational weighted sums `Σ_(i ≥ 1) (g_i/g_0) · codim V^(G_i)` and
  `Σ_(i ≥ 0) (g_i/g_0) · codim V^(G_i)`.

## Declarations

Auxiliary definition (internal to this proof; not a literature definition):

- `upperCodimensionProfile T K ρ v = dim V − dim V^(G^v)`, a real-valued function of the
  real variable `v`. The proof needs this function only for `v ≥ 0`.

Profile lemmas (all in section `Profile`):

- `inertiaUpperFixedVectors_monotone`: `v ↦ V^(G^v)` is monotone, because `G^v` decreases in `v`.
- `upperCodimensionProfile_antitone`, `upperCodimensionProfile_intervalIntegrable`: the profile
  is antitone, hence interval integrable on every interval.
- `herbrandPhi_natCast`: `φ(i) = (Σ_(k < i) g_(k+1)) / g_0` for natural `i`.
- `herbrandPhi_succ_sub`: `φ(i+1) − φ(i) = g_(i+1) / g_0`.
- `herbrandPhi_natCast_nonneg`: `0 ≤ φ(i)`.
- `inertiaUpperFixedVectors_of_mem_Ioc`: for `v ∈ (φ(i), φ(i+1)]`,
  `V^(G^v) = V^(G_(i+1))` (fixed vectors of the lower group `G_(i+1)` inside inertia).
- `card_inertiaLowerGroup`: the lower group `G_i`, regarded as a subgroup of inertia, has
  `g_i` elements.
- `inertiaLowerGroup_eq_bot_of_cutoff`: it is trivial for `i ≥ N`.
- `inertiaSwanConductor_eq_sum_rat`, `inertiaSwanConductor_eq_sum`: in `ℚ` and in `ℝ`,
  `Swan(ρ) = Σ_(i < N) (g_(i+1)/g_0) · (dim V − dim V^(G_(i+1)))`.
- `integral_upperCodimensionProfile_piece`: the integral of the profile over
  `[φ(i), φ(i+1)]` is `(g_(i+1)/g_0) · (dim V − dim V^(G_(i+1)))`.
- `upperCodimensionProfile_eq_zero`: the profile vanishes for `v > φ(N)`.
- `inertiaSwanConductor_eq_integral`: for every real `B ≥ φ(N)`,
  `Swan(ρ) = ∫_0^B (dim V − dim V^(G^v)) dv` (cast to `ℝ`).
- `fixedCodimension_top_eq_profile_zero`: the tame term `codim V^(inertia)` equals the profile
  at `0`.
- `inertiaArtinConductor_eq_integral`: for every real `B ≥ φ(N)`,
  `Artin(ρ) = (dim V − dim V^(G^0)) + ∫_0^B (dim V − dim V^(G^v)) dv`.

Comparison lemma (section `Refinement`):

- `inertiaConductors_eq_of_upperFixedDimension`: let `F : PadicField.{uL} p` and
  `F' : PadicField.{uL'} p` carry topological data `T` and `T'`, let `K` be a common base field
  for both, and let `ρ`, `ρ'` be complex representations of `inertia T K` and `inertia T' K` on
  the same finite-dimensional space `V`. If `dim V^(G^v)` computed from `ρ` equals that computed
  from `ρ'` for every real `v ≥ 0`, then `Artin(ρ') = Artin(ρ)` and `Swan(ρ') = Swan(ρ)`.

## Implemented proof

1. Swan sum as a finite sum. `inertiaSwanConductor` is by definition
   `Ramification.swanConductor T.Integers (inertia T K) ρ` for the restricted integer action
   `inertiaIntegerAction T K`. The proof installs that action and reproves locally the three
   instances the definition uses (faithfulness, Noetherianity of `T.Integers`, finiteness of
   `G`), with the same proofs as in the Library module `Galois`, whose versions are private.
   `Ramification.swanConductor_eq_sum_range`, with the termination bound `N`
   (`lowerRamificationGroup_eq_bot_of_cutoff`), turns the sum into a sum over `i < N`. The lower
   group of the abstract filtration for this action is, by definition, `inertiaLowerGroup T K i`,
   whose cardinality is `g_i` via `Subgroup.subgroupOfEquivOfLe` (`G_i ≤ G_0 = inertia`,
   `lowerRamificationGroup_zero`, `lowerRamificationGroup_antitone`).
2. Pieces. On `(φ(i), φ(i+1))` the upper fixed space is `V^(G_(i+1))`:
   `inertiaUpperFixedVectors_eq_natceil` (Library module `Breaks`) gives
   `V^(G^v) = V^(G_⌈ψ(v)⌉)` for `v ≥ 0`, and `ψ(v) ∈ (i, i+1]` by strict monotonicity of `ψ` and
   `ψ ∘ φ = id` (`herbrandPsi_strictMono`, `herbrandPsi_herbrandPhi`). So the profile is
   constant there and its integral is the constant times `φ(i+1) − φ(i) = g_(i+1)/g_0`, which
   `herbrandPhi_floor` (Library module `Herbrand.Finite`) gives at natural arguments
   (`intervalIntegral.integral_congr_Ioo_of_le`, `intervalIntegral.integral_const`).
3. Tail. For `v > φ(N)`, `⌈ψ(v)⌉ ≥ N`, so `G_⌈ψ(v)⌉ = 1`, the fixed space is everything
   (`inertiaFixedVectors_eq_top_of_lower_eq_bot`) and the profile vanishes; the integral over
   `[φ(N), B]` is `0`.
4. Assembly. `intervalIntegral.sum_integral_adjacent_intervals` over the points `φ(0) = 0,
   φ(1), …, φ(N)` and `intervalIntegral.integral_add_adjacent_intervals` with the tail give
   `inertiaSwanConductor_eq_integral`. `inertiaArtinConductor_eq_tame_add_swan` (Library module
   `Galois`) splits the Artin sum into the tame term and Swan; the tame term is the profile at
   `0` because `G^0 = inertia` (`upperRamificationGroup_zero`), giving
   `inertiaArtinConductor_eq_integral`.
5. Comparison. Take `B = max(φ_T(N_T), φ_T'(N_T'))`. The two profiles agree on `[0, B]`
   by hypothesis, so their integrals agree (`intervalIntegral.integral_congr`), and so do their
   values at `0`. By step 4 the real casts of the two Swan and the two Artin expressions agree,
   and `Rat.cast_injective` gives equality in `ℚ`.
6. Refinement application (exported by `InertiaConductorRefinementProof`).
   `P.artinConductor hP` is by definition
   `inertiaArtinConductor T F.Carrier (P.representation hP)` with
   `T = (absoluteFiniteExtension F P.extension).canonicalTopologicalData`, and likewise for
   Swan and for `P.refine M h`, whose field is `M`. The Library theorem
   `HerbrandBridge.presentationUpperFixedComparison` (module `Herbrand.WeilBreakProof`), applied
   to `P` and to `P.refine M h`, identifies both upper fixed spaces at every `v ≥ 0` with the
   presentation-free space `upperFixedSpace F A v`. Their dimensions therefore agree, and step 5
   with `K = F.Carrier` gives the two equalities.

The general comparison uses equality of fixed-space dimensions as its hypothesis.
The refinement application uses `presentationUpperFixedComparison` for the absolute
upper filtration; it does not use Herbrand's quotient theorem or `representation_refine` directly.

## Sources

Serre, *Local Fields* (1979), registered as `serre-1979-local-fields`:

- IV §3, printed pp. 73–75: Herbrand's function `φ(u) = ∫_0^u dt/(G_0 : G_t)`, its
  piecewise-linear form and the upper numbering `G^v = G_ψ(v)`.
- VI §2, Proposition 2 and Corollary 1', printed pp. 100–101: the weighted fixed-space formula
  for the Artin conductor, which is the Library definition of the two sums.
- VI §2, Proposition 3 and its Corollary, printed p. 101: invariance of the conductor under
  inflation from a quotient. The main theorem is an inertia-level form of this Corollary; the
  Lean proof follows the upper-numbering route instead (Exercise 1(a), printed p. 103, expresses
  the Artin character through the upper groups).
