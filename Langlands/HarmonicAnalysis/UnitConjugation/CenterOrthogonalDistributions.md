# Invariant distributions on the orthogonal of the center

The module `Langlands.HarmonicAnalysis.UnitConjugation.CenterOrthogonalDistributions` compares
conjugation-invariant distributions on `A` with those on `V = z^⊥` (the trace-form orthogonal
of the center `z`), for a finite-dimensional semisimple algebra `A` over a nonarchimedean local
field `F` of characteristic zero, and transports three inputs of Harish-Chandra's proof of
Theorem 3.1 to `V`. All declarations are in the namespace
`Langlands.HarmonicAnalysis.UnitConjugation`.

## Definitions

- `centerOrthogonalInvariant F A`: the distributions `S` on `V` with
  `S (β ∘ Ad u) = S β` for every unit `u`.
- `centerOrthogonalNilpotentInvariant F A`: those among them annihilating every test function
  that vanishes at the points of `V` lying in the closure of the nilpotent elements of `A`.

## Transfer between `A` and `V`

- `restrict_pullback_conjugation`, `extendTest_pullback_conj`: restriction and `extendTest α`
  commute with conjugation; `restrict_extendTest`: `(extendTest α β)|_V = α(0) β`.
- `isConjugationInvariant_comp_restrict`: `S ∘ restrict` is conjugation-invariant on `A`;
  `comp_extendTest_mem_centerOrthogonalInvariant`: `T ∘ extendTest α` is invariant on `V`.
- `isClosed_centerOrthogonal`, `closure_nilpotent_subset_centerOrthogonal`: `V` is closed (the
  zero set of the central component) and contains the closure of the nilpotent cone.
- `apply_eq_comp_extendTest_restrict`: if `T` is supported on the closure of the nilpotent cone
  and `α(0) = 1`, then `T f = (T ∘ extendTest α)(f|_V)`, since `f` and `extendTest α (f|_V)`
  agree on `V`.
- `conjugationSaturation_nilpotent`, `comp_restrict_mem_invariantSupportedIn`: for `S` nilpotent
  invariant on `V`, `S ∘ restrict` lies in `J(N) = invariantSupportedIn N`.
- `exists_centerBump`: the characteristic function `α` of a compact open subgroup of `z` has
  `α(0) = 1` and nonzero integral for every Haar measure.
- `orbitalDistribution_congr`: an orbital distribution at `X₀` only depends on the values of the
  test function on the orbit of `X₀`.

## The inputs on `V`

- `CenterOrthogonalVanishing.fourier` (from `LieAlgebraRegularOrbitalFourierStabilityStatement`,
  Lemma 3.16): the `D₀` of `V` is stable under the Fourier transform of `V`. For `β` in it,
  `extendTest α β ∈ D₀`; the Fourier transform on `A` for the trace form and the product Haar
  measure keeps it in `D₀`; its restriction to `V` lies in the `D₀` of `V` and equals
  `(∫ α) β̂` (`restrict_fourier_extendTest`), with `∫ α ≠ 0`.
- `centerOrthogonalNilpotentInvariant_le_span` and
  `finiteDimensional_centerOrthogonalNilpotentInvariant` (from
  `LieAlgebraNilpotentInvariantSpanStatement`, Lemma 3.3): a nilpotent invariant `S` on `V`
  gives `S ∘ restrict ∈ J(N)`, a combination of nilpotent orbital distributions; composing with
  `extendTest α` (`α(0) = 1`) returns `S`, so `S` lies in the span of the distributions
  `μ ∘ extendTest α`, `μ ∈ nilpotentOrbitals A`. The injective linear map `S ↦ S ∘ restrict`
  into the finite-dimensional `J(N)` makes the nilpotent invariant distributions on `V` a
  finite-dimensional space.
- `exists_homogeneity_degree` (from `LieAlgebraNilpotentOrbitalHomogeneityStatement`,
  Lemma 3.2): for `μ ∈ nilpotentOrbitals A` the distribution `μ ∘ extendTest α` satisfies
  `(μ ∘ extendTest α)(β_{t²}) = |t|^d (μ ∘ extendTest α)(β)` with
  `d = dim A - dim C_A(N) < dim V` when `A` is not commutative
  (`finrank_center_lt_finrank_centralizer` and `dim z + dim V = dim A`). The orbit of `N` lies
  in `V`, where `extendTest α (β_{t²})` and `(extendTest α β)_{t²}` agree.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions`, §3, printed pp. 17–30 (PDF
pp. 32–45): Lemmas 3.2, 3.3, 3.11 and 3.16.
