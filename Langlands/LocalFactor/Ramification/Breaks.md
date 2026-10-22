# Actual upper breaks of finite-inertia representations

The module `Langlands.LocalFactor.Ramification.Breaks` constructs upper-break
multiplicities, their finite support, and justified minimum and maximum breaks.
All declarations are in `Langlands.Ramification.Padic`. Worker 70 implemented
the construction and proofs; Worker 46 supplied the task's construction route
and boundary conventions. Published dependencies are imported unchanged.

## Arithmetic objects and scope

The parameters are a prime `p`, a `PadicField p` called `F`, its supplied
`TopologicalData` called `T`, and a field `K` with the actual compatible tower
`Padic p -> K -> F.Carrier`. The universes of `K`, `F.Carrier`, and the complex
representation space `V` are independent. The representation
`rho : Representation ℂ (inertia T K) V` is finite dimensional. Its group is
the kernel of the published action on the actual residue field; its lower
subgroups are `inertiaLowerGroup T K i`, obtained from the maximal-ideal-power
congruence subgroups of the actual integer ring. There is no supplied break
function or filtration and no irreducibility assumption.

For a finite Galois extension these are precisely its usual inertia and
ramification groups. As in the imported constructions, the elementary
fixed-space formulas also make sense for the automorphism group of a nonnormal
extension. They therefore need no `IsGalois` instance. This extra generality
asserts no arithmetic quotient or tower theorem. It includes every prime and
every actual finite p-adic Galois extension, without an abelian, cyclic, or
total-ramification restriction.

## Multiplicities and finiteness

Write `d(i) = inertiaFixedDimension T K rho i`, the complex dimension of the
actual subspace fixed by the `i`th lower group. The pointwise definition is

- `lowerBreakMultiplicity T K rho 0 = d(1)`;
- `lowerBreakMultiplicity T K rho i = d(i+1) - d(i)` for `i > 0`.

The subtraction is natural-number subtraction. The proved
`inertiaFixedVectors_monotone` and `inertiaFixedDimension_monotone` show that
it is the genuine nonnegative dimension increase. Invariants increase because
the lower subgroups decrease. Their dimensions never exceed `finrank ℂ V`.
If a lower group is trivial its fixed subspace is the whole space, as proved
by `inertiaFixedVectors_eq_top_of_lower_eq_bot`.

`lowerBreakMultiplicity_hasFiniteSupport` uses the already proved intrinsic
`ramificationCutoff T K`. Beyond it, every positive-index multiplicity
vanishes. The proof uses `range (cutoff+1)`, so it also handles cutoff zero
without discarding the zero coefficient. `lowerBreakMultiplicities` packages
the pointwise function using `Finsupp.ofSupportFinite`: the value is the
untruncated intrinsic function and the bound occurs only in its finiteness
proof. In particular, no caller-selected cutoff is an argument.

The telescoping identity `sum_lowerBreakMultiplicity_range` is

`sum (i < n+1) m(i) = d(n+1)`.

Its base case is `m(0)=d(1)`; the inductive step uses dimension monotonicity
to cancel the natural subtraction. `sum_lowerBreakMultiplicity_of_bound`
proves that any `b` with `G_b = 1` gives total rank when summed over `i < b+1`.
The antitone filtration makes `G_(b+1)` trivial as well. Summing over the
intrinsic support gives `sum_lowerBreakMultiplicities`.

## Genuine Herbrand reindexing

`upperBreakIndex` is the embedding `i -> herbrandPhi T K i`. Injectivity
comes from the published strict monotonicity of the actual Herbrand function.
`upperBreakMultiplicities : ℝ →₀ ℕ` applies `Finsupp.embDomain` to the lower
multiplicities; `upperBreakSupport` is its support. Thus no indices are
merged and no Swan-to-rank ratio is used as a definition.

`upperBreakMultiplicities_phi` gives the coefficient at `phi(i)` exactly.
`upperBreakMultiplicities_of_not_range` gives zero elsewhere.
`mem_upperBreakSupport_iff` identifies membership with a positive coefficient.
`upperBreakSupport_description` explicitly describes membership as either
zero with `d(1)>0`, or `phi(i)` for a positive integer with `d(i)<d(i+1)`.
`mem_upperBreakSupport_iff_of_bound` proves the same support description using
any bound `b` for which `G_b` is trivial. Together with the intrinsic pointwise
construction, this eliminates any dependence on a chosen support cutoff.
The Herbrand implementation itself is imported with its proved
`herbrandPhi_floor` identity, which also removes its auxiliary cutoff from
its value.

All support elements are nonnegative. `sum_upperBreakMultiplicities` and
`sum_upperBreakSupport` prove that their multiplicities sum to the actual
rank. Consequently `upperBreakSupport_nonempty_iff` says that the support is
nonempty exactly when `0 < finrank ℂ V`, and
`upperBreakSupport_eq_empty_iff` says it is empty exactly when the rank is
zero. There is no dummy break for a zero-dimensional space.

The zero coefficient is deliberately the entire wild-inertia-fixed space,
including tame vectors and vectors fixed by all inertia.
`upperBreakMultiplicities_of_tame` gives the single coefficient at zero when
`G_1` fixes the whole space. `upperBreakSupport_of_tame` and
`upperBreakSupport_of_trivial` give support `{0}` in positive rank. The latter
uses the explicit condition that every inertia operator is the identity.

## Left continuity and the extremum interfaces

`inertiaUpperFixedVectors T K rho r` uses the actual published
`upperRamificationGroup T K r`, regarded as a subgroup of inertia.
`inertiaUpperFixedVectors_phi` identifies its value at `phi(i)` with the
`G_i`-fixed space. `inertiaUpperFixedVectors_eq_natceil` identifies it, for
nonnegative `r`, with the lower space at `ceil(psi(r))`.

The key identity `sum_upperBreakSupport_lt`, for **positive** `r`, is

`sum (b in support, b < r) multiplicity(b) = dim V^(G^r)`.

The inequality is strict. The proof reindexes the finite sum and uses
`phi(i) < r` if and only if `i < ceil(psi(r))`, then applies the telescoping
identity. At `r=0` this formula is not asserted: the zero coefficient collects
`V^(G_1)`, while the group at zero is `G_0`, and in particular a nonzero
inertia-trivial representation already has invariants at zero.

`minimumUpperBreak` and `maximumUpperBreak` both require a proof
`h : (upperBreakSupport T K rho).Nonempty`. They are the finite set's `min'`
and `max'`. Membership, bounding, nonnegativity, and minimum-at-most-maximum
lemmas are provided, as are coefficient vanishing below the minimum and
above the maximum. The general specification lemmas are

- `le_minimumUpperBreak_iff`: `a <= minimum` exactly when every support
  element is at least `a`;
- `maximumUpperBreak_lt_iff`: `maximum < b` exactly when every support
  element is strictly less than `b`.

Their actual fixed-space forms are

- `le_minimumUpperBreak_iff_fixed_eq_bot`, for `a>0`:
  `a <= minimum` if and only if `V^(G^a) = 0`;
- `maximumUpperBreak_lt_iff_fixed_eq_top`, for `b>0`:
  `maximum < b` if and only if `V^(G^b) = V`.

The first uses that a sum of nonnegative multiplicities vanishes exactly
when none of its supported terms occurs. The second splits the total rank
sum into terms below `b` and its complement, then uses equality of subspace
and ambient dimension. These are elementary interfaces of the construction,
not an assumed one-break theorem. Minimum and maximum remain distinct for a
general representation. No arbitrary real value is assigned when support is
empty.

## Original sources and derived provenance

The explicit finite-support function, its reindexing, telescoping proof, and
linear-algebra interfaces are derived constructions, not verbatim statements
from the sources. Their correspondence is as follows.

1. Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67 (1979),
   IV.1, Lemma 1 and Proposition 1, printed pp.61–62 / PDF pp.68–69:
   the actual lower groups are defined by integer-ring congruences, decrease,
   start with inertia at zero, and eventually become trivial. These facts are
   supplied by the imported `Ramification.Galois` module.
2. Serre IV.3, printed pp.73–75 / PDF pp.80–82: real lower numbering is
   `G_u = G_ceil(u)`; `phi` and its inverse `psi` give `G^phi(u)=G_u`.
   Thus a jump from `G_i` to `G_(i+1)` occurs at `phi(i)`, including the
   right-hand side of the jump while the group at the jump retains `G_i`.
   The image of p.73 was checked independently of OCR.
3. Serre VI.2, Proposition 2 and Corollary 1', printed pp.100–101 /
   PDF pp.107–108: the conductor expression uses the dimensions of actual
   fixed subspaces. This motivates the same fixed-space inputs here; this
   module does not prove a weighted-break/conductor comparison.
4. Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des
   constantes locales d'equations fonctionnelles de fonctions L*, Invent.
   Math. 64 (1981), §§0.4–0.7, printed pp.91–93 / PDF pp.3–5:
   the upper groups are left-continuous, unramified and tame constituents
   receive zero, and the nonzero-constituent extrema are a minimum and a
   maximum. The image of printed p.92 was checked: the minimum comparison
   is non-strict, `alpha(V) >= alpha`, whereas the maximum comparison is
   strict, `beta(V) < beta`. OCR loses the lower equality stroke. The
   positive-threshold fixed-space identities above incorporate this boundary
   behavior and explicitly exclude the zero-index exception.

Registered sources, with verified fingerprints:

- `serre-1979-local-fields`:
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`;
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- `deligne-henniart-1981-variation`:
  `/home/taskhub/central-library/Deligne-Henniart--Sur la variation, par torsion, des constantes locales d'equations fonctionnelles de fonctions L--1981.pdf`;
  SHA256 `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.

The main project dependency is
`Langlands.LocalFactor.Ramification.Herbrand.Finite`, which imports the actual
inertia, lower filtration, fixed-vector spaces, and proved termination.
Mathlib supplies finite-dimensional subspace inequalities, finitely supported
functions, and nonempty finite extrema. Only the standard assumptions
`propext`, `Classical.choice`, and `Quot.sound` occur in inspection of the
main constructor.

This construction concerns an honest representation of one actual finite
inertia group. It does not construct finite-inertia presentations of Weil
representations, prove independence under changing finite quotients, or
identify an irreducible Weil representation with an irreducible inertia
representation. The one-break and Weil comparison theorems are later work.
Nor does this identify virtual Weil support with support after restriction to
inertia: distinct unramified twists can cancel after restriction. No virtual
Grothendieck-group multiplicities, extension-break notation, or full
Deligne–Henniart theorem is introduced here.
