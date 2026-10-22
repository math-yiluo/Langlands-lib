# Intrinsic Weil last-break labels and constituent extrema

The declarations are in
`Langlands.VirtualRepresentation.LocalWeil.Ramification`. The input is any
`F : PadicField.{uF} p`, with `Fact p.Prime`. The representation carrier
universe `uV` is independent of the field universe. Worker 34 implemented this
unit, following Worker 46's proposed intrinsic threshold construction and
including the fixed-space interface requested by Worker 38.

## Actual filtration and threshold construction

`upperGroup F r` is the subgroup preimage of the published
`Langlands.Ramification.Padic.absoluteUpperRamificationGroup F r` under the
actual `Langlands.Weil.Local.localProjection F`. Its ambient group is the
published `localWeilGroup F`; neither a replacement group nor a filtration is
an input. `mem_upperGroup` states precisely this preimage condition.
`upperGroup_antitone` follows from the published absolute filtration's
antitonicity. The real parameter is unrestricted here, as in that imported
filtration's extended domain.

For a genuine finite-dimensional complex representation `A`,
`upperFixedSpace F A r` is Mathlib's invariant submodule for its restriction
to this actual subgroup. `mem_upperFixedSpace` expands it to the condition
that every subgroup element fixes the vector. `IsTrivialAt F A r` says every
element of that subgroup acts by the identity linear endomorphism.

`trivialityThresholds F A` is exactly

```
{r : ℝ | 0 ≤ r ∧ ∀ w ∈ upperGroup F r, A.representation w = 1}.
```

`lastBreak F A` is its real infimum. This definition applies to all genuine
finite-dimensional representations, including reducible and rank-zero ones;
it is a **last**-break construction, not the minimum of the representation's
breaks. `isTrivialAt_mono` proves that triviality persists as the index
increases, using antitonicity. `trivialityThresholds_bddBelow` proves the
bound zero directly from membership. `lastBreak_le_of_mem` applies
conditionally complete order's infimum bound to a supplied member.

Mathlib's real infimum is a total operation: `sInf ∅ = 0`, and it is also
zero for a set unbounded below. The latter case cannot occur for these
threshold sets, because their lower bound zero is proved. Their
**nonemptiness is not proved here**. `lastBreak_eq_zero_of_thresholds_empty`
exposes the empty-set degeneracy explicitly. `lastBreak_nonneg` follows
from `Real.sInf_nonneg`, whose conclusion covers the empty set as well as
nonempty sets of nonnegative reals. Thus nonnegativity alone does not show
that the arithmetic last-break interpretation is nondegenerate.

`isTrivialAt_equiv` transports identity action through an actual invertible
linear intertwiner. One direction uses its surjectivity and the intertwining
identity, and the other uses its injectivity and the same identity.
`trivialityThresholds_equiv` gives equality of the sets by extensionality;
`lastBreak_equiv` applies `sInf` to this equality. These three invariance
lemmas allow distinct representation carrier universes `uV` and `uW`.

`classLastBreak` is a `Quotient.lift` to the published genuine
`FiniteRepresentation.IsomorphismClasses`, with compatibility supplied by
`lastBreak_equiv`. `classLastBreak_classOf` is its evaluation formula and
`classLastBreak_nonneg` follows by quotient induction. `breakLabel` composes
this map with the published `Weil.underlyingClass` on `LocalWeil.Basis F`.
That basis is precisely `Weil.IrreducibleBasis (localWeilGroup F)`, the disjoint
union of the actual continuous irreducible complex classes in positive
ranks. It is not a new label type, and the definition requires no arithmetic
certificate. `breakLabel_basisClass` is the evaluation formula on an actual
continuous irreducible representation of specified positive rank.
`breakLabel_nonneg` inherits the class-level inequality.

## Signed constituent support and extrema

`LocalWeil.Lattice F` is the existing `Weil.IrreducibleLattice` for the actual
local Weil group. Its elements are genuine finitely supported integer
coefficient functions on those Weil isomorphism classes. The definition

```
breakSupport F x = x.support.image (breakLabel F)
```

first takes the support **after cancellation within each Weil class**, and
then takes a finite set image. There is no summation of coefficients along
the numerical label map. In particular, opposite signs on distinct Weil
classes with the same label do not erase that label. The membership theorem
`mem_breakSupport` states that a label occurs exactly when some Weil class
with a nonzero coefficient has that label. Distinct Weil classes remain
distinct coefficient positions even if their restrictions to inertia are
isomorphic; there is no restriction-to-inertia quotient in this construction.
Duplicate numerical labels are recorded once as set elements, which has no
effect on extrema or universal bounds.

`breakSupport_nonempty_iff` proves that this support is nonempty exactly when
`x ≠ 0`, using nonemptiness of a finite set image and the corresponding
`Finsupp` support theorem. `breakSupport_zero` records the empty zero case.
`breakSupport_nonneg` transports `breakLabel_nonneg` through the membership
formula. These statements do not require effective coefficients or positive
total degree; arbitrary signed coefficients are allowed.

`minimumBreak F x h` and `maximumBreak F x h` use `Finset.min'` and
`Finset.max'`, respectively. Both require explicit evidence
`h : (breakSupport F x).Nonempty`. There is no numerical minimum or maximum
on zero virtual input and no value assigned to `alpha(0)` or `beta(0)`.

The predicates quantify over all surviving constituents:

- `AllBreaksAtLeast F x a`: for each `c` with `x c ≠ 0`,
  `a ≤ breakLabel F c`.
- `AllBreaksBelow F x b`: for each `c` with `x c ≠ 0`,
  `breakLabel F c < b`.
- `PositiveBreakSupport F x`: for each `c` with `x c ≠ 0`,
  `0 < breakLabel F c`.

The first two `_iff_support` lemmas rewrite these as universal inequalities
on the finite break support. For nonempty support,
`allBreaksAtLeast_iff_le_minimumBreak` gives equivalence with
`a ≤ minimumBreak F x h`, and
`allBreaksBelow_iff_maximumBreak_lt` gives equivalence with
`maximumBreak F x h < b`. The upper comparison is **strict**.
`positiveBreakSupport_iff_minimumBreak_pos` gives the analogous positivity
equivalence. The proofs use the finite minimum and maximum universal
properties; they assert inequalities of constructed labels, not identities
with fixed-space dimensions or an inflation condition.

All three predicates are vacuous on zero, as the corresponding `_zero`
lemmas prove. `allBreaksAtLeast_nonneg`, `minimumBreak_nonneg`, and
`maximumBreak_nonneg` follow from label nonnegativity.
`minimumBreak_le_maximumBreak` is the finite extrema comparison.
`pos_of_allBreaksBelow` shows that a strict all-constituent upper bound on a
**nonzero** lattice element must be positive. This last nonzero hypothesis
is essential; the zero element satisfies every upper-bound predicate.

## Original sources and exact scope

The original sources read for this unit are:

- P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes
  locales d'equations fonctionnelles de fonctions L*, Invent. Math. 64
  (1981), sections 0.4–0.6, printed pp.91–93, PDF pp.3–5. Registered source
  `deligne-henniart-1981-variation`, SHA256
  `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
- J.-P. Serre, *Local Fields*, English translation, GTM 67 (1979), Chapter IV,
  section 3, printed pp.73–75, PDF pp.80–82. Registered source
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

No source-specific errata file was present in the accessible published notes
or project notes when these passages were read.

Serre defines real lower indices using the ceiling, upper indices using the
inverse Herbrand function, and the infinite filtration using finite Galois
quotients. His Remark 1 on p.75 specifies left continuity. DH81 section 0.4
uses the same upper numbering and left endpoint convention and identifies
the nonnegative Weil filtration with the Galois filtration via its inertia
inclusion. Our actual subgroup preimage is the internal realization through
the project's published projection and absolute filtration. No additional
inertia or quotient-surjectivity theorem is asserted here.

DH81 section 0.5 defines virtual constituents by the nonzero coefficients
in the irreducible expansion in the exact Grothendieck group. Section 0.6
defines the label of a ramified irreducible by its final upper jump, assigns
zero to an unramified irreducible, and takes extrema over virtual
constituents. The threshold infimum is an **internal derived construction**
intended to realize that final jump once its arithmetic comparison is proved;
it is not a claim that DH81 explicitly gives this total-infimum definition.
The source's one-break and Swan/rank conclusions are not proved or assumed
as fields here. Likewise, the source interpretation of positive lower
thresholds by vanishing fixed vectors, and of strict upper thresholds by
inflation, requires separate comparison results. The algebraic inequalities
proved here deliberately preserve a non-strict lower bound and a strict
upper bound.

In particular, later comparison statements must rule out empty threshold
sets on the intended continuous objects, establish the one-break assertion
for Weil-irreducibles without assuming inertia-irreducibility, compare with
finite-inertia upper jumps and Swan/rank, and identify zero labels for the
intended unramified and tame objects. None of those arithmetic conclusions
is inferred from `Real.sInf_nonneg` or inserted into a construction input.

The imported `Generic`/`Local` lattice is reused unchanged. This unit does
not identify it with exact K0 or change the published split `Realization`.
The exact Jordan–Hoelder comparison is separate. There is no epsilon system,
stability theorem, arbitrary chosen inverse, supplied break function,
finite-inertia presentation, or assumed source-interpretation theorem in
any definition. All dependencies are imported by their current Lean names;
no unaccepted break or inertia-presentation draft is used.
