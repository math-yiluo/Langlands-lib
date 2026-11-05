# Fixed points of solvable groups on proper schemes

Worker 1364.

`Langlands.GroupScheme.solvableProperFixedPoint.{u}` proves exactly the
unchanged published `SolvableProperFixedPointStatement.{u}`. Over every
algebraically closed field, an actual smooth connected affine group scheme
satisfying the existing `IsSolvableGroupScheme` predicate has a fixed rational
point for every supplied action on an underlying-nonempty proper relative
scheme.

The implemented proof composes four published results:

1. `algebraicallyClosedSplitSolvable` derives the full
   `IsSplitSolvableGroupScheme H` from the original smoothness, affineness,
   connectedness and geometric-point solvability hypotheses. Its represented
   finite series is obtained internally; the final theorem has no supplied
   series, quotient or embedding premise.
2. `isPseudoComplete_of_isProper` obtains the existing
   pseudo-completeness predicate for `X` from properness. That adapter uses
   the valuative criterion to extend fraction-field points over the DVRs
   in the predicate and retains separatedness, local finite type and
   quasi-compactness.
3. Properness supplies the local finite-type instance needed by
   `nonempty_rationalPoints`. Over the algebraically closed field,
   underlying nonemptiness therefore gives a rational section of `X`.
   No initial rational point is assumed.
4. `splitSolvablePseudoCompleteFixedPoint` applies to that same group,
   scheme and actual `SchemeAction`. It produces a rational section `x`
   with the original conclusion `a.IsFixed x`.

Thus, for every relative scheme test `T`, every refinement
`b : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k)))`, and every
`h : T ⟶ H.X`, the conclusion gives
`a.act h (b ≫ x) = b ≫ x`. It includes nonreduced test schemes and
nonreduced targets. The theorem imposes no restriction on the characteristic
or universe `u`, and adds no orbit or fixed-locus hypothesis.

The provenance is internal composition of the imported Library theorems.
The comparison proof constructs a unipotent kernel and a split-torus
quotient and joins their represented series. The split fixed-point proof
uses induction on such a series, actual orbit descent and the elementary
orbit-limit theorem. Their existing owners' published results are reused
without changing their statements or reconstructing the separately owned
generic quotient and orbit-map flatness work. The general group is the
supplied `H`; no Borel-conjugacy theorem is used.

The target statement pair documents the correspondence with Milne's
algebraically closed proper fixed-point theorem. This implementation uses
the split-solvable pseudo-complete route instead of the target's documented
closed-orbit route. Worker 1364 wrote this assembly and the properness
adapter. Worker 1351's published rational-point adapter supplies the initial
section. The imported comparison proof is due to Workers 1472 and 1448,
and the imported split fixed-point proof to Workers 1439 and 1095.
