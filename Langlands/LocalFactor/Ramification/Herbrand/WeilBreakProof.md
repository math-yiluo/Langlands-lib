# Weil break labels and finite presentations

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.WeilBreakProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof` and
`Langlands.Weil.Representation.SubquotientContinuity`.

## What the module proves

Notation is as in `WeilInertiaProof`: `F : PadicField.{u} p`, `A` a finite-dimensional complex
representation of `localWeilGroup F`, `G^v = absoluteUpperRamificationGroup F v`, and the
Library notions `upperGroup`, `IsTrivialAt`, `upperFixedSpace`, `lastBreak` and `breakLabel`. For a
`FiniteInertiaPresentation P` with surjectivity `hP`, `P.representation hP` is the descended
action of the finite inertia group of `P.extension`. Its finite upper breaks
(`upperBreakSupport`, `upperBreakMultiplicities`, `maximumUpperBreak`, `minimumUpperBreak`) are
those of the Library module `Breaks`, computed with the canonical realization `T` of
`P.extension`.

Clauses of the Library module `WeilBreakStatement`:

- `presentationUpperFixedComparison F : PresentationUpperFixedComparison F`. For every
  presentation and every `r ≥ 0`,
  `upperFixedSpace F A r = inertiaUpperFixedVectors T F.Carrier (P.representation hP) r`.
- `weilLastBreakFiniteMaximum F : WeilLastBreakFiniteMaximum F`. For continuous `A` of positive
  rank and every presentation, the finite upper-break support is nonempty, and `lastBreak F A`
  is its maximum.
- `weilIrreducibleUpperBreak F : WeilIrreducibleUpperBreak F`. For continuous irreducible `A`
  and every presentation, the finite multiplicities are `Finsupp.single (lastBreak F A) A.rank`
  and the support is `{lastBreak F A}`.

The first six conjuncts of `WeilClassBreakComparison`, for basis classes of every positive rank:

- `IsBasisRepresentative F b A`, the one named definition, says that `A` has the class of
  `b : LocalWeil.Basis F`, i.e. `classOf A = underlyingClass b`.
- `classBreak_basic F b A h`. Let `A` satisfy `IsBasisRepresentative F b A`. Then:
  - the triviality thresholds of `A` are nonempty;
  - `lastBreak F A = breakLabel F b`;
  - `A.rank = b.1`;
  - for every `a > 0`, `a ≤ breakLabel F b` if and only if `upperFixedSpace F A a = ⊥`;
  - for every `c > 0`, `breakLabel F b < c` if and only if `upperFixedSpace F A c = ⊤`;
  - `breakLabel F b = 0` if and only if `A` is trivial at every positive index.

  These are the first six conjuncts of `WeilClassBreakComparison`. The last conjunct, on
  finite multiplicities, support and Swan expression, is not proved here.

Supporting results:

- `eq_of_forall_pos_lt_iff`: two nonnegative reals with the same positive strict upper bounds
  are equal.
- `rank_pos_of_irreducible`: an irreducible representation has positive rank.
- `isIrreducible_of_equiv`: an actual representation equivalence preserves irreducibility.

## Sources

- Deligne–Henniart (1981), §0.4–0.6 (registered as `deligne-henniart-1981-variation`, printed
  p. 92, PDF p. 4). The upper groups of the Weil group are those of the Galois group in
  nonnegative index, inertia acts through a finite group, and `α(V)` is the last jump of the
  filtration acting on `V`. For a ramified irreducible `V`, `V^{W(α)} = 0` and
  `V^{W(α+ε)} = V` for every `ε > 0`. An unramified `V` has `α(V) = 0` by convention, and
  `W(0)` (inertia) fixes all of `V`. Accordingly the Lean statements characterize the break
  only through positive indices: `a ≤ lastBreak` iff the fixed space at `a` is `⊥`, for
  `a > 0` only.
- Jean-Pierre Serre, *Local Fields*, GTM 67 (registered as `serre-1979-local-fields`,
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`), Chapter IV, §3,
  Proposition 14 (printed p. 74, PDF p. 81). Upper groups pass to quotients, which is what lets
  the Weil action be computed in a finite quotient.

The Library statement module `WeilBreakStatement` records these comparisons for the actual
Library objects. The supporting lemmas are internal steps.

## Proof (as implemented)

1. **Fixed spaces** (`presentationUpperFixedComparison`). Let `r ≥ 0`.
   - Take an element `k` of the finite inertia group lying in the upper group of index `r`.
     By `absoluteUpperFiniteImage` (`AbsoluteProof`) it is the restriction `r_L σ` of some
     `σ ∈ G^r`. As `r ≥ 0`, `σ` is inertial (`absoluteUpperCanonicalInertia`), so
     `σ = localProjection w` for `w = (localInertiaEquiv F).symm σ`.
   - Then `k = weilInertiaRestriction F L w`, and `P.representation hP k = A w`
     (`representation_apply`) fixes every vector of `upperFixedSpace F A r`.
   - Conversely, `w ∈ upperGroup F r` is inertial, and its restriction lies in the finite upper
     group (`absoluteUpperRamificationGroup_le_comap`). So a vector fixed by the finite group is
     fixed by `A w`.
2. **Maximum** (`weilLastBreakFiniteMaximum`). The support is nonempty by
   `upperBreakSupport_nonempty_iff`. For every `b > 0` there is a chain of equivalences:
   - `lastBreak < b` iff `A` is trivial at `b` (`lastBreak_lt_iff_isTrivialAt`, `WeilInertiaProof`);
   - iff `upperFixedSpace F A b = ⊤`;
   - iff the finite fixed space at `b` is `⊤` (step 1);
   - iff `maximumUpperBreak < b` (`maximumUpperBreak_lt_iff_fixed_eq_top`).

   Both numbers are nonnegative, so `eq_of_forall_pos_lt_iff` makes them equal. That lemma is
   proved by `le_of_forall_pos_lt_add` in both directions.
3. **Single break** (`weilIrreducibleUpperBreak`). By step 2 the maximum is `lastBreak F A`. The
   minimum equals it too:
   - if `lastBreak F A = 0`, the minimum lies between `0` and the maximum;
   - otherwise `weilIrreduciblePositiveThresholds` at `a = lastBreak F A` gives the fixed space
     `⊥`, which by step 1 and `le_minimumUpperBreak_iff_fixed_eq_bot` puts `lastBreak F A` below
     the minimum.

   So the support is `{lastBreak F A}`. The multiplicities sum to the rank
   (`sum_upperBreakSupport`) and vanish off the support.
4. **Basis classes** (`classBreak_basic`). The class of `b` is that of the chosen representative
   `Quotient.out b.2.val`, which is continuous and irreducible. `classOf_eq_iff` gives an
   equivalence from `A` to it.
   - Continuity transfers along the equivalence (`isContinuous_iff_of_equiv`).
   - Irreducibility transfers through `LinearMap.isSimpleModule_iff_of_bijective` on the
     associated modules.
   - `breakLabel F b` is by definition `classLastBreak` of the class of `b`, which is
     `lastBreak F A` (`classLastBreak_classOf`).
   - The rank is `classRank` of that class.
   - The remaining conjuncts are `weilTrivialityThresholdsNonempty`,
     `weilIrreduciblePositiveThresholds` and `weilLastBreakZero` from `WeilInertiaProof`.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
