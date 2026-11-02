# Irreducibility of nonadjacent two-supercuspidal products

Author: Worker 745 (task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`, with Worker
710 as first executor). The proof and its five helper modules are my own work.
Published results of other authors enter only by import; none of their code is
copied here (see "Reused published work" below).

## The theorem

```lean
theorem Langlands.Classification.twoSupercuspidalNonadjacentProductIrreducible
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T
```

It proves the unchanged Library proposition
`Langlands.Classification.TwoSupercuspidalNonadjacentProductIrreducible` of
`Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement`
and has no hypotheses beyond the outer telescope.

The proposition is the first conjunct of Zelevinsky 1980, Proposition 1.11(a)
(`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`, printed
p.175, PDF p.12). It installs `T.topology`. For all positive ranks `k`, `l` and
supercuspidal representations `ρ` of `GL_k` and `ρ'` of `GL_l`, if
`⟨l, [ρ']⟩ ≠ ⟨k, ν[ρ]⟩` and `⟨k, [ρ]⟩ ≠ ⟨l, ν[ρ']⟩` as elements of
`Σ d, SupercuspidalClass (n := d)`, where `ν[·]` is
`T.supercuspidalClassRealPowerTwist _ 1`, then
`(T.normalizedProductInductionFunctor (Shahidi.twoBlocks k l hk hl)).obj
(twoBlockFactors hk hl ρ.obj ρ'.obj)` is irreducible.

### Normalization, factor order and universes

- The product is the published upper normalized parabolic induction for the
  two-block shape `Shahidi.twoBlocks k l`: the first block, of size `k`,
  carries `ρ` and the second, of size `l`, carries `ρ'`. That is the factor
  order `ρ × ρ'` of Ze80 §1.1. The proof never replaces this object. In
  `NonadjacentTwoBlock` it writes `l = l' + 1` and works with
  `twoBlockProduct ρ ρ'`, which is definitionally the same object with the rank
  written `k + l' + 1`. The final step closes the goal through the `rfl`
  equation `twoBlockProduct = twoBlockProductRaw`, where `twoBlockProductRaw`
  is the target's object verbatim.
- The rank-indexed comparisons are kept unchanged. In particular unequal ranks
  are covered, and so are `ρ × ρ` and `ρ × ν^s ρ` with `s ≠ ±1`. The diagonal
  cases are handled by integral twist freeness, as described below.
- `uF` (the field) and `uV` (the carriers of `ρ`, `ρ'`) are independent
  universes. The product has carrier universe `max uF uV`. Exactness,
  detection and BZ77 3.8 are therefore used at `max uF uV`: in
  `GeneralLinearDerivativeExactnessStatement.{uF, max uF uV}`,
  `MirabolicDerivativeDetection.{uF, max uF uV}` and
  `MirabolicHighestDerivativePairingStatement.{uF, max uF uV, max uF uV}`. The
  Leibniz filtration and the supercuspidal derivatives are used at the factor
  universe, in `GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV}` and
  `SupercuspidalDerivatives.{uF, uV}`.
- The prime `p`, the finite extension `F` and the supplied topology `T` are
  arbitrary. The nontrivial additive character `ψ` needed for derivatives
  comes from the published `padicUnitaryAdditiveCharacterExists F T`. It is an
  internal choice, and the conclusion does not depend on it.

## The implemented proof

The Lean term is

```lean
NonadjacentAssembly.nonadjacent_of_leibnizFiltration F T
  (Derivative.generalLinearDerivativeLeibnizFiltration.{uF, uV} F T)
```

The helper modules build it as follows. Each of them has its own Markdown.

1. `NonadjacentAssembly.irreducible_of_pieces` is the BZ77 §§4.7–4.8 argument
   for an arbitrary smooth `π` of `GL_(N+1)`. Assume the top derivative is
   one-dimensional, and at every intermediate order the derivatives of `π` and
   of `ν π~` have filtrations whose graded pieces are zero or irreducible and
   pairwise carry no nonzero invariant form. Then `π` is irreducible. Proof: a
   proper nonzero `S ⊂ π` gives, by exactness of the top derivative and
   `finrank = 1`, a nonzero constituent `X ∈ {S, π/S}` with zero top
   derivative. Then `ν X~` is a quotient or subrepresentation of `ν π~` by
   smooth-dual exactness. Detection gives a highest nonzero derivative of `X`,
   of order `0 < d < N+1`. The twisted evaluation pairing `X × ν X~` is
   left-separating with covariance `|det|`. BZ77 3.8 turns it into a nonzero
   invariant form on the `d`-th derivatives of `X` and `ν X~`. By exactness
   these are subquotients of the `d`-th derivatives of `π` and `ν π~`, so the
   published length bound `length_eq_zero_of_isSubOrQuotient` makes that space
   of forms zero. This is a contradiction.
2. `NonadjacentSpecialization`: a nonzero invariant form between
   supercuspidal `A` and `ν B~` forces `[B] = ν[A]`, via the published
   `smoothInvariantPairingDuality`, closure of supercuspidality under
   contragredients and the published class laws. Also `[A] ≠ ν[A]` for positive
   rank, by the published `cuspidalIntegralTwistFreeness`.
3. `NonadjacentTwoBlock`: for `π = ρ × ρ'`, the pieces are zero or rank casts
   of `ρ`, `ρ'`. The pieces of `ν π~` are zero or rank casts of `ν ρ~`,
   `ν ρ'~`, through `ν (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~` from my published
   `ProductDualTwist.productDualTwist`. With `S = {[ρ], [ρ']}`, the two
   nonadjacency hypotheses and step 2 rule out every form between pieces.
   This proves `nonadjacent_of_twoBlockDerivativePieces`.
4. `NonadjacentLeibnizPieces`: the piece description of step 3
   (`TwoBlockDerivativePieces`) follows from the Leibniz filtration (BZ77
   4.14(c)) and BZ77 4.4. At an intermediate order `d`, the Leibniz piece at
   `(i, j)` vanishes unless `(i, j) ∈ {(0, l), (k, 0)}`, where it is `ρ` or
   `ρ'` times a one-dimensional `GL_0` representation. At the top order the
   only index is `(k, l)`, and the piece is one-dimensional. The module then
   discharges detection, BZ77 3.8, BZ77 4.4 and exactness with their published
   proofs. The result is `nonadjacent_of_leibnizFiltration`, whose only
   hypothesis is the Leibniz filtration statement.
5. This module supplies that hypothesis with the published
   `Derivative.generalLinearDerivativeLeibnizFiltration`.

`TwoSupercuspidalDerivativeBridge` identifies the published
`generalLinearDerivative T ψ (N+1) d` with restriction to the mirabolic
subgroup followed by `mirabolicDerivativeOfOrder`. The two published
constructions agree by definition. `Classification.TwoSupercuspidalBinaryProductBridge`
(my published module) relates the two-block product to the binary product
`T.binaryNormalizedProductFunctor` of the Leibniz statement.

The source route is BZ77 Theorem 4.2 (Bernstein–Zelevinsky 1977,
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, printed
pp.454–456, PDF pp.15–17), which Ze80 cites for 1.11(a). The Lean route
differs from BZ77 in two places. It needs no finite length or Jordan–Hölder
permutation, and it compares spaces of invariant forms by length bounds
instead of choosing an irreducible submodule of the highest derivative.

## Derivative inputs: proofs used

Every derivative result enters through a published, independently accepted
proof:

| Result | Published proof (Lean name, module) | Provenance |
| --- | --- | --- |
| Exactness of derivatives | `Derivative.generalLinearDerivativeExactness`, `Derivative/GeneralLinearDerivativeExactnessProof` | Worker 237, candidate `79bbad40`, task `44f58b77` |
| Detection by derivatives (BZ77 §3.5) | `Derivative.Mirabolic.derivativeDetection`, `Derivative/MirabolicDerivativeVanishing` | Worker 1024 |
| BZ77 Proposition 3.8 | `Derivative.mirabolicHighestDerivativePairing`, `Derivative/MirabolicHighestDerivativePairingProof` | Workers 1024 and 805, task `a925b519` |
| BZ77 4.4 (supercuspidal derivatives) | `Classification.supercuspidalDerivatives`, `Classification/SupercuspidalDerivativesProof` | Workers 818 and 1025, candidate `fd42c8ef`, task `2e5183b1` |
| BZ77 4.14(c) (Leibniz filtration) | `Derivative.generalLinearDerivativeLeibnizFiltration`, `Derivative/GeneralLinearDerivativeLeibnizFiltrationProof` | Workers 593 and 984, candidate `c4c5439d`, task `4e10058b` |

No derivative statement, citation, draft or pending task is a premise of the
final theorem. The helper lemmas that take these statements as arguments are
all applied to the proofs above.

## Operator conditions, condition by condition

The trusted operator's decision on request `a8463ee15d57588c8de10306748b2538`
(correspondence file
`/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md`)
admits a fully proved derivative route under five conditions.

1. *Only BZ77's general derivative theory.* The inputs are the derivative
   functors, their exactness, detection, BZ77 3.8, the Leibniz filtration
   BZ77 4.14(c) and the derivatives of supercuspidal representations BZ77 4.4,
   whose published proof goes through Whittaker multiplicity one and the
   Gelfand–Kazhdan theorem. These are general BZ77 results for arbitrary
   smooth representations or supercuspidal ones. No segment derivative
   formula (Ze80 §3.5 or §9.6) appears in the closure or in the argument.
   Theorem 4.2 itself is proved here, in the form needed.
2. *Every derivative result proved, accepted and published.* See the table
   above. Each proof listed there was independently reviewed and is in the
   Library at the base commit of this submission.
3. *Excluded tasks.* No Lean file in the import closure mentions any task ID
   of the Independence list, or any of its named declarations
   (`SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
   `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`,
   `SegmentSocleProductIrreducibility`, `GenericSegmentProductUniqueness`,
   `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
   `SquareIntegrableLanglandsClassification`,
   `SegmentSpecialEssentialSquareIntegrability`). These names occur only in
   the independence-audit sections of some imported modules' Markdown. Task
   `8e5b4563`: only its cuspidal part `SupercuspidalDerivatives` is used, and
   its proof closure contains no segment-socle module. The only segment-named
   modules it reaches are the definition modules `Classification.Segments`
   and `ConstituentRelations` described below.
4. *Reuse of the derivative infrastructure.* The proof uses the published
   functors `Derivative.generalLinearDerivative` (task `d3e94f0f`, module
   `Derivative/Iteration`), `mirabolicDerivativeOfOrder`, and `level` with
   `level_eq_iff` (task `dfae49d8`, module `Derivative/Homogeneity`). It
   defines no derivative functor of its own. The Gelfand–Kazhdan realization
   (`Smooth/Contragredient/GelfandKazhdanProof`, task `2206daa6`) enters
   through the published proof of BZ77 4.4. The missing derivative results
   were obtained from focused statement and proof tasks: exactness
   `44f58b77`, BZ77 3.8 `a925b519`, BZ77 4.4 `2e5183b1` and the Leibniz
   statement `3238f371` with its proof `4e10058b`.
5. *Audit recorded.* This section and the next.

## Import and mathematical dependency audit

The import closure of this module was computed by a recursive scan of
`import` lines over the Library and these modules. It has about 650 project
modules.

- *Lean text.* No Lean file in the closure contains an excluded task ID or
  declaration name (scan of every closure file for the 23 task-ID prefixes
  and the names above).
- *Segment-named modules.* The closure reaches `Classification.Segments` and
  `Classification.ConstituentRelations`. It reaches them through
  `CuspidalIntegralTwistFreenessStatement` (for the `CuspidalDatum` type) and
  through `Classification.SupercuspidalSupport`, a definition module of
  support relations. `ConstituentRelations` contains definitions only.
  `Segments` contains definitions (cuspidal data, segments, multisegments,
  linkage, segment products, socle/head predicates) and elementary laws:
  equivalence invariance, twist and rank arithmetic, linkage symmetry. No
  existence, Jacquet-formula, classification, exhaustion, irreducibility or
  square-integrability result is stated or proved in either module, and none
  is used here.
- *Jacquet and Whittaker modules.* The Jacquet modules in the closure are the
  general Jacquet functor, its exactness, natural Jacquet duality (through
  `Classification.SupercuspidalContragredientProof`, used for closure of
  supercuspidality under contragredients) and the statement module
  `CuspidalJacquetMultiplicityStatement` (a proposition definition, not used
  as a premise). The Whittaker modules come from the published proof of
  BZ77 4.4 (Whittaker multiplicity one, Gelfand–Kazhdan), which condition 1
  allows.
- *Mathematical dependencies.* The argument uses no product irreducibility
  criterion (Ze80 4.2 or 9.7), no analytic or square-integrability result
  (Ze80 9.3), and no classification or exhaustion theorem. It uses no
  conclusion of the Independence list, under any name. In particular, Ze80
  4.2's linked-pair converse is not used, so there is no circularity with
  §2. The Leibniz, exactness, BZ77 3.8 and BZ77 4.4 proofs each record
  their own import and independence audit in their Markdown. Their import
  closures are part of the scan above. That scan finds no excluded module in
  them; the only segment-named modules they reach are the definition modules
  listed above.

## Reused published work

Published modules are imported by Lean name, and no code of other authors is
copied into this module or its helpers. My own published modules
`Classification.TwoSupercuspidalProductDualTwist` (which adapts proofs by
Workers 264 and 6, credited there), `Filtration.InvariantBilinearSubquotientBounds`
and `Classification.TwoSupercuspidalBinaryProductBridge` are imported as
published.

## Helper modules of this proof

- `Classification.NonadjacentAssembly`
- `Classification.NonadjacentSpecialization`
- `Classification.NonadjacentTwoBlock`
- `Classification.NonadjacentLeibnizPieces`
- `Classification.TwoSupercuspidalDerivativeBridge`
