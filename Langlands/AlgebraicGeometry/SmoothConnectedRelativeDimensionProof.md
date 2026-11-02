# Constant relative dimension for a smooth morphism with connected source

The theorem `Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension.{u}`
proves the unchanged published proposition
`Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionStatement.{u}`:

```lean
∀ (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
  Smooth f → ConnectedSpace X → ∃ n : ℕ, SmoothOfRelativeDimension n f
```

The schemes and universe are arbitrary. The proof uses Mathlib's actual smoothness
and standard-smooth-chart predicates. It adds no rank, finiteness, field,
Noetherian, separatedness, properness or target-connectedness hypothesis.
Connectedness supplies a point of the source.

## Implemented proof

The proof compares finite bases of sections of the actual relative differential
sheaf on intersections of chart opens, then applies connectedness.

1. `sectionBasis` turns a finite free trivialization of a module sheaf over an
   open `U` into a basis of its sections over every smaller open `V`. Its
   coordinate map is the family of `localBasisCoordinate` maps from
   `ModuleDualLocalFree`; the inverse sends coefficients to the finite sum of
   multiples of `localBasisSection`. The published coordinate Kronecker identity
   proves one inverse identity, and `localBasis_expansion` proves the other.
   Both maps preserve the scalar action of the section ring of `V`.
2. The imported `Langlands.Scheme.Modules.freeOverIsoOfRestrict` transports a free trivialization on the open subscheme
   to the equivalent sheaf category on the over-site. `overlapDimension` applies
   `sectionBasis` to two trivializations on their intersection. A common point
   makes the intersection nonempty and its section ring nontrivial, by Mathlib's
   scheme section-ring instance. The commutative ring therefore has invariant
   basis number; `mk_eq_mk_of_basis'` gives equality of the two finite index
   cardinalities, hence equality of the two natural-number dimensions.
3. `standardSmooth_dimension_basis` chooses a finite submersive presentation
   of a standard smooth algebra. It takes the presentation's dimension as `n`.
   The complement of the variables indexing its relations indexes
   `P.basisKaehler`. Injectivity of the relation-variable map identifies the
   cardinality of this complement with the number of variables minus the number
   of relations. Reindexing yields a basis indexed by `ULift (Fin n)`. The same
   presentation witnesses standard smoothness of relative dimension `n`.
4. `smooth_dimension_neighborhoods` uses
   `Smooth.exists_isStandardSmooth` at each source point. The algebraic
   construction in step 3 and the published
   `Langlands.Scheme.relativeDifferentialsAffineChartBasisIso` give, on the same
   chart, both standard smoothness of dimension `n` and a free trivialization
   of the restricted actual relative differential sheaf with `n` basis vectors.
5. Choose these data at every point, obtaining a function `n : X → ℕ`.
   If `y` belongs to the chosen chart of `x`, its own chart and the chart of `x`
   both contain `y`. Step 2 gives `n y = n x`; thus this function is locally
   constant. `IsLocallyConstant.apply_eq_of_preconnectedSpace` makes it constant
   on the connected source. Rewriting each chosen chart's dimension by this
   equality supplies exactly the chart data required by
   `SmoothOfRelativeDimension` for one natural number.

In particular, the conversion back to the geometric chart predicate is part of
the construction: every chosen rank and chart dimension comes from the same
submersive presentation. No converse from an assumed sheaf rank is invoked.
There is no uniqueness assertion in the theorem.

## Provenance and dependencies

This is a derived proof of the published statement, motivated by Stacks Project
Section 29.35: Lemma 29.35.11 (Tag 01V7, standard smooth neighborhoods), Lemma
29.35.12 (Tag 02G1, finite local freeness of relative differentials), and
Definition 29.35.13 (Tag 02G2, fixed relative dimension). The registered original
is `stacks-smooth-differential-rank-2026-10-22`, retained file
`literature/Stacks Project - Smooth morphisms and differential rank (HTML snapshot 2026-10-22)/01V4.html`,
source-folder SHA-256
`a20ebb3b9b37ee166cb66decf78eed5aae44e5ed93634cf911eee19d224c1bc5`,
file SHA-256
`4327b0dc32a5b7a4fc554e6587f0d622d978e306bba4d2783a8aade3704aa3da`.
The tagged passages and their proofs were read; no source-specific errata note
was found. The section is available at
[Stacks Project, Tag 01V4](https://stacks.math.columbia.edu/tag/01V4).

The section-basis, overlap, and connectedness steps are internal derived
arguments implemented here; they are not quotations of a Stacks theorem.
The proof directly reuses the published canonical affine-chart comparison and
finite coordinate expansion, and Mathlib's submersive-presentation basis,
finite basis cardinality theorem and locally constant function theorem. The
trivialization transport is shared through `Modules.FixedRankLocalBases`; basis
reindexing follows `Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank`.
It does not depend on a geometric reducedness, Picard, or downstream smoothness
proof. The published target and its imported dependency closure are unchanged.
