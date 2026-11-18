# Proof of the unequal-rank unfolding

`Langlands.Global.RankinSelbergGlobal.unequalUnfoldingStatement_proof` proves the Library
statement `Langlands.Global.RankinSelbergGlobal.UnequalUnfoldingStatement.{u}` unchanged. That
statement is the ordinary and dual unfolding of Cogdell, *Analytic theory of L-functions for
GL_n* (2004), §2.2, printed pp.205–207. It covers every number field `F : Type u` with
`CompactSpace (AdeleQuotient F)`, all ranks `t < r`, and all actual cuspidal realizations
`T` of rank `r + 1` and `T'` of rank `t + 1`. The half-plane bound `C ≥ 0` is uniform over
standard additive characters and vectors. The universe `u` and every hypothesis are kept.

## Implemented proof

The proof is one term built from published results. It adds no new mathematics.

1. `unequalUnfolding_of_whittakerGauges` (module `UnequalUnfoldingAssembly`) proves
   `UnequalUnfoldingStatement` from `UnequalPadGaugeStatement` and
   `UnequalRectGaugeStatement`. Inside it, `unequalGaugeReduction` turns the two bounds into
   the gauge premises G and G'. `unequalUnfoldingGaugeSufficiency` then applies
   `unequalUnfoldingReduction`, which needs four premises:
   - E comes from `projectionExpansionReduction` and `cuspidalWhittakerExpansionStatement_proof`.
   - E' comes from `dualProjectionExpansionReduction`, `rectangleMeasureModulus` and
     `dualCuspidalWhittakerExpansionStatement_proof`.
   - G and G' come from the gauge statement.
2. `unequalPadGauge` (module `UnequalPadGaugeProof`) proves `UnequalPadGaugeStatement`.
3. `unequalRectGauge_of_simpleRootGauge` (module `UnequalRectGaugeOfSimpleRootGauge`) proves
   `UnequalRectGaugeStatement` from two inputs:
   - `WhittakerSimpleRootMajorizationStatement`, proved by `whittakerSimpleRootMajorization`
     (module `WhittakerSimpleRootMajorization`);
   - `AdelicSimpleRootGaugeRectangularMellinStatement`, proved by
     `adelicSimpleRootGaugeRectangularMellin` (module `RectangularGaugeMellinProof`).

The theorem applies item 1 to the proof from item 2 and to the result of item 3 with its two
proved inputs. The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

Cogdell derives the ordinary and dual unfolding from the Fourier (Whittaker) expansions of the
cusp form and of its dual. He justifies the interchanges of sums and integrals by absolute
convergence for `Re(s) ≫ 0`, using the gauge estimates he cites as [22, Section 13].
The Library proof follows this route. The expansion premises E and E' give the Whittaker
expansions. The gauge premises G and G' give the absolute convergence, through the padded and
rectangular gauge bounds above.
