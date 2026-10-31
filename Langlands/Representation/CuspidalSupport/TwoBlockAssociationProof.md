# Two-block factor matching for associated cuspidal inductions

This module assembles the two-block case of Bernstein–Zelevinsky's matching of
composition factors for associated cuspidal data. It joins the summed Jacquet
length count of `CuspidalSupport.JacquetLengthDetector` and its bounds from
`CuspidalSupport.InducedJacquetCount` with the abstract length-two matching
criterion `LengthTwo.haveSameJordanHolderFactors_of_count_le_two` of
`Filtration.LengthTwoMatching`. The theorem
`twoBlockAssociatedCuspidalInductionFactors_of_hypotheses` proves the Library
statement `TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW}` from
three further Library statements, taken as explicit hypotheses. The final
theorem `twoBlockAssociatedCuspidalInductionFactors` discharges them with their
published proofs and proves the statement without hypotheses. The minimal
nonzero Jacquet descent and the total count of minimal conjugating permutations
are used through their published proofs `minimalNonzeroJacquet` and
`totalConjugatingCount`.

## Results

In namespace `Langlands.CuspidalSupport.JacquetLength`:

- `nontrivial_of_ne_zero g hg`: a nonzero intertwiner has a nontrivial source.
- `ne_zero_of_apply_ne_zero x hx`: an intertwiner with a nonzero value is
  nonzero.
- `nonempty_equiv_of_ne_zero hρ hσ hτ g hg g' hg'`: over a field, nonzero
  intertwiners `g : ρ → σ` and `g' : ρ → τ` between irreducible representations
  give an actual equivalence `σ ≃ τ`. By Mathlib's Schur lemma
  (`IsIrreducible.bijective_or_eq_zero`) both maps are bijective, and the
  equivalence is the inverse of the first composed with the second.
- `nonempty_equiv_of_jacquetLength_eq_one T I hX hB hC hσ hτ g hg g' hg'`: let
  a representation `X` of `GL_n` have summed Jacquet length one over a finite
  set `I` of block shapes, let `B, C ∈ I`, and let `g` and `g'` be nonzero
  intertwiners from the normalized Jacquet modules of `X` along `B` and along
  `C` to irreducible representations `σ` of the Levi of `B` and `τ` of the Levi
  of `C`. Then the normalized inductions of `σ` from `B` and of `τ` from `C` are
  equivalent. Proof: both Jacquet modules are nonzero, so each has length at
  least one. If `B ≠ C`, these two summands of the sum over `I` would give
  total length at least two, so `B = C`. Then the Jacquet module along `B` has
  length exactly one, hence is irreducible (`repLength_eq_one_iff`), and the
  previous result gives `σ ≃ τ`. Normalized parabolic induction carries this
  equivalence to the inductions (`normalizedParabolicInducedEquiv`).
- `nonempty_equiv_of_count_eq_one T I hB hC hσ hτ A S hS hAS`: inside the
  normalized induction of irreducible `σ` from `B`, let `S` be an invariant
  subspace of count one (`count T I S = 1`), and let
  `A` be an intertwiner to the normalized induction of irreducible `τ` from `C`
  that does not vanish on `S`. If `B, C ∈ I`, the two inductions are
  equivalent. Proof: the inclusion of `S` and its composite with `A` are
  nonzero intertwiners from `S` into the two inductions. The easy half of
  Frobenius reciprocity (`exists_ne_zero_normalizedJacquet_hom` of
  `CuspidalSupport.InducedJacquetEvaluation`) turns them into nonzero
  intertwiners from the Jacquet modules of `S` to `σ` and `τ`, and the previous
  result applies.
- `haveSameJordanHolderFactors_of_hypotheses T hnon hnon' hfilt hfilt' B C hassoc hB2`:
  assume `NonassociatedJacquetSubquotientsTheorem F T n` and
  `AssociatedJacquetFiltrationTheorem F T n` in both carrier universes `uV` and
  `uW`. Let `B` and `C` be block shapes of `n` with associated Levis and
  `B.length = 2`. Let `σ` on the Levi of `B` and `τ` on the Levi of `C` be
  irreducible smooth quasicuspidal representations, and let `A` and `A'` be
  nonzero intertwiners in both directions between their normalized inductions.
  Then the two inductions have the same Jordan–Hölder factors with
  multiplicities (`HaveSameJordanHolderFactors`). Proof:
  - Take `I = associatedShapes F.Carrier B`. Since Levi association is an
    equivalence relation (`LevisAssociated.refl/symm/trans`), `I` consists
    exactly of the shapes associated to `C` as well, and `C.length = 2`.
  - `jacquetLength_induced_le`, with the published `totalConjugatingCount`,
    bounds the summed Jacquet length of each induction by `2! = 2`.
  - `one_le_jacquetLength_stepQuotient`, with the published
    `minimalNonzeroJacquet`, gives length at least one on every nonzero step
    quotient, so `count T I` is strictly monotone on invariant subspaces of
    each induction (`count_strictMono`).
  - `count_bot`, the bound above, and the kernel/range additivity
    `count_top_eq_ker_add_range` supply the remaining hypotheses of
    `LengthTwo.haveSameJordanHolderFactors_of_count_le_two`.
  - The two equivalence hypotheses of that criterion come from
    `nonempty_equiv_of_count_eq_one`, applied to `A` (with `B, C ∈ I`) and to
    `A'` (with `C, B ∈ I`, then inverted).

In namespace `Langlands.CuspidalSupport`:

- `twoBlockAssociatedCuspidalInductionFactors_of_hypotheses hnon hnon' hfilt hfilt' hHom hHom'`
  proves `TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW}` under
  these hypotheses:
  - for every prime `p`, `p`-adic field `F` in universe `uF`, topological datum
    `T` and positive rank `n`, `NonassociatedJacquetSubquotientsTheorem F T n`
    and `AssociatedJacquetFiltrationTheorem F T n` in carrier universe `uV`
    (`hnon`, `hfilt`) and in carrier universe `uW` (`hnon'`, `hfilt'`);
  - `AssociatedCuspidalInductionHomTheorem.{uF, uV, uW}` (`hHom`) and
    `AssociatedCuspidalInductionHomTheorem.{uF, uW, uV}` (`hHom'`).

  Proof: given the data of the target statement, the association
  `RepresentationsAssociated B C σ τ` yields Levi association of `B` and `C`
  through its conjugating permutation. `hHom` gives a nonzero intertwiner from
  the induction of `σ` to that of `τ`. The symmetric association
  (`RepresentationsAssociated.symm`) and `hHom'` give one in the other
  direction. Cuspidal data are quasicuspidal (the second component of
  `IsLeviCuspidal`), and the previous theorem applies.
- `twoBlockAssociatedCuspidalInductionFactors` proves
  `TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW}` without
  hypotheses: for a prime `p`, a `p`-adic field `F` with topological datum `T`,
  positive rank `n`, a block shape `B` of `n` with two blocks, a block shape `C`
  of `n`, and irreducible smooth representations `σ` of the Levi of `B` and `τ`
  of the Levi of `C` that are cuspidal (`IsLeviCuspidal`) and associated
  (`RepresentationsAssociated B C σ τ`), the normalized
  parabolic inductions of `σ` and `τ` have the same Jordan–Hölder factors with
  multiplicities. Proof: apply the previous theorem to the published proofs
  `nonassociatedJacquetSubquotients` and `associatedJacquetFiltration`, which
  hold in every rank and are used in carrier universes `uV` and `uW`, and to
  `associatedCuspidalInductionHomTheorem` in the universe orders
  `{uF, uV, uW}` and `{uF, uW, uV}`.

## Provenance

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §2.16(1), printed pages 449–450, prove factor matching for associated
cuspidal data by bounding the number of composition factors through Jacquet
modules along associated Levis. Their two-block step uses nonzero maps in both
directions between the two inductions (BZ77 §2.15(2)). This module follows that
route; the counting and its interaction with maps in both directions are
packaged in `Filtration.LengthTwoMatching`. The Schur-type lemmas and the
count-one detection are internal.

The hypotheses of `twoBlockAssociatedCuspidalInductionFactors_of_hypotheses`
are Library statements, and the final theorem uses their published proofs:

- `NonassociatedJacquetSubquotientsTheorem` and
  `AssociatedJacquetFiltrationTheorem`
  (`CuspidalSupport.JacquetInductionStatement`, BZ77 corollary 2.13), proved by
  `nonassociatedJacquetSubquotients`
  (`CuspidalSupport.NonassociatedJacquetSubquotientsProof`) and
  `associatedJacquetFiltration` (`CuspidalSupport.AssociatedProof`);
- `AssociatedCuspidalInductionHomTheorem`
  (`CuspidalSupport.AssociationForwardStatement`, BZ77 theorem 2.9(a),
  (i)⇒(ii)), proved by `associatedCuspidalInductionHomTheorem`
  (`CuspidalSupport.AssociationForwardHomProof`).

Imported project constructions:

- `CuspidalSupport.JacquetLengthDetector`: `jacquetLength`, `count`,
  `subtypeMap`, `count_strictMono`, `count_bot`, `count_top`,
  `count_top_eq_ker_add_range`.
- `CuspidalSupport.InducedJacquetCount`: `associatedShapes`,
  `one_le_jacquetLength_stepQuotient`, `jacquetLength_induced_le`.
- `CuspidalSupport.InducedJacquetEvaluation`:
  `exists_ne_zero_normalizedJacquet_hom`.
- `CuspidalSupport.LeviAssociation`: `LevisAssociated.refl/symm/trans/length_eq`,
  `RepresentationsAssociated.symm`.
- `Filtration.RepresentationLength`: `repLength`, `repLength_pos_iff`,
  `repLength_eq_one_iff`.
- `Filtration.LengthTwoMatching`:
  `LengthTwo.haveSameJordanHolderFactors_of_count_le_two`.
- `Induction.Equivalences`: `normalizedParabolicInducedEquiv`.
- `CuspidalSupport.MinimalJacquetProof`: `minimalNonzeroJacquet`.
- `CuspidalSupport.TotalConjugatingCountProof`: `totalConjugatingCount`.

Authors: Worker 286 (this module up to
`twoBlockAssociatedCuspidalInductionFactors_of_hypotheses`) and Worker 241 (the
closing theorem `twoBlockAssociatedCuspidalInductionFactors`, the imported
`Filtration.LengthTwoMatching`, `CuspidalSupport.LeviAssociation` and
`CuspidalSupport.InducedJacquetEvaluation`, and the interface of the
length-two criterion).
