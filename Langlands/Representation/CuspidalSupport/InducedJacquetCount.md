# Summed Jacquet lengths of quasicuspidal inductions

This internal module proves the two bounds on the summed Jacquet length
`jacquetLength T I` of `CuspidalSupport.JacquetLengthDetector` that the
two-block factor-matching proof needs, for the actual normalized parabolic
induction `T.normalizedParabolicInduced B σ` of smooth quasicuspidal data `σ`
on a block shape `B`. Four Library theorem statements enter as explicit
hypotheses of the bounds; nothing here assumes them otherwise.

## Definitions

- `associatedShapes F B`: the finite set of block shapes `C` with
  `LevisAssociated B C`. It is the `Finset` of the set
  `{C | LevisAssociated B C}`, finite because the type of block shapes is finite
  (`finiteBlockShape`). `mem_associatedShapes` states membership.
- `compSubrepresentationOrderIso ρ f hf`: for a surjective monoid homomorphism
  `f : H →* G`, the order isomorphism between the invariant subspaces of `ρ` and
  of `ρ.comp f`; both have the same underlying submodule.

## Results

- `isIrreducible_comp f hf`: composition with a surjective monoid homomorphism
  preserves irreducibility (through `OrderIso.isSimpleOrder_iff` and the order
  isomorphism above).
- `isIrreducible_of_equiv e`: an equivalence `e : ρ.Equiv σ` of representations
  carries irreducibility of `ρ` to `σ`. It turns `e` into a bijective linear map
  of the associated modules (`equivLinearMapAsModule`) and applies
  `LinearMap.isSimpleModule_iff_of_bijective`. The Library's
  `Langlands.isIrreducible_iff_of_equiv` (in
  `Classification.SupercuspidalContragredientAux`) proves the same for complex
  coefficients and groups; this version, for any field and monoid, avoids
  importing that classification module.
- `isIrreducible_transport w hw`: the Weyl transport `transport B C w hw ρ`,
  which is `ρ.comp (leviConjugation B C w hw).symm.toMonoidHom`, of an
  irreducible representation is irreducible.
- `one_le_jacquetLength_of_isSubquotient hmin hnon B I hI`: assume
  `hmin : MinimalNonzeroJacquetTheorem`,
  `hnon : NonassociatedJacquetSubquotientsTheorem F T n`, and that `I` contains
  every shape associated to `B`. Then every nontrivial smooth subquotient `Q` of
  `(T.normalizedParabolicInductionFunctor B).obj σ`, for quasicuspidal `σ`, has
  `1 ≤ jacquetLength T I Q.representation`. Proof: `hmin` gives a shape `C`
  whose normalized Jacquet module of `Q` is nonzero and quasicuspidal. If `C`
  is associated to `B`, then `C ∈ I` and the summand at `C` has positive length
  (`repLength_pos_iff`). Otherwise the published
  `normalizedJacquetSubquotient` makes the Jacquet module of `Q` a subquotient
  of that of the induction, and `hnon` forces it to be zero, a contradiction.
- `one_le_jacquetLength_stepQuotient`: the same bound for every nontrivial step
  quotient `stepQuotient S S'`, `S ≤ S'`, of invariant subspaces of the raw
  induced representation. The step quotient is a smooth subquotient
  (`SmoothRep.isSubquotient_iff_exists`, with the inclusion of `S'` and the
  quotient map), so the previous result applies.
- `jacquetLength_induced_le hfilt hcount B I hI`: assume
  `hfilt : AssociatedJacquetFiltrationTheorem F T n`,
  `hcount : TotalConjugatingCountTheorem`, and that every shape of `I` is
  associated to `B`. For irreducible quasicuspidal `σ`,
  `jacquetLength T I (T.normalizedParabolicInduced B σ.representation) ≤ B.length!`.
  Proof: for `C ∈ I`, `hfilt` gives a filtration of the Jacquet module with `r`
  steps, `r` in bijection with the minimal conjugating permutations from `B` to
  `C`, whose graded pieces are equivalent to Weyl transports of `σ`, hence
  irreducible; so the Jacquet module has length `r`
  (`repLength_eq_of_hasSimpleFactors`). Summing over `I` gives the cardinality
  of the part over `I` of the sigma type of `hcount`, which is at most the full
  cardinality `B.length!`.

## Provenance

Internal. Bernstein–Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), §2.16(1), printed pages 449–450, bound the number of
composition factors of a quasicuspidal induction by the lengths of its Jacquet
modules along associated Levis; this module isolates the positivity and the
upper bound of that count. The hypotheses are the Library statements
`MinimalNonzeroJacquetTheorem` (`CuspidalSupport.MinimalJacquetStatement`),
`NonassociatedJacquetSubquotientsTheorem` and
`AssociatedJacquetFiltrationTheorem` (`CuspidalSupport.JacquetInductionStatement`,
BZ77 corollary 2.13), and `TotalConjugatingCountTheorem`
(`CuspidalSupport.TotalConjugatingCountStatement`, BZ77 2.8).

Imported project constructions:

- `CuspidalSupport.JacquetLengthDetector`: `jacquetLength`, `stepQuotient`,
  `subtypeMap`.
- `CuspidalSupport.JacquetSubquotientProof`: `normalizedJacquetSubquotient`.
- `CuspidalSupport.FiniteBlockShapes`: finiteness of block shapes.

Author: Worker 286.
