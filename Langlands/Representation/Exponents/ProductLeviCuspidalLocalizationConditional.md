# Product-Levi cuspidal localization from the product-Levi geometric lemma

Author: Worker 276. The intersection and proper-induction arguments originate
with Worker 954 (task `32a402c0`) and are reused through the published modules
listed below. The proof route was agreed with Worker 379, who wrote the
interface statement.

The module
`Langlands.Representation.Exponents.ProductLeviCuspidalLocalizationConditional`,
namespace `Langlands.ProductLeviCuspidalLocalization`, proves that the upper
product-Levi geometric lemma `Geometric.PadicProductLeviGeometricLemmaTheorem`
implies `Langlands.GLProductLeviCuspidalLocalizationStatement`. The
implication is conditional: this module does not prove the geometric lemma.
The geometric lemma is stated by Worker 379 in
`Langlands.Representation.Geometric.ProductLeviGeometricLemmaStatement`. It is
Bernstein–Zelevinsky's geometric lemma (BZ77, 2.12) for the group `B.Levi F`,
with its pieces indexed by the minimal representatives that lie in
`blockWeyl B`.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`. There
is no `sorry` and no new axiom.

## Main result

`productLeviCuspidalLocalization_of_geometricLemma` has type

```
PadicProductLeviGeometricLemmaTheorem.{uF, uM} →
  GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM}
```

The universe `uM` of the middle representation `σ` is the universe of the
inducing carriers in the hypothesis.

## Reversal lemmas

- The imported `Langlands.GeometricExcessBranch.reverse_reverse E` states that
  reversing a block shape twice gives `E`.
- `reverseRefinement_reverseRefinement C R`: inner reversal of a refinement
  is an involution, `reverseRefinement C (reverseRefinement C R) = R`.

## Order lemmas

- `lt_of_blockLabel_lt X h`: if the block label of `a` is smaller than that of
  `b`, then `a < b`.
- `blockPermOf_lt_of_label_lt X S τ hτ hab hlt`. Let `τ` be a family of
  permutations of the blocks of `X`, each of which reverses the order of two
  coordinates lying in different blocks of `S i`. Let `a` and `b` lie in the
  same block of `X`, with the `X.flatten S` label of `a` smaller than that of
  `b`. Then `blockPermOf X τ b < blockPermOf X τ a`.
- `reversePermutation_lt_of_label_lt` and
  `reversePermutation_symm_lt_of_label_lt`: the reversal permutation of a
  shape `E`, and its inverse, reverse the order of two coordinates in
  different blocks.
- `innerReverse_lt_of_label_lt B S` and
  `innerReverse_symm_lt_of_label_lt B S` apply the previous lemma to
  `innerReversePermutation B S` and to its inverse. Let `a` and `b` lie in one
  block of `B` and in different blocks of `B.flatten (reverseRefinement B S)`,
  respectively of `B.flatten S`. Then the permutation, respectively its
  inverse, reverses their order.

## Minimality of the localized permutation

`isMinimalRepresentative_localized F Q S R hwB hmin hw`. Put `D = B.flatten Q`
and `C = B.flatten (reverseRefinement B S)`. Let `x` be
`innerReversePermutation B S` and `y` be `innerReversePermutation D R`.
Assume:

- `w ∈ blockWeyl B`;
- `w` is a minimal representative for `(D, C)`;
- `w` conjugates the Levi of `D.flatten (reverseRefinement D R)` onto the
  Levi of `C`.

Then `x * (w * y⁻¹)` is a minimal representative for `(D, B.flatten S)`.

The proof uses `isMinimalRepresentative_iff`. That lemma states minimality as
two conditions. First, the permutation preserves the order of two coordinates
in one source block. Second, its inverse preserves the order of two
coordinates in one target block. The published lemmas
`isMinimalRepresentative_innerReverse` and `conjugatesLevi_innerReverse` say
that `x` and `y` are minimal and conjugate the corresponding Levis. Two
coordinates have the same block label after a conjugating permutation exactly
when they had the same label before
(`blockIndex_eq_iff_of_conjugatesLevi`). This lets block equalities pass
through `x`, `y` and `w`.

- Source condition. Let `a < b` lie in one block of `D`. The permutation `y⁻¹`
  lies in `blockWeyl D`, so `y⁻¹ a` and `y⁻¹ b` again lie in one block of `D`.
  - Suppose `a` and `b` lie in one block of `D.flatten R`. Then `y⁻¹`
    preserves their order. Next `w` preserves it, by the source condition for
    `w`. The images lie in one block of `C`, so `x` preserves the order.
  - Otherwise `y⁻¹` reverses the order (`innerReverse_symm_lt_of_label_lt`),
    and `w` preserves the reversed order. The two images under `w` lie in
    different blocks of `C`. Otherwise, by `hw` and the conjugation property
    of `y`, `a` and `b` would lie in one block of `D.flatten R`. Since
    `w ∈ blockWeyl B` and `D` refines `B` (`blockIndex_eq_flatten`), the
    images lie in one block of `B`. So `x` reverses the order once more
    (`innerReverse_lt_of_label_lt`), and the order of `a` and `b` is restored.
- Target condition. Let `c < d` lie in one block of `B.flatten S`. Then `x⁻¹`
  preserves their order and puts them in one block of `C`. Next `w⁻¹`
  preserves their order, by the target condition for `w`, and by `hw` it puts
  them in one block of `D.flatten (reverseRefinement D R)`. Finally `y`
  preserves their order.

## Reused intersection and proper-induction lemmas

The proof imports `Geometric.InducedOppositeCuspidalPieceConditional`, which
also imports `Exponents.GeometricExcessBranchFromUpper`, and uses their
existing declarations. The original intersection and proper-induction
arguments are due to Worker 954.

- `InducedOppositeCuspidalPiece.conjugatesLevi_flatten_of_intersections B C S w hS hR`. Assume
  `sourceLevi F B C w = refinedLevi F B S` and `sourceLevi F C B w⁻¹ = ⊤`.
  Then `ConjugatesLevi (B.flatten S) C w`. One inclusion uses
  `leviEmbedding_mem_flattenedLevi_iff` and `hS`. For the other inclusion, an
  element of the Levi of `C` lies in `sourceLevi F C B w⁻¹` by `hR`. So it is
  the conjugate of an element of the Levi of `B`, and that element lies in
  `sourceLevi F B C w = refinedLevi F B S`.
- `GeometricExcessBranch.not_isSubquotient_properInduced T hn C R hR`. This is the subquotient
  form of BZ77 2.4(d). Assume `refinedParabolic F C R ≠ ⊤`. Let `τ` be an
  irreducible representation of the Levi of `C` that is quasicuspidal along
  `C`. Then `τ` is not an actual subquotient of the normalized induction from
  `R` of any smooth representation of the refined Levi. Suppose it were. Then
  a quotient `D` of a smooth subrepresentation of the induction is equivalent
  to `τ`, and so is quasicuspidal. The published
  `CuspidalSupport.padicProperRefinedInduction` then makes `D` subsingleton.
  But `τ` is nontrivial, a contradiction.

## Localizing a whole-target piece

`localization_of_upperPiece T B Q S σ Sf hwB hmin hw ρ h`. Put
`D = B.flatten Q`, `C = B.flatten (reverseRefinement B S)` and let `x` be
`innerReversePermutation B S`. Assume:

- `w ∈ blockWeyl B`;
- `w` is a minimal representative for `(D, C)`;
- `hw` says that `w` conjugates the Levi of `D.flatten Sf` onto the Levi of
  `C`;
- `ρ ∘ leviConjugation C (B.flatten S) x` is a subquotient of the transport
  by `w` of the flattened upper normalized Jacquet module
  `T.normalizedRefinedJacquet D Sf σ`.

Then the conclusion of the target statement holds for `σ` and `ρ`.

Proof. Write `Sf = reverseRefinement D R'` with
`R' = reverseRefinement D Sf`, by the involution lemma. Let `y` be
`innerReversePermutation D R'` and put `g = x * (w * y⁻¹)`.

- `g` conjugates the Levi of `D.flatten R'` onto the Levi of `B.flatten S`, by
  `conjugatesLevi_mul` and `conjugatesLevi_inv`.
- `g` lies in `blockWeyl B`: `x` lies there (`blockPermOf_mem_blockWeyl`), `w`
  lies there, and `y ∈ blockWeyl D ≤ blockWeyl B` (`blockWeyl_flatten_le`).
- `g` is minimal by `isMinimalRepresentative_localized`.

For the representation, let `U` be the flattened upper Jacquet module of `σ`
along `reverseRefinement D R'`. By `transport_mul`, transport by `g` is
transport by `y⁻¹`, then by `w`, then by `x`. Transport by `y⁻¹` undoes
transport by `y` (`transport_inv`). The hypothesis `h`, composed with the
inverse of the Levi conjugation by `x`, says that `ρ` is a subquotient of the
transport by `x` of the transport by `w` of `U`. The published
`flattenedNormalizedOppositeReverseEquiv D R'` identifies the transport of `U`
by `y` with the flattened opposite Jacquet module of `σ` along `R'`. This
opposite Jacquet module is the target's `innerJacquet T D R' σ`. Applying
`CuspidalSupport.transportEquiv` three times and then
`IsSubquotient.of_equiv_left` finishes the proof.

## Proof of the main result

Fix the data of the target statement: `B`, `Q`, the smooth `σ` on the Levi of
`D = B.flatten Q`, a refinement `S'` of `B`, and an irreducible Levi-cuspidal
`ρ` on the Levi of `B.flatten S'`. Assume `ρ` is a subquotient of the
flattened `innerJacquet T B S' (middleInduced T B Q σ)`. Put
`C = B.flatten (reverseRefinement B S')` and let `x` be
`innerReversePermutation B S'`.

1. Apply the hypothesis to `(B, Q, reverseRefinement B S')`. This gives the
   refinements `Sf` and `Rf`, the intersection proofs, the enumeration `e` of
   `BlockMinimalRepresentatives B Q (reverseRefinement B S')`, and a gluing of
   `innerJacquetInductionFunctor T B Q (reverseRefinement B S')` from the
   geometric pieces. Let `σs` be `σ` as a smooth representation.
2. Let `ρ' = ρ ∘ leviConjugation C (B.flatten S') x`, a representation of the
   Levi of `C`. It is irreducible (`isIrreducible_comp_of_surjective`). It is
   quasicuspidal along `C`, by `isLeviQuasicuspidal_transport` applied to
   `x⁻¹` and then `transport_inv`. Here `x⁻¹` is a minimal representative for
   `(B.flatten S', C)`, because the two minimality conditions for `x` are the
   two conditions for `x⁻¹` in the other order.
3. `ρ'` is a subquotient of the representation underlying
   `(innerJacquetInductionFunctor T B Q (reverseRefinement B S')).obj σs`. By
   `flattenedNormalizedOppositeReverseEquiv B S'`, the opposite Jacquet module
   in the hypothesis is equivalent to the transport by `x` of the flattened
   upper Jacquet module of `middleInduced T B Q σ` along
   `reverseRefinement B S'`. Composing with the Levi conjugation by `x` undoes
   this transport. The resulting representation is definitionally the
   representation underlying the functor value.
4. `IsGluedFrom.exists_isSubquotient_piece` gives an index `i` such that `ρ'`
   is a subquotient of the geometric piece of `(e i).val.val`.
5. If `refinedParabolic F C (Rf (e i)) ≠ ⊤`, that piece is a normalized
   induction from `Rf (e i)`, so `GeometricExcessBranch.not_isSubquotient_properInduced` gives a
   contradiction.
6. Otherwise the refined Levi of `Rf (e i)` is everything
   (`refinedLevi_eq_top_of_refinedParabolic_eq_top`), so the target
   intersection of the piece is the whole Levi of `C`.
   `InducedOppositeCuspidalPiece.conjugatesLevi_flatten_of_intersections` then shows that `(e i).val.val`
   conjugates the Levi of `D.flatten (Sf (e i))` onto the Levi of `C`. The
   published `wholeLeviGeometricPieceEquiv` identifies the piece with the
   transport by `(e i).val.val` of the flattened upper Jacquet module of `σ`
   along `Sf (e i)`.
7. The permutation `(e i).val.val` lies in `blockWeyl B` and is a minimal
   representative for `(D, C)`. So `localization_of_upperPiece` with
   `Sf = Sf (e i)` gives the conclusion.
