# Positive-rank assembly of actual Aubert induction commutation

Author: Worker 76.

This supporting module constructs the actual source-refinement contributions
and proves the positive-rank commutation identity from two explicit inputs:
the geometric Grothendieck formula and the comparison of each actual geometric
piece after ordinary induction. It does not itself supply either input, prove
rank zero, or establish the unconditional all-rank target.

`refinementInductionJacquetK0 F T B S` is the integer-linear map from the full
exact finite-length Grothendieck group of the actual product Levi of `B` to
that of `GL_n(F)`. It first applies normalized refined Jacquet restriction for
`S`, then normalized refined induction, then ordinary normalized induction
from `B`. All three are the existing actual exact-category maps. The definition
retains independent field and representation universes and saturated carriers.

`inductionCommutation_positive_of_piece_comparison` takes the existing
`GeometricLemmaGrothendieckStatement F T`, a positive rank, a source shape `B`,
and an explicit comparison for every target shape `C`, minimal representative
`w`, actual intersection refinements `S` and `R`, and virtual class `x`. That
comparison says that ordinary induction from `C` of the actual geometric-piece
class equals `refinementInductionJacquetK0 F T B S x`. Only the actual source
and target Levi intersection equalities are required for this comparison;
the other intersection conditions are supplied by the geometric formula.

The proof compares the two integer-linear maps on finite-length object classes
using `FiniteLengthGrothendieckGroup.hom_ext_object`. The geometric formula
chooses intersection refinements and a finite enumeration of the minimal
representatives uniformly before the input object. The actual piece-map
generator formula converts each representation class in that enumeration to
the value of `geometricPieceK0`. Reindexing through the supplied equivalence
expresses the normalized Jacquet-after-induction map as a sum over every minimal
representative.

Ordinary induction distributes over that finite sum. The explicit piece
comparison then replaces every induced piece by its actual source-refinement
contribution. `refinementSignedSum_eq_refinement_sum` regroups the ambient
signs `(-1)^(n - C.length)` into the intrinsic product-Levi signs
`(-1)^(sum i, (B.size i - (S i).length))`. Linearity identifies the resulting
sum with ordinary induction after the existing product-Levi alternating
operator. Generator extensionality is used on the existing exact quotient,
so all actual short exact relations, including nonsplit ones, are retained.

The provenance is an internal derivation from the published exact
Grothendieck-map constructions and geometric-formula statement, together with
the source-refinement coefficient and finite-regrouping helpers. No original
literature statement is newly transcribed here. No classification, Aubert
involutivity or irreducible-image conclusion enters the proof. The explicit
piece-comparison premise remains an obligation of the final unconditional
commutation proof.
