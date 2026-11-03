# Affine coordinates of diagonalizable group actions

This internal construction transports an actual automorphic action of a
diagonalizable group scheme on an affine group scheme to the natural
algebra-valued point action in `CharacterActionGrading`. It identifies the
coefficient ideal with the existing all-test fixed subgroup and, for conjugation,
with the published `torusCentralizer`. Its formal smoothness conclusion is about
the coordinate quotient. Geometric smoothness and closed representability remain
separate obligations.

For a commutative ring object `R`, an affine group scheme `G` over `Spec R`, and
an additive commutative group `M`, the acting group is the actual diagonalizable
group scheme `D(M)` from `Torus.Diagonalizable`. There is no field, characteristic,
finite generation, or torsion-free hypothesis. The formal smoothness results
assume `Algebra.FormallySmooth R (AffineCoordinates.algebra G)`. The coordinate
algebra is the chosen cogroup algebra already provided by `AffineCorepresented`.

`AffineCoordinates.coordinateSchemeIso` forgets the group structure on the
chosen coordinate comparison. Full faithfulness of relative spectrum then gives
`pointEquiv`, an equivalence between algebra maps from this coordinate algebra
to `C` and actual `Spec C` points of `G`. `pointEquiv_comp` verifies that algebra
extension corresponds to precomposition with the spectrum map.

`characterPoint` uses the diagonalizable corepresentation to turn a character
`M → Cˣ` into an actual scheme point. It preserves identity and multiplication
and is natural in `C`. The definition `ofAutomorphicAction` transports the
scheme action through these two point equivalences. The identity, associative,
and naturality laws follow from the corresponding actual action laws;
`pointEquiv_act` states the resulting compatibility explicitly.

To compare fixedness, `AutomorphicAction.isFixed_iff_affineRefinements` reduces
the all-scheme condition for an affine test to all affine algebra refinements.
For the reverse implication it uses the universal acting point on the product
of the test with the acting group. This product is affine over the affine base.
An affine spectrum comparison lets the assumed algebra-refinement condition be
applied to that universal point, and cancellation of the comparison isomorphism
recovers universal fixedness. Consequently `isFixed_iff_scheme` identifies
`CharacterAction.IsFixed` with the actual action's `IsFixed`; the quantifier over
all scheme refinements is preserved.

`schemeFixedIdeal` is the coefficient ideal of the coaction of
`ofAutomorphicAction`. Combining the comparison with the algebraic kernel
criterion gives `schemeFixedIdeal_le_ker_iff`: an algebra point kills this ideal
exactly when its actual scheme point belongs to the published fixed subgroup.
`formallySmooth_schemeFixedQuotient` applies the homogeneous-coaction
square-zero lifting theorem from `CharacterActionGrading`.

Finally, `centralizerIdeal` specializes to the published conjugation action.
The existing equality between its fixed subgroup and `torusCentralizer` yields
`centralizerIdeal_le_ker_iff`; formal smoothness of the centralizer coordinate
quotient follows from the same fixed-quotient theorem. The inclusion into `G`
need not be a closed immersion for these ideal and kernel statements.

The provenance is internal: these are adapters between existing Library
constructions, not a translation of an additional theorem in the literature.
The mathematical context is Milne, *Algebraic Groups* (2017), Theorem 13.1 and
Corollary 13.10, printed pp.254–257 / PDF pp.270–273. The retained official
errata correct the proofs of 13.4 and 13.5. This implementation uses the
alternative affine square-zero argument of `GradedFixedQuotient` and does not
use those local-ring arguments. Worker 1131's contribution to that reused
algebraic argument is retained in the submission's coauthor list.
