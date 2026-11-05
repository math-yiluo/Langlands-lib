# Actual pullbacks under affine Weil restriction

This is derived construction infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points*, Example 4.2, printed pp.9–10,
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The example invokes construction of Weil restriction using affine opens.
The preservation of cartesian squares and its comparison isomorphism here are
derived directly from the Library's all-test affine representability and
postcomposition naturality. The paper motivates this infrastructure; it does
not supply the specific Yoneda-style proof implemented below.

Let `A → B` be a commutative algebra finite and projective as an `A`-module,
in an arbitrary common universe `u`. Let `W`, `X`, `Y`, and `Z` be actual
objects of `Over (Spec B)` with affine underlying schemes and locally
finite-type structure morphisms, hence affine finite-type schemes. For
relative morphisms `i : W ⟶ X`, `j : W ⟶ Y`, `f : X ⟶ Z`, and `g : Y ⟶ Z`,
assume `IsPullback i j f g`. No immersion, field, separability, local-ring or
topological hypothesis is imposed.

`affineWeilRestrictionMap_isPullback A B i j f g h` proves that the square of
existing affine Weil-restriction coordinate morphisms is also cartesian in
`Over (Spec A)`. The principal construction,
`affineWeilRestrictionPullbackIso A B i j f g h`, is an actual isomorphism from
the constructed affine Weil restriction of `W` to the categorical pullback of
the existing morphisms associated to `f` and `g`. Its hom followed by the
first projection is the existing morphism associated to `i`, and its hom
followed by the second projection is the existing morphism associated to
`j`, as the two `hom_fst` and `hom_snd` lemmas state.

The proof uses the actual comparisons on all test schemes, with no affine
or quasi-compactness assumption on a test scheme. Functoriality of the
coordinate maps first proves commutativity of the new square. For uniqueness,
apply injectivity of the comparison for `W`, then uniqueness for the original
cartesian square; postcomposition naturality identifies its two projection
equalities with those of the new square. For existence, take compatible maps
from any test scheme into the affine Weil restrictions of `X` and `Y`.
Postcomposition naturality makes their base-changed comparisons compatible
over `Z`. The original cartesian square supplies a morphism to `W`.
Surjectivity of the comparison for `W` lifts it back to its affine Weil
restriction, and injectivity for `X` and `Y` proves the required projection
identities. Mathlib's `IsPullback.mk'` packages existence and uniqueness into
the new cartesian square; `IsPullback.isoPullback` supplies the actual
isomorphism and projection identities.

This unit supplies overlap compatibility for later gluing. It does not
construct a general nonaffine Weil restriction or assert quasi-projectivity
preservation or a local or adelic topology comparison.
