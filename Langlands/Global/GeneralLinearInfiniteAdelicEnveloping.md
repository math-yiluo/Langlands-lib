# Actual general-linear tangent Lie and enveloping comparisons

This internal comparison retains every natural rank and arbitrary number fields.
It uses the existing identity derivative of the actual-point diffeomorphism,
`infiniteRealLieAlgebraEquiv`, without assuming a tangent identification.
The same generic smooth scalar vector-field commutator required by the actual
adelic Lie action is an explicit hypothesis throughout. The chosen atlas is
constructed from a supplied proof of algebraic smoothness in its relative
dimension, as in the existing original real differential comparison.

The bracket proof applies faithfulness of the original real smooth differential.
Every original smooth function is the image of an actual plot-smooth function.
The actual adelic Lie-action law, transported through the unchanged original
function equivalence and its derivative formula, is the original operator
commutator. The original matrix differential has the same bracket law, so
faithfulness gives bracket preservation. The resulting real Lie equivalence
has exactly the previously constructed real linear equivalence underneath.

The complex Lie equivalence uses the actual tensor scalar extension, with
pure-tensor value `z ⊗ infiniteRealLieAlgebraEquiv X`. The actual universal
enveloping algebra equivalence is induced by this Lie equivalence, and its
generator formula identifies the original matrix generator. Its restriction
identifies the actual associative enveloping centers; its underlying value is
exactly the enveloping equivalence applied to the central element.

Tensor induction and the already proved real differential comparison show that
the unchanged original smooth-function equivalence intertwines the full complex
Lie actions. Conjugation of endomorphisms by that function equivalence defines
an actual complex algebra equivalence. Extensionality on universal enveloping
generators then identifies the conjugated actual tangent action with the
original matrix action composed with the enveloping equivalence. Evaluation
proves the action formula for every enveloping element and original function.
Restricting to the actual center proves the center-action formula.

This is internal content based on the published original differential comparison,
its faithfulness helper, and `LieEnvelopingEquiv`. It retains Worker 72's original
matrix differential, smooth-function carriers and enveloping action. It proves
no generic scalar manifold commutator, exponential-curve comparison, growth,
quotient-measure or reduction-theory assertion.
