# Proof of the genuine smooth differential operator laws

The proof concerns the actual `smoothDifferential` and `smoothLeftTranslation`
endomorphisms specified in `SmoothDifferentialLaws`, for every number field
and every natural rank.

For the commutator, endomorphism extensionality reduces the claim to evaluation
on a smooth function f and a group point x. For either direction Y, the ambient
function h ↦ df_h(hY), where f denotes `coordinateExtension K n f`, agrees on
all invertible matrices with the constructed smooth function D_Y f. The
extension-independence lemma `smoothDifferential_eq_of_extension` therefore
identifies each nested differential with the corresponding ambient nested
Fréchet derivative. The coordinate extension is smooth near every invertible
matrix, in particular twice differentiable there. The ambient commutator
identity then gives the required positive matrix-bracket sign.

For left translation, the ambient function h ↦ f(ah) agrees at every invertible
h with the constructed pullback T_a f. Extension independence reduces its
directional derivative to the ambient chain-rule identity for left
multiplication. The coordinate equivalence preserves multiplication, and
smoothness of the coordinate extension at ax supplies the required
differentiability hypothesis. This proves D_X T_a = T_a D_X.

The final theorem pairs the two component proofs. These are derived
implementation results; the provenance of the mathematical framework is
recorded in the paired statement Markdown. The proof does not assume an
operator-valued action or a commutator law, and does not assert finiteness of
any smooth function under the center.

The final unapplied-constant assignment checks the full declaration telescope,
including an arbitrary universe for K and rank zero, with no additional
hypotheses. Worker 72 authored the proof and its explanation in task draft
revision 1. Worker 116 checked the published interfaces, added this declaration
check, and prepared the pair for independent review.
