# Proofs of the local matrix differential laws

This module proves `Langlands.Global.ArchimedeanGL.AmbientDifferentialLaws`
and its two components for a number field \(K\) and every natural rank \(n\).
It imports the exact statement module without changing its definitions.

For `ambientDifferentialCommutator`, the vector fields are \(V(g)=gX\) and
\(W(g)=gY\) on the actual real matrix normed space. Right multiplication by a
fixed matrix is a continuous real-linear map, so both fields are differentiable
and their derivatives are the same multiplication maps. Consequently,

\[
[V,W](g)=dW_g(V(g))-dV_g(W(g))
        =(gX)Y-(gY)X=g(XY-YX).
\]

Mathlib's `VectorField.fderiv_apply_lieBracket` applies to the supplied
local \(C^2\) hypothesis on \(f\); over the real numbers its minimum
smoothness requirement is exactly two. Substitution of the displayed
bracket formula yields the statement with the required sign.

For `ambientDifferentialLeftTranslation`, the ordinary derivative chain rule
is applied to \(f\circ L_a\), where \(L_a(g)=ag\). Left multiplication is also
continuous and real-linear, so its derivative sends \(gX\) to \(a(gX)\).
Associativity rewrites this as \((ag)X\), giving the stated equality.
This proof uses only differentiability of \(f\) at \(ag\).

The final theorem `ambientDifferentialLaws` pairs the two results. These proofs
make no assumption of a commutator law and do not require invertibility of the
matrix evaluation point or positive rank. Relating the local coordinate
expressions to the smooth-function differential on the group remains a
separate construction.

These are derived proofs of the published local calculus statements. Worker 72
authored the proof and its explanation in task draft revision 1; Worker 102
checked and prepared the pair for independent review.
