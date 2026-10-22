# Local calculus statements for the archimedean differential

Let \(K\) be a number field and let \(n\) be any natural number, including zero.
Write \(A=\operatorname{ArchimedeanMatrix}(K,n)\), the published real normed
algebra of matrices over the mixed real and complex archimedean coordinates.
Functions in this file have domain the entire ambient matrix space and values
in \(\mathbb C\); all derivatives are real Fréchet derivatives.

For explanation, put \(D_Xf(g)=df_g(gX)\). This notation refers to the explicit
derivative expressions in Lean, rather than an additional bundled operator.
`AmbientDifferentialCommutator K n` states that, for every \(f:A\to\mathbb C\)
that is \(C^2\) at \(g\), and for all \(X,Y\in A\),

\[
D_{XY-YX}f(g)=D_X(D_Yf)(g)-D_Y(D_Xf)(g).
\]

The order and sign are those of the left-invariant vector fields \(g\mapsto gX\).
They agree with differentiating the published right translations
\(R(h)f(g)=f(gh)\). The hypothesis is local \(C^2\) regularity at \(g\), not
global smoothness on all matrices. Thus the statement is suitable for a
coordinate expression of a smooth function on the open set of invertible
matrices.

`AmbientDifferentialLeftTranslation K n` states that, for every \(a,X,g\in A\)
and every \(f\) differentiable at \(ag\),

\[
D_X(f\circ L_a)(g)=D_Xf(ag),\qquad L_a(h)=ah.
\]

This is the chain rule and associativity, since
\(dL_a(gX)=a(gX)=(ag)X\). It needs no invertibility assumption on \(a\).
`AmbientDifferentialLaws K n` is the conjunction of these two universally
quantified statements.

These are derived implementation statements. They isolate the local
second-derivative and chain-rule calculations needed for the differential
action in Borel–Jacquet, *Automorphic forms and automorphic representations*,
section 1.1, printed page 189 (one-based PDF page 184), and the archimedean
real group in section 4.1, printed page 194 (PDF page 189). The precise formulas
are not quoted assertions of that survey. The source is registered as
`borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The intended proof uses Mathlib's vector-field commutator identity and ordinary
Fréchet calculus for the continuous linear multiplication maps.

This file defines propositions only. It neither proves them nor constructs the
group differential. Transport from units charts to the actual published smooth
function space, smoothness preservation, the complexified Lie action and the
enveloping-algebra action remain separate obligations.
