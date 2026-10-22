# Operator laws for the genuine smooth archimedean differential

Let K be any number field and n any natural number, including zero. The domain
is the published `RealLieAlgebra K n`, the actual real matrix Lie algebra with
bracket XY − YX. The operators act on the published `SmoothFunctions K n`,
whose functions are complex-valued and smooth over the reals on the actual
archimedean general linear group in completion coordinates.

Write D_X for the constructed `smoothDifferential K n X`. This is the actual
real derivative in the left-invariant matrix direction gX in mixed coordinates.
The imported `smoothDifferential_eq_mfderiv` identifies it with the manifold
derivative, and `smoothDifferential_apply` gives its coordinate evaluation.
The operator is complex-linear in the function and real-linear in X.

`SmoothDifferentialCommutator K n` asserts the endomorphism equality

D_[X,Y] = D_X ∘ D_Y − D_Y ∘ D_X

for every pair X,Y. The positive sign is consistent with the published right
translation R(h)f(g) = f(gh). Composition is the actual composition of
complex-linear endomorphisms of the smooth-function space.

Let T_a denote `smoothLeftTranslation K n a`, namely (T_a f)(x) = f(ax).
`SmoothDifferentialLeftTranslation K n` asserts D_X ∘ T_a = T_a ∘ D_X for
every X and every element a of the completion-coordinate group. Thus the
constructed differentiation preserves any left-translation invariance
condition. No abstract operator action or commutator law is supplied as a
hypothesis. `SmoothDifferentialLaws K n` is the conjunction of these two
universal propositions. This file states the laws; their proofs are separate.

These are derived implementation obligations for the differential action in
Borel–Jacquet, *Automorphic forms and automorphic representations*, sections
1.1 and 1.3, printed pages 189–190 (one-based PDF pages 184–185), and section
4.1, printed page 194 (PDF page 189). The registered source is
`borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The original supplies the real Lie-group, enveloping-algebra, and smooth
complex-valued function framework. The precise bundled equalities here are
derived from the published ambient derivative identities using the open units
chart and extension independence, rather than quoted from that source.
