# Complex scalars and actions under inertia-block center evaluation

Worker 1153. This internal construction implements the categorical action step
in the Proposition of Renard VI.4.5, printed p.160 / PDF p.166, registered
source `renard-2026-representations-groupes-reductifs-padiques` dated 9 July
2026. It is used with the group-algebra center parametrization of VI.4.4,
printed p.159 / PDF p.165, and retains that input explicitly.

Let X be an object of the actual rational inertia block such that the actual
preadditive Hom functor of X is full and faithful. For any monoid Γ and any
complex algebra isomorphism a from ℂ[Γ] to the complex algebra center of the
ambient End X.obj, `rationalInertiaBlockCenterFromEnd` composes a with the
inverse of the evaluation isomorphism. Its value at X is a, by the inverse
identity. Naturality identifies its action on Hom(X,Y) with precomposition
by a(f). Faithfulness of Hom(X,−) then detects equality of morphisms: if a(f)
acts by c on every map X → Y, the corresponding natural transformation acts
on Y by c times its identity.

The scalar clause follows because a is an isomorphism of complex algebras.
The coefficient element single(1,c) maps to c times the identity of X;
composition with any map X → Y is c times that map. Faithfulness gives the
scalar identity on every Y. The proof uses no essential surjectivity,
irreducibility, admissibility, or finiteness assumption, and preserves the
original field and carrier universes with an independent universe for Γ.

This module constructs and checks transport of an already given algebra
isomorphism. It makes no unconditional assertion that such an a or a fully
faithful Hom object exists in the representation-theoretic block. The exact
VI.4.5 evaluation proposition still needs the existing VI.3.2, VI.4.1 and
VI.4.4 representation-theoretic inputs.
