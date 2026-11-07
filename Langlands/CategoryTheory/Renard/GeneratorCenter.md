# Evaluation of a categorical center at a generator

Worker 1153. This internal categorical lemma supplies the evaluation argument
used in Renard VI.4.5 (printed p.160 / PDF p.166) and the module example in A.X
(printed p.269 / PDF p.275), from the registered 9 July 2026 edition
`renard-2026-representations-groupes-reductifs-padiques`.

For any preadditive category with independent object and morphism universes,
evaluation at an object P defines a ring homomorphism from Mathlib's CatCenter
to the center of End P. Naturality at endomorphisms gives centrality. If the
actual preadditive Hom functor of P is faithful, evaluation is injective:
naturality determines every component after composition with every map from P,
and faithfulness detects equality. If this Hom functor is also full, a central
endomorphism c acts on Hom(P,X) by precomposition. Centrality makes this action
linear over the opposite endomorphism ring. Fullness lifts that action to X;
faithfulness checks naturality. Evaluation on the identity of P recovers c.
`generatorCenterEquiv` packages these facts as a ring isomorphism whose forward
map is exactly evaluation.

This proof uses neither essential surjectivity of the Hom functor nor an
abelian structure, and makes no claim about existence of a representation
theoretic progenerator. It preserves arbitrary object and morphism universes.
